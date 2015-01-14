#include "CodeGen_PTX_Dev.h"
#include "CodeGen_Internal.h"
#include "IROperator.h"
#include "IRPrinter.h"
#include "Debug.h"
#include "Target.h"
#include "LLVM_Headers.h"

// This is declared in NVPTX.h, which is not exported. Ugly, but seems better than
// hardcoding a path to the .h file.
#ifdef WITH_PTX
#include "nvvm.h" // TODO: separate WITH_NVVM sub-def?
namespace llvm { ModulePass *createNVVMReflectPass(const StringMap<int>& Mapping); }
#endif

namespace Halide {
namespace Internal {

using std::vector;
using std::string;

using namespace llvm;

CodeGen_PTX_Dev::CodeGen_PTX_Dev(Target host) : CodeGen(host) {
    #if !(WITH_PTX)
    user_error << "ptx not enabled for this build of Halide.\n";
    #endif
    user_assert(llvm_NVPTX_enabled) << "llvm build not configured with nvptx target enabled\n.";
}

void CodeGen_PTX_Dev::add_kernel(Stmt stmt,
                                 const std::string &name,
                                 const std::vector<GPU_Argument> &args) {

    debug(2) << "In CodeGen_PTX_Dev::add_kernel\n";

    // Now deduce the types of the arguments to our function
    vector<llvm::Type *> arg_types(args.size());
    for (size_t i = 0; i < args.size(); i++) {
        if (args[i].is_buffer) {
            arg_types[i] = llvm_type_of(UInt(8))->getPointerTo();
        } else {
            arg_types[i] = llvm_type_of(args[i].type);
        }
    }

    // Make our function
    function_name = name;
    FunctionType *func_t = FunctionType::get(void_t, arg_types, false);
    function = llvm::Function::Create(func_t, llvm::Function::ExternalLinkage, name, module);

    // Mark the buffer args as no alias
    for (size_t i = 0; i < args.size(); i++) {
        if (args[i].is_buffer) {
            function->setDoesNotAlias(i+1);
        }
    }


    // Make the initial basic block
    entry_block = BasicBlock::Create(*context, "entry", function);
    builder->SetInsertPoint(entry_block);

    // Put the arguments in the symbol table
    vector<string> arg_sym_names;
    {
        size_t i = 0;
        for (llvm::Function::arg_iterator iter = function->arg_begin();
             iter != function->arg_end();
             iter++) {

            string arg_sym_name = args[i].name;
            if (args[i].is_buffer) {
                // HACK: codegen expects a load from foo to use base
                // address 'foo.host', so we store the device pointer
                // as foo.host in this scope.
                arg_sym_name += ".host";
            }
            sym_push(arg_sym_name, iter);
            iter->setName(arg_sym_name);
            arg_sym_names.push_back(arg_sym_name);

            i++;
        }
    }

    // We won't end the entry block yet, because we'll want to add
    // some allocas to it later if there are local allocations. Start
    // a new block to put all the code.
    BasicBlock *body_block = BasicBlock::Create(*context, "body", function);
    builder->SetInsertPoint(body_block);

    debug(1) << "Generating llvm bitcode for kernel...\n";
    // Ok, we have a module, function, context, and a builder
    // pointing at a brand new basic block. We're good to go.
    stmt.accept(this);

    // Now we need to end the function
    builder->CreateRetVoid();

    // Make the entry block point to the body block
    builder->SetInsertPoint(entry_block);
    builder->CreateBr(body_block);

    // Add the nvvm annotation that it is a kernel function.
    MDNode *mdNode = MDNode::get(*context, vec<LLVMMDNodeArgumentType>(value_as_metadata_type(function),
                                                                       MDString::get(*context, "kernel"),
                                                                       value_as_metadata_type(ConstantInt::get(i32, 1))));

    module->getOrInsertNamedMetadata("nvvm.annotations")->addOperand(mdNode);


    // Now verify the function is ok
    verifyFunction(*function);

    // Finally, verify the module is ok
    verifyModule(*module);

    debug(2) << "Done generating llvm bitcode for PTX\n";

    // Clear the symbol table
    for (size_t i = 0; i < arg_sym_names.size(); i++) {
        sym_pop(arg_sym_names[i]);
    }
}

void CodeGen_PTX_Dev::init_module() {

    CodeGen::init_module();

    #ifdef WITH_PTX
    module = get_initial_module_for_ptx_device(target, context);
    #endif

    owns_module = true;
}

string CodeGen_PTX_Dev::simt_intrinsic(const string &name) {
    if (ends_with(name, ".__thread_id_x")) {
        return "llvm.nvvm.read.ptx.sreg.tid.x";
    } else if (ends_with(name, ".__thread_id_y")) {
        return "llvm.nvvm.read.ptx.sreg.tid.y";
    } else if (ends_with(name, ".__thread_id_z")) {
        return "llvm.nvvm.read.ptx.sreg.tid.z";
    } else if (ends_with(name, ".__thread_id_w")) {
        return "llvm.nvvm.read.ptx.sreg.tid.w";
    } else if (ends_with(name, ".__block_id_x")) {
        return "llvm.nvvm.read.ptx.sreg.ctaid.x";
    } else if (ends_with(name, ".__block_id_y")) {
        return "llvm.nvvm.read.ptx.sreg.ctaid.y";
    } else if (ends_with(name, ".__block_id_z")) {
        return "llvm.nvvm.read.ptx.sreg.ctaid.z";
    } else if (ends_with(name, ".__block_id_w")) {
        return "llvm.nvvm.read.ptx.sreg.ctaid.w";
    }
    internal_error << "simt_intrinsic called on bad variable name\n";
    return "";
}

void CodeGen_PTX_Dev::visit(const For *loop) {
    if (is_gpu_var(loop->name)) {
        Expr simt_idx = Call::make(Int(32), simt_intrinsic(loop->name), std::vector<Expr>(), Call::Extern);
        internal_assert(is_zero(loop->min));
        sym_push(loop->name, codegen(simt_idx));
        codegen(loop->body);
        sym_pop(loop->name);
    } else {
        CodeGen::visit(loop);
    }
}

void CodeGen_PTX_Dev::visit(const Allocate *alloc) {

    if (alloc->name == "__shared") {
        // PTX uses zero in address space 3 as the base address for shared memory
        Value *shared_base = Constant::getNullValue(PointerType::get(i8, 3));
        sym_push(alloc->name + ".host", shared_base);
    } else {

        debug(2) << "Allocate " << alloc->name << " on device\n";

        string allocation_name = alloc->name + ".host";
        debug(3) << "Pushing allocation called " << allocation_name << " onto the symbol table\n";

        // Jump back to the entry and generate an alloca. Note that by
        // jumping back we're rendering any expression we carry back
        // meaningless, so we had better only be dealing with
        // constants here.
        int32_t size = 0;
        bool is_constant = constant_allocation_size(alloc->extents, allocation_name, size);
        user_assert(is_constant)
            << "Allocation " << alloc->name << " has a dynamic size. "
            << "Only fixed-size allocations are supported on the gpu. "
            << "Try storing into shared memory instead.";

        BasicBlock *here = builder->GetInsertBlock();

        builder->SetInsertPoint(entry_block);
        Value *ptr = builder->CreateAlloca(llvm_type_of(alloc->type), ConstantInt::get(i32, size));
        builder->SetInsertPoint(here);
        sym_push(allocation_name, ptr);
    }
    codegen(alloc->body);
}

void CodeGen_PTX_Dev::visit(const Free *f) {
    sym_pop(f->name + ".host");
}

string CodeGen_PTX_Dev::march() const {
    return "nvptx64";
}

string CodeGen_PTX_Dev::mcpu() const {
    if (target.has_feature(Target::CUDACapability50)) {
        return "sm_50";
    } else if (target.has_feature(Target::CUDACapability35)) {
        return "sm_35";
    } else if (target.has_feature(Target::CUDACapability32)) {
        return "sm_32";
    } else if (target.has_feature(Target::CUDACapability30)) {
        return "sm_30";
    } else {
        return "sm_20";
    }
}

string CodeGen_PTX_Dev::mattrs() const {
    if (target.features_any_of(vec(Target::CUDACapability32,
                                   Target::CUDACapability50))) {
        // Need ptx isa 4.0. llvm < 3.5 doesn't support it.
        #if LLVM_VERSION < 35
        user_error << "This version of Halide was linked against llvm 3.4 or earlier, "
                   << "which does not support cuda compute capability 3.2 or 5.0\n";
        return "";
        #else
        return "+ptx40";
        #endif
    } else {
        // Use the default. For llvm 3.5 it's ptx 3.2.
        return "";
    }

}

bool CodeGen_PTX_Dev::use_soft_float_abi() const {
    return false;
}

static void checkNVVMCall(nvvmResult res) {
  assert(res == NVVM_SUCCESS && "libnvvm call failed");
}

vector<char> CodeGen_PTX_Dev::compile_to_src() {

    #ifdef WITH_PTX

    debug(2) << "In CodeGen_PTX_Dev::compile_to_src";

    // DISABLED - hooked in here to force PrintBeforeAll option - seems to be the only way?
    /*char* argv[] = { "llc", "-print-before-all" };*/
    /*int argc = sizeof(argv)/sizeof(char*);*/
    /*cl::ParseCommandLineOptions(argc, argv, "Halide PTX internal compiler\n");*/

    // Generic llvm optimizations on the module.
    // optimize_module();

    // Set up TargetTriple
    module->setTargetTriple(Triple::normalize(march()+"-nvidia-cuda"));
    
    // nvptx64 datalayout
    module->setDataLayout("e-p:64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-"
                          "i64:64:64-f32:32:32-f64:64:64-v16:16:16-v32:32:32-"
                          "v64:64:64-v128:128:128-n16:32:64");
    
    nvvmProgram compileUnit;
    nvvmResult res;
    
    // Export IR to string
    std::string moduleStr;
    llvm::raw_string_ostream str(moduleStr);
    // str << *module;
    llvm::WriteBitcodeToFile(module, str);
    str.flush();
    
    std::string err;
    llvm::raw_fd_ostream moduleOut("/tmp/halide.ll", err);
    moduleOut << *module;
    moduleOut.close();
    
    // debug(0) << "Compiling PTX:\n" << moduleStr << "\n";
    
    // NVVM Initialization
    checkNVVMCall(nvvmCreateProgram(&compileUnit));
    // Create NVVM compilation unit from LLVM IR
    checkNVVMCall(nvvmAddModuleToProgram(compileUnit,
                                         moduleStr.c_str(), moduleStr.size(),
                                         module->getModuleIdentifier().c_str()));
    
    std::string archVer = mcpu();
    std::string archArg = "-arch=compute_" + std::string(archVer.c_str()+3);
    debug(0) << "Arch: " << archArg << "\n";
    
    const char *options[] = { archArg.c_str() };
    
    // Compile LLVM IR into PTX
    res = nvvmCompileProgram(compileUnit, 1, options);
    if (res != NVVM_SUCCESS) {
      std::cerr << "nvvmCompileProgram failed!" << std::endl;
      size_t logSize;
      nvvmGetProgramLogSize(compileUnit, &logSize);
      char *msg = new char[logSize];
      nvvmGetProgramLog(compileUnit, msg);
      std::cerr << msg << std::endl;
      delete [] msg;
      internal_error << "nvvmCompileProgram failed";
    }

    size_t ptxSize;
    checkNVVMCall(nvvmGetCompiledResultSize(compileUnit, &ptxSize));
    vector<char> buffer;
    buffer.resize(ptxSize);
    checkNVVMCall(nvvmGetCompiledResult(compileUnit, &buffer[0]));
    checkNVVMCall(nvvmDestroyProgram(&compileUnit));

    debug(1) << "PTX kernel:\n" << &buffer[0] << "\n";
    // vector<char> buffer(str.begin(), str.end());
    // buffer.push_back(0);
    return buffer;
#else // WITH_PTX
    return vector<char>();
#endif
}

int CodeGen_PTX_Dev::native_vector_bits() const {
    // PTX doesn't really do vectorization. The widest type is a double.
    return 64;
}

string CodeGen_PTX_Dev::get_current_kernel_name() {
    return function->getName();
}

void CodeGen_PTX_Dev::dump() {
    module->dump();
}
    
std::string CodeGen_PTX_Dev::print_gpu_name(const std::string &name) {
    return name;
}

}}
