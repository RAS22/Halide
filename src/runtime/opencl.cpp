#include "runtime_internal.h"
#include "scoped_spin_lock.h"
#include "../buffer_t.h"
#include "HalideRuntime.h"

#include "mini_cl.h"

#include "cuda_opencl_shared.h"

namespace Halide { namespace Runtime { namespace Internal {

WEAK const char *get_opencl_error_name(cl_int err);
WEAK int create_opencl_context(void *user_context, cl_context *ctx, cl_command_queue *q);

// An OpenCL context/queue/synchronization lock defined in
// this module with weak linkage
cl_context WEAK weak_cl_ctx = 0;
cl_command_queue WEAK weak_cl_q = 0;
volatile int WEAK weak_cl_lock = 0;

// In the non-JIT case, the context is stored in the weak globals above.
// JIT modules will call halide_set_cl_context, changing the pointers below.
cl_context WEAK *cl_ctx_ptr = NULL;
cl_command_queue WEAK *cl_q_ptr = NULL;
volatile int WEAK *cl_lock_ptr = NULL;

}}} // namespace Halide::Runtime::Internal

// Allow OpenCL 1.1 features to be used.
#define ENABLE_OPENCL_11

extern "C" {

extern int64_t halide_current_time_ns(void *user_context);
extern void free(void *);
extern void *malloc(size_t);
extern const char * strstr(const char *, const char *);
extern int atoi(const char *);

WEAK void halide_set_cl_context(cl_context* ctx_ptr, cl_command_queue* q_ptr, volatile int* lock_ptr) {
    cl_ctx_ptr = ctx_ptr;
    cl_q_ptr = q_ptr;
    cl_lock_ptr = lock_ptr;
}

// The default implementation of halide_acquire_cl_context uses the global
// pointers above, and serializes access with a spin lock.
// Overriding implementations of acquire/release must implement the following
// behavior:
// - halide_acquire_cl_context should always store a valid context/command
//   queue in ctx/q, or return an error code.
// - A call to halide_acquire_cl_context is followed by a matching call to
//   halide_release_cl_context. halide_acquire_cl_context should block while a
//   previous call (if any) has not yet been released via halide_release_cl_context.
WEAK int halide_acquire_cl_context(void *user_context, cl_context *ctx, cl_command_queue *q) {
    // TODO: Should we use a more "assertive" assert? These asserts do
    // not block execution on failure.
    halide_assert(user_context, ctx != NULL);
    halide_assert(user_context, q != NULL);

    // If the context pointers aren't hooked up, use our weak globals.
    if (cl_ctx_ptr == NULL) {
        cl_ctx_ptr = &weak_cl_ctx;
        cl_q_ptr = &weak_cl_q;
        cl_lock_ptr = &weak_cl_lock;
    }

    halide_assert(user_context, cl_lock_ptr != NULL);
    while (__sync_lock_test_and_set(cl_lock_ptr, 1)) { }

    // If the context has not been initialized, initialize it now.
    halide_assert(user_context, cl_ctx_ptr != NULL);
    halide_assert(user_context, cl_q_ptr != NULL);
    if (!(*cl_ctx_ptr)) {
        cl_int error = create_opencl_context(user_context, cl_ctx_ptr, cl_q_ptr);
        if (error != CL_SUCCESS) {
            __sync_lock_release(cl_lock_ptr);
            return error;
        }
    }

    *ctx = *cl_ctx_ptr;
    *q = *cl_q_ptr;
    return 0;
}

WEAK int halide_release_cl_context(void *user_context) {
    __sync_lock_release(cl_lock_ptr);
    return 0;
}

} // extern "C"

namespace Halide { namespace Runtime { namespace Internal {

// Helper object to acquire and release the OpenCL context.
class ClContext {
    void *user_context;

public:
    cl_context context;
    cl_command_queue cmd_queue;
    cl_int error;

    // Constructor sets 'error' if any occurs.
    ClContext(void *user_context) : user_context(user_context),
                                    context(NULL),
                                    cmd_queue(NULL),
                                    error(CL_SUCCESS) {
        error = halide_acquire_cl_context(user_context, &context, &cmd_queue);
        halide_assert(user_context, context != NULL && cmd_queue != NULL);
    }

    ~ClContext() {
        halide_release_cl_context(user_context);
    }
};

// Structure to hold the state of a module attached to the context.
// Also used as a linked-list to keep track of all the different
// modules that are attached to a context in order to release them all
// when then context is released.
struct module_state {
    cl_program program;
    module_state *next;
};
WEAK module_state *state_list = NULL;

WEAK bool validate_dev_pointer(void *user_context, buffer_t* buf, size_t size=0) {
    if (buf->dev == 0) {
        return true;
    }

    size_t real_size;
    cl_int result = clGetMemObjectInfo((cl_mem)buf->dev, CL_MEM_SIZE, sizeof(size_t), &real_size, NULL);
    if (result != CL_SUCCESS) {
        error(user_context) << "CL: Bad device pointer " << (void *)buf->dev
                            << ": clGetMemObjectInfo returned "
                            << get_opencl_error_name(result);
        return false;
    }

    debug(user_context) << "CL: validate " << (void *)buf->dev
                        << ": asked for " << size
                        << ", actual allocated " << real_size << "\n";

    if (size) {
        halide_assert(user_context, real_size >= size && "Validating pointer with insufficient size");
    }
    return true;
}

// Initializes the context used by the default implementation
// of halide_acquire_context.
WEAK int create_opencl_context(void *user_context, cl_context *ctx, cl_command_queue *q) {
    debug(user_context)
        << "    create_opencl_context (user_context: " << user_context << ")\n";

    halide_assert(user_context, ctx != NULL && *ctx == NULL);
    halide_assert(user_context, q != NULL && *q == NULL);

    cl_int err = 0;

    const cl_uint max_platforms = 4;
    cl_platform_id platforms[max_platforms];
    cl_uint platform_count = 0;

    err = clGetPlatformIDs(max_platforms, platforms, &platform_count);
    if (err != CL_SUCCESS) {
        error(user_context) << "CL: clGetPlatformIDs failed: "
                            << get_opencl_error_name(err);
        return err;
    }

    cl_platform_id platform = NULL;

    // Find the requested platform, or the first if none specified.
    const char *name = halide_get_ocl_platform_name(user_context);
    if (name != NULL) {
        for (cl_uint i = 0; i < platform_count; ++i) {
            const cl_uint max_platform_name = 256;
            char platform_name[max_platform_name];
            err = clGetPlatformInfo(platforms[i], CL_PLATFORM_NAME, max_platform_name, platform_name, NULL );
            if (err != CL_SUCCESS) continue;

            // A platform matches the request if it is a substring of the platform name.
            if (strstr(platform_name, name)) {
                platform = platforms[i];
                break;
            }
        }
    } else if (platform_count > 0) {
        platform = platforms[0];
    }
    if (platform == NULL){
        error(user_context) << "CL: Failed to find platform\n";
        return CL_INVALID_PLATFORM;
    }

    #ifdef DEBUG_RUNTIME
    const cl_uint max_platform_name = 256;
    char platform_name[max_platform_name];
    err = clGetPlatformInfo(platform, CL_PLATFORM_NAME, max_platform_name, platform_name, NULL );
    if (err != CL_SUCCESS) {
        debug(user_context) << "    clGetPlatformInfo(CL_PLATFORM_NAME) failed: "
                            << get_opencl_error_name(err) << "\n";
        // This is just debug info, report the error but don't fail context creation due to it.
        //return err;
    } else {
        debug(user_context) << "    Got platform '" << platform_name
                            << "', about to create context (t="
                            << halide_current_time_ns(user_context)
                            << ")\n";
    }
    #endif

    // Get the types of devices requested.
    cl_device_type device_type = 0;
    const char * dev_type = halide_get_ocl_device_type(user_context);
    if (dev_type != NULL) {
        if (strstr("cpu", dev_type)) {
            device_type |= CL_DEVICE_TYPE_CPU;
        }
        if (strstr("gpu", dev_type)) {
            device_type |= CL_DEVICE_TYPE_GPU;
        }
        if (strstr("acc", dev_type)) {
            device_type |= CL_DEVICE_TYPE_ACCELERATOR;
        }
    }
    // If no device types are specified, use all the available
    // devices.
    if (device_type == 0) {
        device_type = CL_DEVICE_TYPE_ALL;
    }

    // Get all the devices of the specified type.
    const cl_uint maxDevices = 4;
    cl_device_id devices[maxDevices];
    cl_uint deviceCount = 0;
    err = clGetDeviceIDs(platform, device_type, maxDevices, devices, &deviceCount );
    if (err != CL_SUCCESS) {
        error(user_context) << "CL: clGetDeviceIDs failed: "
                            << get_opencl_error_name(err);
        return err;
    }

    // If the user indicated a specific device index to use, use
    // that. Note that this is an index within the set of devices
    // specified by the device type. -1 means the last device.
    int device = halide_get_gpu_device(user_context);
    if (device == -1) {
        device = deviceCount - 1;
    }

    if (device < 0 || device >= deviceCount) {
        error(user_context) << "CL: Failed to get device: " << device;
        return CL_DEVICE_NOT_FOUND;
    }

    cl_device_id dev = devices[device];

    #ifdef DEBUG_RUNTIME
    // Declare variables for other state we want to query.
    char device_name[256] = "";
    char device_vendor[256] = "";
    char device_profile[256] = "";
    char device_version[256] = "";
    char driver_version[256] = "";
    cl_ulong global_mem_size = 0;
    cl_ulong max_mem_alloc_size = 0;
    cl_ulong local_mem_size = 0;
    cl_uint max_compute_units = 0;
    size_t max_work_group_size = 0;
    cl_uint max_work_item_dimensions = 0;
    size_t max_work_item_sizes[4] = { 0, };


    struct {void *dst; size_t sz; cl_device_info param;} infos[] = {
        {&device_name[0], sizeof(device_name), CL_DEVICE_NAME},
        {&device_vendor[0], sizeof(device_vendor), CL_DEVICE_VENDOR},
        {&device_profile[0], sizeof(device_profile), CL_DEVICE_PROFILE},
        {&device_version[0], sizeof(device_version), CL_DEVICE_VERSION},
        {&driver_version[0], sizeof(driver_version), CL_DRIVER_VERSION},
        {&global_mem_size, sizeof(global_mem_size), CL_DEVICE_GLOBAL_MEM_SIZE},
        {&max_mem_alloc_size, sizeof(max_mem_alloc_size), CL_DEVICE_MAX_MEM_ALLOC_SIZE},
        {&local_mem_size, sizeof(local_mem_size), CL_DEVICE_LOCAL_MEM_SIZE},
        {&max_compute_units, sizeof(max_compute_units), CL_DEVICE_MAX_COMPUTE_UNITS},
        {&max_work_group_size, sizeof(max_work_group_size), CL_DEVICE_MAX_WORK_GROUP_SIZE},
        {&max_work_item_dimensions, sizeof(max_work_item_dimensions), CL_DEVICE_MAX_WORK_ITEM_DIMENSIONS},
        {&max_work_item_sizes[0], sizeof(max_work_item_sizes), CL_DEVICE_MAX_WORK_ITEM_SIZES},
        {NULL}};

    // Do all the queries.
    for (int i = 0; infos[i].dst; i++) {
        err = clGetDeviceInfo(dev, infos[i].param, infos[i].sz, infos[i].dst, NULL);
        if (err != CL_SUCCESS) {
            error(user_context) << "CL: clGetDeviceInfo failed: "
                                << get_opencl_error_name(err);
            return err;
        }
    }

    debug(user_context)
        << "      device name: " << device_name << "\n"
        << "      device vendor: " << device_vendor << "\n"
        << "      device profile: " << device_profile << "\n"
        << "      global mem size: " << global_mem_size/(1024*1024) << " MB\n"
        << "      max mem alloc size: " << max_mem_alloc_size/(1024*1024) << " MB\n"
        << "      local mem size: " << local_mem_size << "\n"
        << "      max compute units: " << max_compute_units << "\n"
        << "      max workgroup size: " << max_work_group_size << "\n"
        << "      max work item dimensions: " << max_work_item_dimensions << "\n"
        << "      max work item sizes: " << max_work_item_sizes[0]
        << "x" << max_work_item_sizes[1]
        << "x" << max_work_item_sizes[2]
        << "x" << max_work_item_sizes[3] << "\n";
    #endif


    // Create context and command queue.
    cl_context_properties properties[] = { CL_CONTEXT_PLATFORM, (cl_context_properties)platform, 0 };
    debug(user_context) << "    clCreateContext -> ";
    *ctx = clCreateContext(properties, 1, &dev, NULL, NULL, &err);
    if (err != CL_SUCCESS) {
        debug(user_context) << get_opencl_error_name(err);
        error(user_context) << "CL: clCreateContext failed: "
                            << get_opencl_error_name(err);
        return err;
    } else {
        debug(user_context) << *ctx << "\n";
    }

    debug(user_context) << "    clCreateCommandQueue ";
    *q = clCreateCommandQueue(*ctx, dev, 0, &err);
    if (err != CL_SUCCESS) {
        debug(user_context) << get_opencl_error_name(err);
        error(user_context) << "CL: clCreateCommandQueue failed: "
                            << get_opencl_error_name(err);
        return err;
    } else {
        debug(user_context) << *q << "\n";
    }

    return err;
}

}}} // namespace Halide::Runtime::Internal

extern "C" {

WEAK int halide_dev_free(void *user_context, buffer_t* buf) {

    // halide_dev_free, at present, can be exposed to clients and they
    // should be allowed to call halide_dev_free on any buffer_t
    // including ones that have never been used with a GPU.
    if (buf->dev == 0) {
      return 0;
    }

    debug(user_context)
        << "CL: halide_dev_free (user_context: " << user_context
        << ", buf: " << buf << ")\n";

    ClContext ctx(user_context);
    if (ctx.error != CL_SUCCESS) {
        return ctx.error;
    }

    #ifdef DEBUG_RUNTIME
    uint64_t t_before = halide_current_time_ns(user_context);
    #endif

    halide_assert(user_context, validate_dev_pointer(user_context, buf));
    debug(user_context) << "    clReleaseMemObject " << (void *)buf->dev << "\n";
    cl_int result = clReleaseMemObject((cl_mem)buf->dev);
    // If clReleaseMemObject fails, it is unlikely to succeed in a later call, so
    // we just end our reference to it regardless.
    buf->dev = 0;
    if (result != CL_SUCCESS) {
        error(user_context) << "CL: clReleaseMemObject failed: "
                            << get_opencl_error_name(result);
        return result;
    }

    #ifdef DEBUG_RUNTIME
    uint64_t t_after = halide_current_time_ns(user_context);
    debug(user_context) << "    Time: " << (t_after - t_before) / 1.0e6 << " ms\n";
    #endif

    return 0;
}


WEAK int halide_init_kernels(void *user_context, void **state_ptr, const char* src, int size) {
    debug(user_context)
        << "CL: halide_init_kernels (user_context: " << user_context
        << ", state_ptr: " << state_ptr
        << ", program: " << (void *)src
        << ", size: " << size << "\n";

    ClContext ctx(user_context);
    if (ctx.error != CL_SUCCESS) {
        return ctx.error;
    }

    #ifdef DEBUG_RUNTIME
    uint64_t t_before = halide_current_time_ns(user_context);
    #endif

    // Create the state object if necessary. This only happens once, regardless
    // of how many times halide_init_kernels/halide_release is called.
    // halide_release traverses this list and releases the program objects, but
    // it does not modify the list nodes created/inserted here.
    module_state **state = (module_state**)state_ptr;
    if (!(*state)) {
        *state = (module_state*)malloc(sizeof(module_state));
        (*state)->program = NULL;
        (*state)->next = state_list;
        state_list = *state;
    }

    // Create the program if necessary. TODO: The program object needs to not
    // only already exist, but be created for the same context/device as the
    // calling context/device.
    if (!(*state && (*state)->program) && size > 1) {
        cl_int err = 0;
        cl_device_id dev;

        err = clGetContextInfo(ctx.context, CL_CONTEXT_DEVICES, sizeof(dev), &dev, NULL);
        if (err != CL_SUCCESS) {
            error(user_context) << "CL: clGetContextInfo(CL_CONTEXT_DEVICES) failed: "
                                << get_opencl_error_name(err);
            return err;
        }

        cl_device_id devices[] = { dev };

        // Get the max constant buffer size supported by this OpenCL implementation.
        cl_ulong max_constant_buffer_size = 0;
        err = clGetDeviceInfo(dev, CL_DEVICE_MAX_CONSTANT_BUFFER_SIZE, sizeof(max_constant_buffer_size), &max_constant_buffer_size, NULL);
        if (err != CL_SUCCESS) {
            error(user_context) << "CL: clGetDeviceInfo (CL_DEVICE_MAX_CONSTANT_BUFFER_SIZE) failed: "
                                << get_opencl_error_name(err);
            return err;
        }
        // Get the max number of constant arguments supported by this OpenCL implementation.
        cl_uint max_constant_args = 0;
        err = clGetDeviceInfo(dev, CL_DEVICE_MAX_CONSTANT_ARGS, sizeof(max_constant_args), &max_constant_args, NULL);
        if (err != CL_SUCCESS) {
            error(user_context) << "CL: clGetDeviceInfo (CL_DEVICE_MAX_CONSTANT_ARGS) failed: "
                                << get_opencl_error_name(err);
            return err;
        }

        // Build the compile argument options.
        stringstream options(user_context);
        options << "-D MAX_CONSTANT_BUFFER_SIZE=" << max_constant_buffer_size
                << " -D MAX_CONSTANT_ARGS=" << max_constant_args;

        const char * sources[] = { src };
        debug(user_context) << "    clCreateProgramWithSource -> ";
        cl_program program = clCreateProgramWithSource(ctx.context, 1, &sources[0], NULL, &err );
        if (err != CL_SUCCESS) {
            debug(user_context) << get_opencl_error_name(err) << "\n";
            error(user_context) << "CL: clCreateProgramWithSource failed: "
                                << get_opencl_error_name(err);
            return err;
        } else {
            debug(user_context) << (void *)program << "\n";
        }
        (*state)->program = program;

        debug(user_context) << "    clBuildProgram " << (void *)program
                            << " " << options.str() << "\n";
        err = clBuildProgram(program, 1, devices, options.str(), NULL, NULL );
        if (err != CL_SUCCESS) {

            // Allocate an appropriately sized buffer for the build log.
            char buffer[8192];

            // Get build log
            if (clGetProgramBuildInfo(program, dev,
                                      CL_PROGRAM_BUILD_LOG,
                                      sizeof(buffer), buffer,
                                      NULL) == CL_SUCCESS) {
                error(user_context) << "CL: clBuildProgram failed: "
                                    << get_opencl_error_name(err)
                                    << "\nBuild Log:\n "
                                    << buffer;
            } else {
                error(user_context) << "clGetProgramBuildInfo failed";
            }

            return err;
        }
    }

    #ifdef DEBUG_RUNTIME
    uint64_t t_after = halide_current_time_ns(user_context);
    debug(user_context) << "    Time: " << (t_after - t_before) / 1.0e6 << " ms\n";
    #endif

    return 0;
}

// Used to generate correct timings when tracing
WEAK int halide_dev_sync(void *user_context) {
    debug(user_context) << "CL: halide_dev_sync (user_context: " << user_context << ")\n";

    ClContext ctx(user_context);
    halide_assert(user_context, ctx.error == CL_SUCCESS);

    #ifdef DEBUG_RUNTIME
    uint64_t t_before = halide_current_time_ns(user_context);
    #endif

    cl_int err = clFinish(ctx.cmd_queue);
    if (err != CL_SUCCESS) {
        error(user_context) << "CL: clFinish failed: "
                            << get_opencl_error_name(err);
        return err;
    }

    #ifdef DEBUG_RUNTIME
    uint64_t t_after = halide_current_time_ns(user_context);
    debug(user_context) << "    Time: " << (t_after - t_before) / 1.0e6 << " ms\n";
    #endif

    return CL_SUCCESS;
}

WEAK void halide_release(void *user_context) {
    debug(user_context)
        << "CL: halide_release (user_context: " << user_context << ")\n";

    // The ClContext object does not allow the context storage to be modified,
    // so we use halide_acquire_context directly.
    int err;
    cl_context ctx;
    cl_command_queue q;
    err = halide_acquire_cl_context(user_context, &ctx, &q);
    if (err != 0 || !ctx) {
        return;
    }

    err = clFinish(q);
    halide_assert(user_context, err == CL_SUCCESS);

    // Unload the modules attached to this context. Note that the list
    // nodes themselves are not freed, only the program objects are
    // released. Subsequent calls to halide_init_kernels might re-create
    // the program object using the same list node to store the program
    // object.
    module_state *state = state_list;
    while (state) {
        if (state->program) {
            debug(user_context) << "    clReleaseProgram " << state->program << "\n";
            err = clReleaseProgram(state->program);
            halide_assert(user_context, err == CL_SUCCESS);
            state->program = NULL;
        }
        state = state->next;
    }

    // Release the context itself, if we created it.
    if (ctx == weak_cl_ctx) {
        debug(user_context) << "    clReleaseCommandQueue " << weak_cl_q << "\n";
        err = clReleaseCommandQueue(weak_cl_q);
        halide_assert(user_context, err == CL_SUCCESS);
        weak_cl_q = NULL;

        debug(user_context) << "    clReleaseContext " << weak_cl_ctx << "\n";
        err = clReleaseContext(weak_cl_ctx);
        halide_assert(user_context, err == CL_SUCCESS);
        weak_cl_ctx = NULL;
    }

    halide_release_cl_context(user_context);
}

WEAK int halide_dev_malloc(void *user_context, buffer_t* buf) {
    debug(user_context)
        << "CL: halide_dev_malloc (user_context: " << user_context
        << ", buf: " << buf << ")\n";

    ClContext ctx(user_context);
    if (ctx.error != CL_SUCCESS) {
        return ctx.error;
    }

    size_t size = buf_size(user_context, buf);
    if (buf->dev) {
        halide_assert(user_context, validate_dev_pointer(user_context, buf, size));
        return 0;
    }

    halide_assert(user_context, buf->stride[0] >= 0 && buf->stride[1] >= 0 &&
                                buf->stride[2] >= 0 && buf->stride[3] >= 0);

    debug(user_context)
        << "    Allocating buffer of " << size << " bytes,"
        << " extents: " << buf->extent[0] << "x" << buf->extent[1] << "x" << buf->extent[2] << "x" << buf->extent[3]
        << " strides: " << buf->stride[0] << "x" << buf->stride[1] << "x" << buf->stride[2] << "x" << buf->stride[3]
        << " (" << buf->elem_size << " bytes per element)\n";

    #ifdef DEBUG_RUNTIME
    uint64_t t_before = halide_current_time_ns(user_context);
    #endif

    cl_int err;
    debug(user_context) << "    clCreateBuffer -> " << size << " ";
    buf->dev = (uint64_t)clCreateBuffer(ctx.context, CL_MEM_READ_WRITE, size, NULL, &err);
    if (err != CL_SUCCESS || buf->dev == 0) {
        debug(user_context) << get_opencl_error_name(err) << "\n";
        error(user_context) << "CL: clCreateBuffer failed: "
                            << get_opencl_error_name(err);
        return err;
    } else {
        debug(user_context) << (void *)buf->dev << "\n";
    }

    debug(user_context)
        << "    Allocated device buffer " << (void *)buf->dev
        << " for buffer " << buf << "\n";

    #ifdef DEBUG_RUNTIME
    uint64_t t_after = halide_current_time_ns(user_context);
    debug(user_context) << "    Time: " << (t_after - t_before) / 1.0e6 << " ms\n";
    #endif

    return CL_SUCCESS;
}

WEAK int halide_copy_to_dev(void *user_context, buffer_t* buf) {
    int err = halide_dev_malloc(user_context, buf);
    if (err) {
        return err;
    }

    debug(user_context)
        << "CL: halide_copy_to_dev (user_context: " << user_context
        << ", buf: " << buf << ")\n";

    // Acquire the context so we can use the command queue. This also avoids multiple
    // redundant calls to clEnqueueWriteBuffer when multiple threads are trying to copy
    // the same buffer.
    ClContext ctx(user_context);
    if (ctx.error != CL_SUCCESS) {
        return ctx.error;
    }

    if (buf->host_dirty) {
        #ifdef DEBUG_RUNTIME
        uint64_t t_before = halide_current_time_ns(user_context);
        #endif

        halide_assert(user_context, buf->host && buf->dev);
        halide_assert(user_context, validate_dev_pointer(user_context, buf));

        dev_copy c = make_host_to_dev_copy(buf);

        for (int w = 0; w < c.extent[3]; w++) {
            for (int z = 0; z < c.extent[2]; z++) {
#ifdef ENABLE_OPENCL_11
                // OpenCL 1.1 supports stride-aware memory transfers up to 3D, so we
                // can deal with the 2 innermost strides with OpenCL.
                uint64_t off = z * c.stride_bytes[2] + w * c.stride_bytes[3];

                size_t offset[3] = { off, 0, 0 };
                size_t region[3] = { c.chunk_size, c.extent[0], c.extent[1] };

                debug(user_context)
                    << "    clEnqueueWriteBufferRect ((" << z << ", " << w << "), "
                    << "(" << (void *)c.src << " -> " << c.dst << ") + " << off << ", "
                    << region[0] << "x" << region[1] << "x" << region[2] << " bytes, "
                    << c.stride_bytes[0] << "x" << c.stride_bytes[1] << ")\n";

                cl_int err = clEnqueueWriteBufferRect(ctx.cmd_queue, (cl_mem)c.dst, CL_FALSE,
                                                      offset, offset, region,
                                                      c.stride_bytes[0], c.stride_bytes[1],
                                                      c.stride_bytes[0], c.stride_bytes[1],
                                                      (void *)c.src,
                                                      0, NULL, NULL);

                if (err != CL_SUCCESS) {
                    error(user_context) << "CL: clEnqueueWriteBufferRect failed: "
                                        << get_opencl_error_name(err);
                    return err;
                }
#else
                for (int y = 0; y < c.extent[1]; y++) {
                    for (int x = 0; x < c.extent[0]; x++) {
                        uint64_t off = (x * c.stride_bytes[0] +
                                        y * c.stride_bytes[1] +
                                        z * c.stride_bytes[2] +
                                        w * c.stride_bytes[3]);
                        void *src = (void *)(c.src + off);
                        void *dst = (void *)(c.dst + off);
                        uint64_t size = c.chunk_size;

                        debug(user_context)
                            << "    clEnqueueWriteBuffer  ((" << x << ", " << y << ", " << z << ", " << w << "), "
                            << size << " bytes, " << src << " -> " << (void *)dst << ")\n";

                        cl_int err = clEnqueueWriteBuffer(ctx.cmd_queue, (cl_mem)c.dst,
                                                          CL_FALSE, off, size, src, 0, NULL, NULL);
                        if (err != CL_SUCCESS) {
                            error(user_context) << "CL: clEnqueueWriteBuffer failed: "
                                                << get_opencl_error_name(err);
                            return err;
                        }
                    }
                }
#endif
            }
        }
        // The writes above are all non-blocking, so empty the command
        // queue before we proceed so that other host code won't write
        // to the buffer while the above writes are still running.
        clFinish(ctx.cmd_queue);

        #ifdef DEBUG_RUNTIME
        uint64_t t_after = halide_current_time_ns(user_context);
        debug(user_context) << "    Time: " << (t_after - t_before) / 1.0e6 << " ms\n";
        #endif
    }
    buf->host_dirty = false;
    return 0;
}

WEAK int halide_copy_to_host(void *user_context, buffer_t* buf) {
    if (!buf->dev_dirty) {
        return 0;
    }

    debug(user_context)
        << "CL: halide_copy_to_host (user_context: " << user_context
        << ", buf: " << buf << ")\n";

    // Acquire the context so we can use the command queue. This also avoids multiple
    // redundant calls to clEnqueueReadBuffer when multiple threads are trying to copy
    // the same buffer.
    ClContext ctx(user_context);
    if (ctx.error != CL_SUCCESS) {
        return ctx.error;
    }

    // Need to check dev_dirty again, in case another thread did the
    // copy_to_host before the serialization point above.
    if (buf->dev_dirty) {
        #ifdef DEBUG_RUNTIME
        uint64_t t_before = halide_current_time_ns(user_context);
        #endif

        halide_assert(user_context, buf->host && buf->dev);
        halide_assert(user_context, validate_dev_pointer(user_context, buf));

        dev_copy c = make_dev_to_host_copy(buf);

        for (int w = 0; w < c.extent[3]; w++) {
            for (int z = 0; z < c.extent[2]; z++) {
#ifdef ENABLE_OPENCL_11
                // OpenCL 1.1 supports stride-aware memory transfers up to 3D, so we
                // can deal with the 2 innermost strides with OpenCL.
                uint64_t off = z * c.stride_bytes[2] + w * c.stride_bytes[3];

                size_t offset[3] = { off, 0, 0 };
                size_t region[3] = { c.chunk_size, c.extent[0], c.extent[1] };

                debug(user_context)
                    << "    clEnqueueReadBufferRect ((" << z << ", " << w << "), "
                    << "(" << (void *)c.src << " -> " << (void *)c.dst << ") + " << off << ", "
                    << region[0] << "x" << region[1] << "x" << region[2] << " bytes, "
                    << c.stride_bytes[0] << "x" << c.stride_bytes[1] << ")\n";

                cl_int err = clEnqueueReadBufferRect(ctx.cmd_queue, (cl_mem)c.src, CL_FALSE,
                                                     offset, offset, region,
                                                     c.stride_bytes[0], c.stride_bytes[1],
                                                     c.stride_bytes[0], c.stride_bytes[1],
                                                     (void *)c.dst,
                                                     0, NULL, NULL);

                if (err != CL_SUCCESS) {
                    error(user_context) << "CL: clEnqueueReadBufferRect failed: "
                                        << get_opencl_error_name(err);
                    return err;
                }
#else
                for (int y = 0; y < c.extent[1]; y++) {
                    for (int x = 0; x < c.extent[0]; x++) {
                        uint64_t off = (x * c.stride_bytes[0] +
                                        y * c.stride_bytes[1] +
                                        z * c.stride_bytes[2] +
                                        w * c.stride_bytes[3]);
                        void *src = (void *)(c.src + off);
                        void *dst = (void *)(c.dst + off);
                        uint64_t size = c.chunk_size;

                        debug(user_context)
                            << "    clEnqueueReadBuffer  ((" << x << ", " << y << ", " << z << ", " << w << "), "
                            << size << " bytes, " << src << " -> " << dst << ")\n";

                        cl_int err = clEnqueueReadBuffer(ctx.cmd_queue, (cl_mem)c.src,
                                                         CL_FALSE, off, size, dst, 0, NULL, NULL);
                        if (err != CL_SUCCESS) {
                            error(user_context) << "CL: clEnqueueReadBuffer failed: "
                                                << get_opencl_error_name(err);
                            return err;
                        }
                    }
                }
#endif
            }
        }
        // The writes above are all non-blocking, so empty the command
        // queue before we proceed so that other host code won't read
        // bad data.
        clFinish(ctx.cmd_queue);

        #ifdef DEBUG_RUNTIME
        uint64_t t_after = halide_current_time_ns(user_context);
        debug(user_context) << "    Time: " << (t_after - t_before) / 1.0e6 << " ms\n";
        #endif
    }
    buf->dev_dirty = false;
    return 0;
}

WEAK int halide_dev_run(void *user_context,
                        void *state_ptr,
                        const char* entry_name,
                        int blocksX, int blocksY, int blocksZ,
                        int threadsX, int threadsY, int threadsZ,
                        int shared_mem_bytes,
                        size_t arg_sizes[],
                        void* args[],
                        int num_attributes,
                        float* vertex_buffer,
                        int num_coords_dim0,
                        int num_coords_dim1) {

    debug(user_context)
        << "CL: halide_dev_run (user_context: " << user_context << ", "
        << "entry: " << entry_name << ", "
        << "blocks: " << blocksX << "x" << blocksY << "x" << blocksZ << ", "
        << "threads: " << threadsX << "x" << threadsY << "x" << threadsZ << ", "
        << "shmem: " << shared_mem_bytes << "\n";


    cl_int err;
    ClContext ctx(user_context);
    if (ctx.error != CL_SUCCESS) {
        return ctx.error;
    }

    #ifdef DEBUG_RUNTIME
    uint64_t t_before = halide_current_time_ns(user_context);
    #endif

    // Create kernel object for entry_name from the program for this module.
    halide_assert(user_context, state_ptr);
    cl_program program = ((module_state*)state_ptr)->program;

    halide_assert(user_context, program);
    debug(user_context) << "    clCreateKernel " << entry_name << " -> ";
    cl_kernel f = clCreateKernel(program, entry_name, &err);
    if (err != CL_SUCCESS) {
        debug(user_context) << get_opencl_error_name(err) << "\n";
        error(user_context) << "CL: clCreateKernel " << entry_name << " failed: "
                            << get_opencl_error_name(err) << "\n";
        return err;
    } else {
        #ifdef DEBUG_RUNTIME
        uint64_t t_create_kernel = halide_current_time_ns(user_context);
        debug(user_context) << "    Time: " << (t_create_kernel - t_before) / 1.0e6 << " ms\n";
        #endif
    }

    // Pack dims
    size_t global_dim[3] = {blocksX*threadsX,  blocksY*threadsY,  blocksZ*threadsZ};
    size_t local_dim[3] = {threadsX, threadsY, threadsZ};

    // Set args
    int i = 0;
    while (arg_sizes[i] != 0) {
        debug(user_context) << "    clSetKernelArg " << i
                            << " " << arg_sizes[i]
                            << " [" << (*((void **)args[i])) << " ...]\n";
        cl_int err = clSetKernelArg(f, i, arg_sizes[i], args[i]);
        if (err != CL_SUCCESS) {
            error(user_context) << "CL: clSetKernelArg failed: "
                                << get_opencl_error_name(err);
            return err;
        }
        i++;
    }
    // Set the shared mem buffer last
    // Always set at least 1 byte of shmem, to keep the launch happy
    debug(user_context)
        << "    clSetKernelArg " << i << " " << shared_mem_bytes << " [NULL]\n";
    err = clSetKernelArg(f, i, (shared_mem_bytes > 0) ? shared_mem_bytes : 1, NULL);
    if (err != CL_SUCCESS) {
        error(user_context) << "CL: clSetKernelArg failed "
                            << get_opencl_error_name(err);
        return err;
    }

    // Launch kernel
    debug(user_context)
        << "    clEnqueueNDRangeKernel "
        << blocksX << "x" << blocksY << "x" << blocksZ << ", "
        << threadsX << "x" << threadsY << "x" << threadsZ << " -> ";
    err = clEnqueueNDRangeKernel(ctx.cmd_queue, f,
                                 // NDRange
                                 3, NULL, global_dim, local_dim,
                                 // Events
                                 0, NULL, NULL);
    debug(user_context) << get_opencl_error_name(err) << "\n";
    if (err != CL_SUCCESS) {
        error(user_context) << "CL: clEnqueueNDRangeKernel failed: "
                            << get_opencl_error_name(err) << "\n";
        return err;
    }

    debug(user_context) << "    clReleaseKernel " << (void *)f << "\n";
    clReleaseKernel(f);

    #ifdef DEBUG_RUNTIME
    err = clFinish(ctx.cmd_queue);
    if (err != CL_SUCCESS) {
        error(user_context) << "CL: clFinish failed (" << err << ")\n";
        return err;
    }
    uint64_t t_after = halide_current_time_ns(user_context);
    debug(user_context) << "    Time: " << (t_after - t_before) / 1.0e6 << " ms\n";
    #endif
    return 0;
}

} // extern "C" linkage

namespace Halide { namespace Runtime { namespace Internal {
WEAK const char *get_opencl_error_name(cl_int err) {
    switch (err) {
    case CL_SUCCESS: return "CL_SUCCESS";
    case CL_DEVICE_NOT_FOUND: return "CL_DEVICE_NOT_FOUND";
    case CL_DEVICE_NOT_AVAILABLE: return "CL_DEVICE_NOT_AVAILABLE";
    case CL_COMPILER_NOT_AVAILABLE: return "CL_COMPILER_NOT_AVAILABLE";
    case CL_MEM_OBJECT_ALLOCATION_FAILURE: return "CL_MEM_OBJECT_ALLOCATION_FAILURE";
    case CL_OUT_OF_RESOURCES: return "CL_OUT_OF_RESOURCES";
    case CL_OUT_OF_HOST_MEMORY: return "CL_OUT_OF_HOST_MEMORY";
    case CL_PROFILING_INFO_NOT_AVAILABLE: return "CL_PROFILING_INFO_NOT_AVAILABLE";
    case CL_MEM_COPY_OVERLAP: return "CL_MEM_COPY_OVERLAP";
    case CL_IMAGE_FORMAT_MISMATCH: return "CL_IMAGE_FORMAT_MISMATCH";
    case CL_IMAGE_FORMAT_NOT_SUPPORTED: return "CL_IMAGE_FORMAT_NOT_SUPPORTED";
    case CL_BUILD_PROGRAM_FAILURE: return "CL_BUILD_PROGRAM_FAILURE";
    case CL_MAP_FAILURE: return "CL_MAP_FAILURE";
    case CL_INVALID_VALUE: return "CL_INVALID_VALUE";
    case CL_INVALID_DEVICE_TYPE: return "CL_INVALID_DEVICE_TYPE";
    case CL_INVALID_PLATFORM: return "CL_INVALID_PLATFORM";
    case CL_INVALID_DEVICE: return "CL_INVALID_DEVICE";
    case CL_INVALID_CONTEXT: return "CL_INVALID_CONTEXT";
    case CL_INVALID_QUEUE_PROPERTIES: return "CL_INVALID_QUEUE_PROPERTIES";
    case CL_INVALID_COMMAND_QUEUE: return "CL_INVALID_COMMAND_QUEUE";
    case CL_INVALID_HOST_PTR: return "CL_INVALID_HOST_PTR";
    case CL_INVALID_MEM_OBJECT: return "CL_INVALID_MEM_OBJECT";
    case CL_INVALID_IMAGE_FORMAT_DESCRIPTOR: return "CL_INVALID_IMAGE_FORMAT_DESCRIPTOR";
    case CL_INVALID_IMAGE_SIZE: return "CL_INVALID_IMAGE_SIZE";
    case CL_INVALID_SAMPLER: return "CL_INVALID_SAMPLER";
    case CL_INVALID_BINARY: return "CL_INVALID_BINARY";
    case CL_INVALID_BUILD_OPTIONS: return "CL_INVALID_BUILD_OPTIONS";
    case CL_INVALID_PROGRAM: return "CL_INVALID_PROGRAM";
    case CL_INVALID_PROGRAM_EXECUTABLE: return "CL_INVALID_PROGRAM_EXECUTABLE";
    case CL_INVALID_KERNEL_NAME: return "CL_INVALID_KERNEL_NAME";
    case CL_INVALID_KERNEL_DEFINITION: return "CL_INVALID_KERNEL_DEFINITION";
    case CL_INVALID_KERNEL: return "CL_INVALID_KERNEL";
    case CL_INVALID_ARG_INDEX: return "CL_INVALID_ARG_INDEX";
    case CL_INVALID_ARG_VALUE: return "CL_INVALID_ARG_VALUE";
    case CL_INVALID_ARG_SIZE: return "CL_INVALID_ARG_SIZE";
    case CL_INVALID_KERNEL_ARGS: return "CL_INVALID_KERNEL_ARGS";
    case CL_INVALID_WORK_DIMENSION: return "CL_INVALID_WORK_DIMENSION";
    case CL_INVALID_WORK_GROUP_SIZE: return "CL_INVALID_WORK_GROUP_SIZE";
    case CL_INVALID_WORK_ITEM_SIZE: return "CL_INVALID_WORK_ITEM_SIZE";
    case CL_INVALID_GLOBAL_OFFSET: return "CL_INVALID_GLOBAL_OFFSET";
    case CL_INVALID_EVENT_WAIT_LIST: return "CL_INVALID_EVENT_WAIT_LIST";
    case CL_INVALID_EVENT: return "CL_INVALID_EVENT";
    case CL_INVALID_OPERATION: return "CL_INVALID_OPERATION";
    case CL_INVALID_GL_OBJECT: return "CL_INVALID_GL_OBJECT";
    case CL_INVALID_BUFFER_SIZE: return "CL_INVALID_BUFFER_SIZE";
    case CL_INVALID_MIP_LEVEL: return "CL_INVALID_MIP_LEVEL";
    case CL_INVALID_GLOBAL_WORK_SIZE: return "CL_INVALID_GLOBAL_WORK_SIZE";
    default: return "<Unknown error>";
    }
}

}}} // namespace Halide::Runtime::Internal
