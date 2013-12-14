CXX ?= g++

ifdef BUILD_PREFIX
LIB_HALIDE = bin/$(BUILD_PREFIX)/libHalide.a
else
LIB_HALIDE = bin/libHalide.a
endif

LIBPNG_LIBS_DEFAULT = $(shell libpng-config --ldflags)
LIBPNG_CXX_FLAGS ?= $(shell libpng-config --cflags)
# Workaround for libpng-config pointing to 64-bit versions on linux even when we're building for 32-bit
ifneq (,$(findstring -m32,$(CXX)))
ifneq (,$(findstring x86_64,$(LIBPNG_LIBS_DEFAULT)))
LIBPNG_LIBS ?= -lpng
endif
endif
LIBPNG_LIBS ?= $(LIBPNG_LIBS_DEFAULT)
PNGFLAGS=$(LIBPNG_LIBS) $(LIBPNG_CXX_FLAGS)

ifneq (,$(findstring ptx,$(HL_TARGET)))
  CUDA_LDFLAGS=-L/usr/lib/nvidia-current -lcuda
endif
ifneq (,$(findstring cuda,$(HL_TARGET)))
  CUDA_LDFLAGS=-L/usr/lib/nvidia-current -lcuda
endif

all: scan

scan: ../../ ../../$(LIB_HALIDE) scan.cpp
	$(MAKE) -C ../../ $(LIB_HALIDE) -j12
	$(CXX) $(CPPFLAGS) scan.cpp -I ../../include/ -I ../support ../../$(LIB_HALIDE) -o scan  -lpthread -ldl -lncurses $(PNGFLAGS) $(CUDA_LDFLAGS)

clean:
	rm -f scan
