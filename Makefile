# Directory where this Makefile is located
MAKEFILE_DIR := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))

LLVM_PATH := $(realpath $(MAKEFILE_DIR)/../llvm-project-llvmorg-21.1.8/build)
BUILD_DIR := $(MAKEFILE_DIR)/build


default_target: all
.PHONY: all clean test

all: $(BUILD_DIR)/build.ninja
	@cmake --build $(BUILD_DIR)

$(BUILD_DIR)/build.ninja:
	@mkdir -p $(BUILD_DIR)
	@cd $(BUILD_DIR) && cmake \
		-DCMAKE_BUILD_TYPE=Release \
		-DCMAKE_PREFIX_PATH="$(LLVM_PATH)" \
		-DBUILD_TV=1 \
		-GNinja \
		..

clean:
	@rm -rf $(BUILD_DIR)

test:
	@cd $(BUILD_DIR) && ninja check
