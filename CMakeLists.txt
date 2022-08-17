cmake_minimum_required(VERSION 3.11)
project(DVI-PAC VERSION 1.0.0
	DESCRIPTION "DVI-PAC project"
	)

# Configuration for directories
SET(PROJ_DIR	${PROJECT_SOURCE_DIR})
SET(BUILD_DIR	${PROJ_DIR}/build)
SET(LLVM_DIR	${PROJ_DIR}/llvm-project)
SET(LLVM_V_DIR	${PROJ_DIR}/llvm-project-vanilla)

execute_process(COMMAND sysctl -n hw.logicalcpu OUTPUT_VARIABLE NPROC)

add_custom_target(llvm-mac-all
	COMMAND cd ${LLVM_DIR}/ && rm -rf build
	COMMAND mkdir ${LLVM_DIR}/build
	COMMAND cd ${LLVM_DIR}/build && cmake 
	-DLLVM_BUILD_LLVM_DYLIB=ON 
	-DLLVM_LINK_LLVM_DYLIB=ON
	-DCMAKE_BUILD_TYPE=Debug ../llvm 
    -DCMAKE_CXX_STANDARD=17
	-DCMAKE_C_FLAGS=-g 
	-DCMAKE_C_COMPILER_TARGET=\"arm64-apple-darwin\" 
    -DCMAKE_ASM_COMPILER_TARGET=\"arm64-apple-darwin\" 
	-DCMAKE_CXX_COMPILER_TARGET=\"arm64-apple-darwin\"
	-DLLVM_DEFAULT_TARGET_TRIPLE=\"arm64-apple-darwin\"
	-DLLVM_TARGET_ARCH=AArch64
	-DLLVM_TARGETS_TO_BUILD=AArch64
	-DCOMPILER_RT_DEFAULT_TARGET_ONLY=ON
	-DCOMPILER_RT_BUILD_BUILTINS=ON
	-DCOMPILER_RT_BUILD_SANITIZERS=ON
	-DCOMPILER_RT_BUILD_XRAY=OFF
	-DCOMPILER_RT_BUILD_LIBFUZZER=OFF
    -DLLVM_ENABLE_PROJECTS=\"clang\;compiler-rt\;lld\" 
	-G \"Unix Makefiles\" 
	COMMAND cd ${LLVM_DIR}/build && make -j${NPROC}
)

add_custom_target(llvm-mac-compiler-rt
	COMMAND cd ${LLVM_DIR}/build && rm -rf aarch64-compiler-rt 
	COMMAND mkdir ${LLVM_DIR}/build/aarch64-compiler-rt
	COMMAND cd ${LLVM_DIR}/build/aarch64-compiler-rt && cmake
	-DCMAKE_BUILD_TYPE=Debug ${LLVM_DIR}/compiler-rt
	-DCMAKE_CROSSCOMPILING=True
	-DCMAKE_C_COMPILER_TARGET=\"arm64e-apple-darwin\" 
    -DCMAKE_ASM_COMPILER_TARGET=\"arm64e-apple-darwin\" 
	-DCMAKE_CXX_COMPILER_TARGET=\"arm64e-apple-darwin\"
	-DLLVM_DEFAULT_TARGET_TRIPLE=\"arm64e-apple-darwin\"
    -DLLVM_TARGET_ARCH=AArch64
    -DLLVM_TARGETS_TO_BUILD=AArch64
	-DCOMPILER_RT_DEFAULT_TARGET_ONLY=ON
	-DCOMPILER_RT_BUILD_BUILTINS=ON
	-DCOMPILER_RT_BUILD_SANITIZERS=ON
	-DCOMPILER_RT_BUILD_XRAY=OFF
	-DCOMPILER_RT_BUILD_LIBFUZZER=OFF
	-DCOMPILER_RT_BUILD_PROFILE=OFF
	-DLLVM_TARGETS_TO_BUILD=AArch64
	-DLLVM_CONFIG_PATH=\"${PROJ_DIR}/llvm-project-vanilla/build/bin/llvm-config\"
	-DCMAKE_AR=\"${PROJ_DIR}/llvm-project-vanilla/build/bin/llvm-ar\"
	-DCMAKE_NM=\"${PROJ_DIR}/llvm-project-vanilla/build/bin/llvm-nm\"
	-DCMAKE_RANLIB=\"${PROJ_DIR}/llvm-project-vanilla/build/bin/llvm-ranlib\"
	-G \"Unix Makefiles\"
    COMMAND cd ${LLVM_DIR}/build/aarch64-compiler-rt && make -j${NPROC}
	COMMAND cd ${LLVM_DIR}/build/aarch64-compiler-rt/lib/darwin/ && cp * ${LLVM_DIR}/build/lib/clang/10.0.0/lib/darwin/
)

add_custom_target(llvm-only-remake
	COMMAND cd ${LLVM_DIR}/build && make -j${NPROC}
)

add_custom_target(compiler-rt-mac-remake
	COMMAND cd ${LLVM_DIR}/build/aarch64-compiler-rt && make -j${NPROC}
	COMMAND cd ${LLVM_DIR}/build/aarch64-compiler-rt/lib/darwin/ && cp * ${LLVM_DIR}/build/lib/clang/10.0.0/lib/darwin/
)

add_custom_target(llvm-remake
	COMMAND cd ${LLVM_DIR}/build && make -j${NPROC}
	COMMAND cd ${LLVM_DIR}/build/aarch64-compiler-rt && make -j${NPROC}
	COMMAND cd ${LLVM_DIR}/build/aarch64-compiler-rt/lib/linux/ && cp * ${LLVM_DIR}/build/lib/clang/10.0.1/lib/linux/
)

add_custom_target(llvm-remake-m1
	COMMAND cd ${LLVM_DIR}/build && make -j${NPROC}
	COMMAND cd ${LLVM_DIR}/build/projects/compiler-rt && make -j${NPROC}
)

add_custom_target(llvm-clean
	COMMAND cd ${LLVM_DIR}/ && rm -rf build
)

add_custom_target(llvm-vanilla
	COMMAND cd ${LLVM_V_DIR}/ && rm -rf build
	COMMAND mkdir ${LLVM_V_DIR}/build
	COMMAND cd ${LLVM_V_DIR}/build && cmake 
	-DLLVM_BUILD_LLVM_DYLIB=ON 
	-DLLVM_LINK_LLVM_DYLIB=ON
	-DCMAKE_BUILD_TYPE=Debug ../llvm 
	-DCMAKE_C_FLAGS=-g 
	-DLLVM_OPTIMIZED_TABLEGEN=ON
	-DLLVM_ENABLE_PROJECTS=\"clang\;compiler-rt\" 
	-G \"Unix Makefiles\" 
	COMMAND cd ${LLVM_V_DIR}/build && make -j${NPROC}
)

add_custom_target(llvm-vanilla-remake
	COMMAND cd ${LLVM_V_DIR}/build && make -j${NPROC}
)

add_custom_target(llvm-vanilla-clean
	COMMAND cd ${LLVM_V_DIR}/ && rm -rf build
)
