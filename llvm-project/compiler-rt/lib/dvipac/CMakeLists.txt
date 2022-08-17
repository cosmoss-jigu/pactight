
set(DVIPAC_SOURCES
	libpac.c
	hashtable_1.c
)

include_directories(..)

if (APPLE)
    set(DVIPAC_FLAGS "${SANITIZER_COMMON_CFLAGS} -fno-ptrauth-intrinsics -fno-ptrauth-returns -fno-ptrauth-calls -fno-ptrauth-indirect-gotos -fno-ptrauth-auth-traps -fno-ptrauth-soft -flto")
else()
    set(DVIPAC_FLAGS "${SANITIZER_COMMON_CFLAGS}")
endif()

#set(DVIPAC_FLAGS "${SANITIZER_COMMON_CFLAGS} -march=armv8.3-a -I/home/imohannad/imohannad-ssd/dvi-pac/Resources/sysroot-glibc-linaro-2.25-2018.05-aarch64-linux-gnu/usr/include -B/home/imohannad/imohannad-ssd/dvi-pac/Resources/gcc-linaro-7.3.1-2018.05-x86_64_aarch64-linux-gnu --sysroot=/home/imohannad/imohannad-ssd/dvi-pac/Resources/sysroot-glibc-linaro-2.25-2018.05-aarch64-linux-gnu")

add_custom_target(dvipac)

#message(FATAL_ERROR "CMAKE PROCESSOR ${CMAKE_C_COMPILER_TARGET}")

if (APPLE)
    add_compiler_rt_runtime(clang_rt.dvipac
        SHARED
        OS ${SANITIZER_COMMON_SUPPORTED_OS}
        ARCHS arm64e
        SOURCES ${DVIPAC_SOURCES}
        CFLAGS ${DVIPAC_FLAGS}
        PARENT_TARGET dvipac)
else()
    add_compiler_rt_runtime(clang_rt.dvipac
        STATIC
        ARCHS aarch64
        SOURCES ${DVIPAC_SOURCES}
        CFLAGS ${DVIPAC_FLAGS}
        PARENT_TARGET dvipac)
endif()

add_sanitizer_rt_symbols(clang_rt.dvipac)

add_dependencies(compiler-rt dvipac)
