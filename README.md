# PACTight

This repository contains the source code for the USENIX Security'22 paper:

*Tightly Seal Your Sensitive Pointers with PACTight*\
*Mohannad Ismail, Andrew Quach, Christopher Jelesnianski, Yeongjin Jang, Changwoo Min*\
*In Proceedings of the 31st USENIX Security Symposium (USENIX Security 2022)*

## Directory structure
```{.sh}
pactight
├── CMakeLists.txt    # CMake file for building PACTight
├── example           # Example code
├── llvm-project      # PACTight compiler
```


## Setup notes
PACTight uses a fork of Apple's LLVM (swift-5.3.1-RELEASE), and thus this will only work on an Apple macOS machine with an ARM processor. This has been tested on an Apple Mac Mini M1.

## How to compile PACTight
```bash
$ mkdir build
$ cd build
$ cmake ..
$ make llvm-mac-all
```

#### Running examples
```bash
$ cd example
$ ./pactight_compile_c example
$ ./pactight_compile_c++ example_cpp
$ ./example
$ ./example_cpp
```
If you wish to use the PACTight compiler, please check the compile scripts in the example directory for all the flags necessary. You can copy the file and modify it as needed.
