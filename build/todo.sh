#!/bin/bash
# set -e
set -x
./clean.sh
# export AFL_USE_ASAN=1
export AFL="/home/matesoos/development/AFLplusplus"
export LD_LIBRARY_PATH="/usr/lib:$LD_LIBRARY_PATH"
env
# CC=$AFL/afl-cc CXX=$AFL/afl-c++ cmake -DCMAKE_C_COMPILERC=$AFL/afl-cc -DCMAKE_CXX_COMPILER=$AFL/afl-c++ ..
AR=llvm-ar RANLIB=llvm-ranlib AS=llvm-as cmake -DCMAKE_C_COMPILERC=$AFL/afl-cc -DCMAKE_CXX_COMPILER=$AFL/afl-c++ -DPEDANTIC=OFF ..
make -j12 VERBOSE=1
# CC=$AFL/afl-cc CXX=$AFL/afl-c++ make -j12 VERBOSE=1
