#!/bin/bash

LLVM_ROOT=$(realpath `pwd`/../install)
LLVM_SRC=$(realpath `pwd`/../llvm-mirror)

pushd ${LLVM_SRC}
mkdir -p build && cd build
cmake .. -DCMAKE_INSTALL_PREFIX=${LLVM_ROOT} -DCMAKE_BUILD_TYPES=Release -DLLVM_TARGETS_TO_BUILD=all && \
    make -j20 && make install
popd
