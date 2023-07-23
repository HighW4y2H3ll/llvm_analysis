#!/bin/bash

cmake ${HOME}/llvm/llvm-project/llvm -G "Ninja" -DLLVM_TARGETS_TO_BUILD="all" \
    -DCMAKE_INSTALL_PREFIX="${HOME}/llvm/install" \
    -DLLVM_ENABLE_PROJECTS="clang;clang-tools-extra;compiler-rt;libcxx;libcxxabi"    \
    -DCMAKE_BUILD_TYPE=Release
