#!/bin/bash

make $@ \
    CC=${HOME}/llvm/build/bin/clang \
    AR=${HOME}/llvm/build/bin/llvm-ar \
    NM=${HOME}/llvm/build/bin/llvm-nm \
    STRIP=${HOME}/llvm/build/bin/llvm-strip \
    OBJCOPY=${HOME}/llvm/build/bin/llvm-objcopy \
    OBJDUMP=${HOME}/llvm/build/bin/llvm-objdump \
    OBJSIZE=${HOME}/llvm/build/bin/llvm-size \
    READELF=${HOME}/llvm/build/bin/llvm-readelf \
    HOSTCC=${HOME}/llvm/build/bin/clang \
    HOSTCXX=${HOME}/llvm/build/bin/clang++ \
    HOSTAR=${HOME}/llvm/build/bin/llvm-ar \
    LLC=${HOME}/llvm/build/bin/llc
