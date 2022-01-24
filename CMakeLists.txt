cmake_minimum_required (VERSION 3.0)
project (dfa)

set (LLVM_ROOT ../install)
set (CMAKE_CXX_STANDARD 11)

#set (CMAKE_CXX_FLAGS "-O3 -Wall -Wextra")
#set (CMAKE_CXX_FLAGS "-O3 -Wno-narrowing")
set (CMAKE_CXX_FLAGS "-O3 -fno-rtti")

add_executable (dfa Analysis.cc)
target_include_directories (dfa PUBLIC ${LLVM_ROOT}/include)
target_link_directories (dfa
    PUBLIC ${LLVM_ROOT}/lib
    )
target_link_libraries (dfa
    # c++ mangling
    llvmdemangle    # llvm demangler
    # BC reader
    LLVMIRReader
    LLVMBitReader
    LLVMAsmParser
    # BC output
    LLVMBitWriter
    LLVMObject
    LLVMMCParser
    LLVMMC
    # Common
    LLVMAnalysis
    LLVMCore
    LLVMSupport
    LLVMTarget
    LLVMBinaryFormat
    LLVMProfileData
    # aux lib
    z
    ncurses
    tinfo
    pthread)
