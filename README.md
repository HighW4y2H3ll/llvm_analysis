
### Install

```
mkdir build && cd build
cmake ..
make
```

### Algorithm

Walk through every instruction of functions starting from entry point functions. Build dataflow table per function, with constructor call as the start, and indirect call as sink. Infer indirect call class types on the fly.

- Pass One: Build dataflow table && infer indirect calls on the fly.
- Pass Two: Infer all indirect calls again after everything.
- Pass Three: Resolve possible virtual functions with the same class name prefix as we found in the indirect call.

### Run

```
./dfa ${BC_FILE} [-l ${LOG_FILE}] [-o ${BC_OUTPUT}] [-v] [-c] [-t x86|sparc]

-v :  verbose output with all the resolved class names, virtual functions
-c :  use cutoff function list to speed things up
-t :  switch to select target architectures (default x86)
```
