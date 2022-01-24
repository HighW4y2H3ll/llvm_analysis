
OUTPUT_PATH="build/output"
LOG_PATH="build/log"
X86_BC_PATH="../llvm6bcfiles"
SPARC_BC_PATH="/opt/sparc_bc_files/svc_bc_new"
MAX_NUM_THREAD=10
COUNT=0

for f in `ls ${X86_BC_PATH}/*.bc`; do
    # Skip delivergie.bc because of inlined LLVM IR optimization
    # sub_403619__Z19symbolic_initializePc :   %38 = tail call i64 bitcast (i64 (i64, i64, i64, i64, i64, i64, i64, i64)* @_Znwm to i64 (i64)*)(i64 80), !noalias !1271, !blpsymex !1265
    if [ `basename ${f}` == "delivergie.bc" ]; then
        continue;
    fi
    { time taskset -c $((2*COUNT+20)) ./build/dfa $f -o ${OUTPUT_PATH}/x86/new_`basename ${f}` &> ${LOG_PATH}/x86/log_`basename ${f}`; } 2> ${LOG_PATH}/x86/`basename ${f}`.time &
    { time taskset -c $((2*COUNT+1+20)) ./build/dfa $f -c -o ${OUTPUT_PATH}/x86/cutoff_`basename ${f}` &> ${LOG_PATH}/x86/cutlog_`basename ${f}`; } 2> ${LOG_PATH}/x86/cutoff_`basename ${f}`.time &
    COUNT=$((COUNT+1))
    if ((COUNT == $MAX_NUM_THREAD)); then
        wait
        COUNT=0
    fi
done

wait

COUNT=0
for f in `ls ${SPARC_BC_PATH}/*.bc`; do
    { time taskset -c $((2*COUNT+20)) ./build/dfa $f -t sparc -o ${OUTPUT_PATH}/sparc/new_`basename ${f}` &> ${LOG_PATH}/sparc/log_`basename ${f}`; } 2> ${LOG_PATH}/sparc/`basename ${f}`.time &
    { time taskset -c $((2*COUNT+1+20)) ./build/dfa $f -c -t sparc -o ${OUTPUT_PATH}/sparc/cutoff_`basename ${f}` &> ${LOG_PATH}/sparc/cutlog_`basename ${f}`; } 2> ${LOG_PATH}/sparc/cutoff_`basename ${f}`.time &
    COUNT=$((COUNT+1))
    if ((COUNT == $MAX_NUM_THREAD)); then
        wait
        COUNT=0
    fi
done

wait
