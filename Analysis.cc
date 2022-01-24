
#include <map>
#include <set>

#include "Demangle/Demangle.h"
#include "demangle.h"

#include "CalledFuncCount.h"

#include <llvm/Support/SourceMgr.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/IR/Module.h>
#include <llvm-c/Core.h>
#include <llvm/IR/InstIterator.h>
#include <llvm/IR/CallSite.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/IR/Constants.h>
#include <llvm/Support/FileSystem.h>
#include <llvm/Bitcode/BitcodeWriter.h>
#include <llvm/Support/CommandLine.h>
#include <llvm/IR/Operator.h>


static llvm::cl::opt<std::string> input_bc (llvm::cl::Positional, llvm::cl::desc("bc input file"), llvm::cl::Required);
static llvm::cl::opt<std::string> output_bc ("o", llvm::cl::desc("bc output"), llvm::cl::init(""));
static llvm::cl::opt<std::string> log_file ("l", llvm::cl::desc("log file"), llvm::cl::init(""));
static llvm::cl::opt<bool> use_cutoff ("c", llvm::cl::desc("use cutoff functions"));
static llvm::cl::opt<bool> verbose ("v", llvm::cl::desc("verbose output"));
static llvm::cl::opt<std::string> target_arch ("t", llvm::cl::desc("target arch: x86, sparc... (default: x86)"), llvm::cl::init("x86"));

#include "CutoffFunctionList.def"

llvm::raw_ostream *LOG = &llvm::errs();

size_t total_func;
size_t func_count = 0;

llvm::LLVMContext *context_ = nullptr;
std::unique_ptr<llvm::Module> module;

std::map<std::string, llvm::StructType*> ObjTypeMap;    // Mapping of Struct Type name to LLVM Struct Type


struct Sym;
struct SymValue;

typedef std::map<Sym, std::set<SymValue>> SymTab;
std::map<llvm::Function*, SymTab> FuncPassThro;   // Function Pass Thro to treat Func as a black box for dataflow propagation

typedef enum {
    SEEN,   // Seen and is undergoing analyzing
    DONE,   // Done analyzing
} FunctionState;

std::map<llvm::Function*, FunctionState> FuncState;

struct Sym {
    typedef enum {
        Constant,   // Address/Offset
        Variable,   // pointer to LLVM Valueor
        Register,   // pointer to register slot
        MemAddr,    // Anything from 2nd Arg(%1), Addr derived from PC; data_ will be ignored.
        Memory,     // 3rd Arg(%2) of McSema Lifted Function, struct.Memory*, just for compatiblity
        FuncArg,    // Function Argument
        Return,     // Function Return
        None,       // For Undefined Sym
    } DataType;

public:
    DataType type_;
    size_t data_;
    size_t version_;

public:
    bool operator< (const Sym &other) const {
        return (type_ < other.type_)
            || (type_ == other.type_ && data_ < other.data_)
            || (type_ == other.type_ && data_ == other.data_ && version_ < other.version_);
    }
    bool operator== (const Sym &other) const {
        return (type_ == other.type_) && (data_ == other.data_) && (version_ == other.version_);
    }
};

struct SymBase {
    Sym::DataType type_;
    size_t data_;

public:
    bool operator< (const SymBase &other) const {
        return (type_ < other.type_) || (type_ == other.type_ && data_ < other.data_);
    }

public:
    SymBase (Sym::DataType type, size_t data) : type_(type), data_(data) {}
};

typedef std::map<SymBase, size_t> VerTabType;
// Version Table to resolve load-store variable conflict, since Store breaks SSA
// Version number is increased only on Store, when has a conflict in SymMap
std::map<llvm::Function*, VerTabType> FuncVerTab;   // VerTab is maintained per function


std::map<Sym, llvm::Function*> SymLookup;   // Helper to make Sym -> Function Lookup easier
std::map<llvm::Function*, std::set<llvm::Function*>> CallGraph;   // Helper to lookup callees inside a Function (except Ctor && Indirect Call)
std::map<llvm::Function*, std::set<llvm::Function*>> CtorCallGraph;   // Helper to lookup Ctor callees inside a Function
std::map<llvm::Function*, std::set<llvm::Instruction*>> ICallGraph;   // Helper to lookup Indirect Callsites inside a Function

struct SymValue {
    typedef enum {
        Ref,        // Store, e.g. "dst_ptr = Ref(val)"
        Deref,      // Load, e.g. " lhs = Deref(rhs_ptr)"
        Add,
        Cast,
        AuxGEP,     // Handle Complicated GetElementPtrInst
        Phi,        // Phi Node
        None,       // Direct Use of data1_ or Undefined
    } OpType;

public:
    Sym data1_;
    OpType op_;
    Sym data2_; // Only Used in Add, and Phi
    size_t nextra_;  // Only in Phi if contains more than 2 nodes
    Sym *extra_data_;

public:
    bool operator< (const SymValue &other) const {
        return (data1_ < other.data1_)
            || (data1_ == other.data1_ && op_ < other.op_)
            || (data1_ == other.data1_ && op_ == other.op_ && data2_ < other.data2_)
            || (data1_ == other.data1_ && op_ == other.op_ && data2_ == other.data2_ && nextra_ < other.nextra_)
            || (data1_ == other.data1_ && op_ == other.op_ && data2_ == other.data2_ && nextra_ == other.nextra_ && extra_data_ < other.extra_data_);
    }
};

Sym g_s_empty {Sym::None, 0, 0};
SymValue g_sv_empty {g_s_empty, SymValue::None, g_s_empty, 0, 0};

std::map<llvm::Instruction*, std::set<std::pair<std::string, size_t/*dataflow depth*/>>> ICallObj;            // All possible ClassName related to Indirect CallInst
std::set<llvm::Instruction*> PltICall;  // Log all indirect calls that seems like related to a PLT call (lifted from McSema)


std::map<Sym, std::string> RegObj; // Update on Ctor, Mapping different Versions of this pointer register to Class Name
std::map<Sym, std::set<Sym>> RegUses;   // All direct Uses of Each version of Register


typedef enum {
    ARCH_X86,
    ARCH_SPARC,
} ArchType;
ArchType target_mode;

#include "X86.inl"
#include "SPARC.inl"


void initDataflowFromReg(std::set<Sym> &toResolve, std::set<std::pair<std::string, size_t>> &result) {
    switch (target_mode) {
    case ARCH_X86:
        initDataflowFromReg_X86(toResolve, result);
        break;
    case ARCH_SPARC:
        initDataflowFromReg_SPARC(toResolve, result);
        break;
    default:
        break;
    }
}

bool checkRegThisPtr(Sym &s) {
    switch (target_mode) {
    case ARCH_X86:
        return checkRegThisPtr_X86(s);
    case ARCH_SPARC:
        return checkRegThisPtr_SPARC(s);
    default:
        return false;
    }
}

void updateThisPtrRegVersion(std::string ctor) {
    switch (target_mode) {
    case ARCH_X86:
        updateThisPtrRegVersion_X86(ctor);
        break;
    case ARCH_SPARC:
        updateThisPtrRegVersion_SPARC(ctor);
        break;
    default:
        break;
    }
}

bool checkGepGPR(llvm::GetElementPtrInst *gep) {
    switch (target_mode) {
    case ARCH_X86:
        return checkGepGPR_X86(gep);
    case ARCH_SPARC:
        return checkGepGPR_SPARC(gep);
    default:
        return false;
    }
}

void updateRegDefSet(llvm::GetElementPtrInst *gep, Sym &sl, SymTab &SymMap, llvm::Function *func) {
    switch (target_mode) {
    case ARCH_X86:
        updateRegDefSet_X86(gep, sl, SymMap, func);
        break;
    case ARCH_SPARC:
        updateRegDefSet_SPARC(gep, sl, SymMap, func);
        break;
    default:
        break;
    }
}

void handleGepUnionAnon(llvm::GetElementPtrInst *gep, llvm::Function *func, Sym &sl, SymTab &SymMap, VerTabType &VerTab) {
    switch (target_mode) {
    case ARCH_X86:
        handleGepUnionAnon_X86(gep, func, sl, SymMap, VerTab);
        break;
    case ARCH_SPARC:
        handleGepUnionAnon_SPARC(gep, func, sl, SymMap, VerTab);
        break;
    default:
        break;
    }
}




std::set<std::string> McSemaInternalFunctions ({
        "__remill_sync_hyper_call",
        });

bool isInternalFunction(const std::string &fn) {
    return (McSemaInternalFunctions.find(fn) != McSemaInternalFunctions.end());
}


void dumpSymMap(llvm::Function *func, const SymTab &SymMap) {
    (*LOG) << "----------- SymMap "<< SymMap.size() <<" : " << func->getName() << " ------------------\n";
    for (auto &debuge : SymMap) {
        (*LOG) << " key " << debuge.first.type_ << " , " << (void*)debuge.first.data_ << " , " << debuge.first.version_ <<"";
        for (auto &v : debuge.second) {
            (*LOG) << " >> value : " << v.data1_.type_ << " , " << (void*)v.data1_.data_ << " , " << v.data1_.version_ << " : " << v.op_ << "\n";
        }
    }
    (*LOG) << "--------------------------------------------------\n";
}
void dumpVerTab(llvm::Function *func, const VerTabType &VerTab) {
    (*LOG) << "----------- VerTab "<< VerTab.size() <<" : " << func->getName() << " ------------------\n";
    for (auto &debuge : VerTab) {
        (*LOG) << " > " << debuge.first.type_ << " , " << (void*)debuge.first.data_ << " : " << debuge.second << "\n";
    }
    (*LOG) << "--------------------------------------------------\n";
}

void dumpICallStat() {
    // Count ctor #, indirect callsite #, ctor callsite #, inferred indirect callsite #, dataflow depth
    size_t nresolved = 0;
    size_t ntarget = 0;
    std::set<std::string> total_class;
    std::set<std::string> total_ctor;
    for (auto &e : ICallObj) {
        if (e.second.size()) {
            nresolved++;
            ntarget += e.second.size();
            for (auto &p : e.second) {
                total_class.insert(p.first);
            }
        }
    }
    for (auto &e : RegObj) {
        total_ctor.insert(e.second);
    }
    (*LOG) << "Final # icalls : " << ICallObj.size() << " , resolved : " << nresolved << " , targets : " << ntarget << " , total classes: " << total_class.size() << " / " << total_ctor.size() << "\n";

    // Print Resolved Objects & dataflow depth
    if (verbose) {
        (*LOG) << "Resolved ICalls:\n";
        for (auto &e : ICallObj) {

            (*LOG) << "  " << e.first->getFunction()->getName() << " icall inst: ";
            e.first->printAsOperand(*LOG, false/*dont print type*/, module.get());
            (*LOG) << "\n";

            for (auto &o : e.second) {
                (*LOG) << "      class: " << o.first << " , depth: " << o.second << "\n";
            }
        }
    }
}



bool checkPltSeg(const Sym &sym) {

    (*LOG) << "Debug plt check : " << (sym.type_ == Sym::Variable) << "\n";
    if (sym.type_ != Sym::Variable) // Skip non-var
        return false;

    llvm::Value *var = (llvm::Value*)sym.data_;
    (*LOG) << "debug " << *var << "\n";
    auto varname = var->getName();
    // McSema Optimization would collide multiple instructions into one, as in the case of load address from plt
    llvm::LoadInst *loadinst = llvm::dyn_cast<llvm::LoadInst>(var);
    if (loadinst)
        var = loadinst->getOperand(0);
    llvm::IntToPtrInst *i2pinst = llvm::dyn_cast<llvm::IntToPtrInst>(var);
    if (i2pinst) {
        (*LOG) << "debug " << *i2pinst << "\n";
        llvm::Instruction *addinst = llvm::dyn_cast<llvm::Instruction>(i2pinst->getOperand(0));
        if (addinst) {
            (*LOG) << "debug " << *addinst << "\n";
            llvm::PtrToIntInst *p2iinst = llvm::dyn_cast<llvm::PtrToIntInst>(addinst->getOperand(0));
            if (p2iinst) {
                (*LOG) << "debug " << *p2iinst << "\n";
                varname = p2iinst->getOperand(0)->getName();
                (*LOG) << "check plt seg variable : " << varname << " , " << *var << "\n";
                if (varname.startswith("seg_") && varname.endswith("__got_plt")) {
                    return true;
                }
            }
        }
    }

    return false;
}

// Copied from LLVM 9.0 - check CallInst is Indirect Call
bool isIndirectCall(llvm::CallInst *callinst) {
    const llvm::Value *V = callinst->getCalledValue();
    if (llvm::isa<llvm::Function>(V) || llvm::isa<llvm::Constant>(V))
        return false;
    if (callinst->isInlineAsm())
        return false;
    return true;
}

bool isFuncTyLifted(llvm::FunctionType *fty);
Sym inferSym(llvm::Value *v, VerTabType &VerTab);

void doIndirectCall(llvm::Instruction *icall, bool useAllRegVer = false, llvm::Function *callee = nullptr) {
    llvm::CallInst *ic = llvm::dyn_cast<llvm::CallInst>(icall);
    llvm::Function *func = ic->getFunction();

    std::set<Sym> toResolve;
    std::set<std::pair<Sym, size_t/*dataflow depth count*/>> resolveQueue, toEnqueue;
    std::set<std::pair<std::string, size_t>> result;

    if (callee) {   // __mcsema_detach_call_value

        Sym target = inferSym(ic->getArgOperand(1), FuncVerTab[func]);
        toResolve.insert(target);

        initDataflowFromReg(toResolve, result);

        if (useAllRegVer) {
            for (auto &r : RegUses) {
                toResolve.insert(r.second.begin(), r.second.end());
            }
        }

    } else {    // Now it should be truely indirect calls
        if (isFuncTyLifted(ic->getFunctionType())) {

            initDataflowFromReg(toResolve, result);

            if (useAllRegVer) {
                for (auto &r : RegUses) {
                    toResolve.insert(r.second.begin(), r.second.end());
                }
            }

            Sym target = inferSym(ic->getCalledValue(), FuncVerTab[func]);
            toResolve.insert(target);

        } else if (ic->getNumArgOperands() > 0) {    // Treated as normal calls - lookup the first arg

            Sym arg = inferSym(ic->getArgOperand(0), FuncVerTab[func]);
            toResolve.insert(arg);
            //(*LOG) << "Debug 1st Arg in icall " << *ic->getArgOperand(0) << "\n";
            Sym target = inferSym(ic->getCalledValue(), FuncVerTab[func]);
            toResolve.insert(target);
            //(*LOG) << "Debug Indirect call oprand " << *ic->getCalledValue() << "\n";

        } else {
            // Log and skip
            (*LOG) << "[debug] indirect call with 0 args in " << ic->getFunction()->getName() << " : " << *ic << "\n";
            return;
        }
    }

    for (auto &e : toResolve) {
        resolveQueue.insert(std::make_pair(e, 0));
    }

    //(*LOG) << "XXXX : " << *(ic->arg_begin()) << "\n";
    //(*LOG) << "ICall : " << *icall << "\n";
    // Resolve Sym Queue
    std::set<Sym> seenSym;
    while (resolveQueue.size()) {
        auto &e = *resolveQueue.begin();
        Sym s = e.first;
        size_t depth = e.second;

        resolveQueue.erase(e);

        // Resolve Register
        if (checkRegThisPtr(s)) {
            if (RegObj.find(s) != RegObj.end()) {   // Entry point func may take this ptr in args. could do indirect call before any ctor
                result.insert(std::make_pair(RegObj[s], depth + 1));
            }

            // Pass Through to resolve reg alias
            //(*LOG) << "Debhug found register " << s.data_ << " , " << (void*)s.version_ << "\n";
        }

        // Depricated: No longer a problem in later version of McSema now
        // - Check if the variable is seg_xxx__got_plt global var
        //if (checkPltSeg(s)) {
        //    PltICall.insert(icall);
        //    continue;
        //}

        if (seenSym.find(s) != seenSym.end())   // Avoid loop
            continue;
        seenSym.insert(s);

        /*
        if (s.type_ == Sym::Variable)
            (*LOG) << "DEBUG symbol " << *(llvm::Value*)s.data_ << " , " << s.version_ << "\n";
        else
            (*LOG) << "Debug symbol " << s.type_ << " , " << (void*)s.data_ << " , " << s.version_ << "\n";
        */
        if (SymLookup.find(s) == SymLookup.end()) {   // Skip Globally Versioned Reg that are possible this ptrs
            // NOTE: Remove the check for This Pointer Register:
            // - Found backward edges in loops -
            // we may have uses of Variables defined from the Instruction that we haven't processed yet
            //
            // e.g.
            // block_e43f30:
            //   %483 = tail call %struct.Memory* @__mcsema_detach_call_value(%struct.State* nonnull %0, i32 %529, %struct.Memory* %2)
            // ...
            // block_e43ef8:
            //   %529 = add nuw nsw i32 %283, 44
            //
            //assert (checkRegThisPtr(s));
            continue;
        }

        llvm::Function *f = SymLookup[s];
        SymTab &SymMap = FuncPassThro[f];

        //(*LOG) << "Debug Sym " << s.type_ << " , " << (void*)s.data_ << " , " << (void*)s.version_ << "\n";
        if (SymMap.find(s) == SymMap.end()) {   // It's possible that some Sym wont resolve to Register
            //(*LOG) << "Failed to Resolve " << s.type_ << " , " << (void*)s.data_ << " , " << (void*)s.version_;
            //if (s.type_ == Sym::Variable)
            //    (*LOG) << *(llvm::Value*)s.data_;
            //(*LOG) << "\n";
            continue;
        }

        toEnqueue.clear();
        //(*LOG) << "size " << SymMap[s].size() << "\n";
        for (auto &sv : SymMap[s]) {
            //(*LOG) << "    vals : " << sv.op_ << " , " << sv.data1_.type_ << " , " << (void*)sv.data1_.data_ << " , " << sv.data1_.version_ <<"\n";
            switch (sv.op_) {
            case SymValue::Ref:
            case SymValue::Deref:
            case SymValue::Cast:
            case SymValue::None:
                toEnqueue.insert(std::make_pair(sv.data1_, depth + 1));
                break;
            case SymValue::Add:
                toEnqueue.insert(std::make_pair(sv.data1_, depth + 1));
                toEnqueue.insert(std::make_pair(sv.data2_, depth + 1));
                break;
            case SymValue::Phi:
                toEnqueue.insert(std::make_pair(sv.data1_, depth + 1));
                if (sv.data2_.type_ != Sym::None) {
                    toEnqueue.insert(std::make_pair(sv.data2_, depth + 1));
                    for (auto i = 0; i < sv.nextra_; i++) {
                        toEnqueue.insert(std::make_pair(sv.extra_data_[i], depth + 1));
                    }
                }
                break;
            case SymValue::AuxGEP:  // Skip for now
            default:
                break;
            }
        }
        // Ignore All Variable Versions for Registers
        if (s.type_ == Sym::Register) {
            for (auto &varpair : toEnqueue) {
                if (varpair.first.type_ == Sym::Variable) { // For Symn::Variable only
                    SymBase key(varpair.first.type_, varpair.first.data_);
                    for (size_t i = 0; i <= FuncVerTab[func][key]; i++) {
                        Sym newsym {key.type_, key.data_, i};
                        resolveQueue.insert(std::make_pair(newsym, varpair.second));
                    }
                } else {
                    resolveQueue.insert(varpair);
                }
            }
        } else {
            resolveQueue.insert(toEnqueue.begin(), toEnqueue.end());
        }
    }

    // Update Resolved Class Info
    ICallObj[icall].insert(result.begin(), result.end());

    // Log Idirect Calls inside the function
    ICallGraph[func].insert(icall);
}

void doCtor(llvm::Instruction *icall, std::string &clsname) {
    llvm::CallInst *ic = llvm::dyn_cast<llvm::CallInst>(icall);
    llvm::Function *func = icall->getFunction();

    //(*LOG) << "Ctor : ";
    //ic->dump();
    //(*LOG) << ctor << "\n";
    //(*LOG) << "#args : " << ic->getNumArgOperands() << "\n";
    //assert (ic->getNumArgOperands() > 0);
    //llvm::Value *arg0 = ic->getArgOperand(0);
    //(*LOG) << "XXXX : " << *arg0 << "\n";
    //for (auto &u : arg0->uses()) {
    //    (*LOG) << "Uses : " << *u << "\n";
    //}

    updateThisPtrRegVersion(clsname);
}


const char *stripMcsemaFunctionName(const char *mangled) {
    const char *mangled_name = mangled;

    // Decode McSema Function name:
    //   https://github.com/trailofbits/mcsema/blob/472675ba9cf24f99a3ed9a22182e05876249cba8/mcsema/CFG/CFG.cpp#L64
    if (!strncmp(mangled_name, "sub_", 4)) {
        mangled_name = strstr(mangled_name, "__");
        if (mangled_name) {
            mangled_name += 1;
        } else {
            mangled_name = mangled;
        }
    }

    return mangled_name;
}

std::string demangleSolaris(const char *mangled, bool noret) {
    size_t sz = 1024;
    char *out = (char*)malloc(sz);
    int err = noret ?
        cplus_demangle_noret(mangled, out, sz) :
        cplus_demangle(mangled, out, sz);
    while (err == DEMANGLE_ESPACE) {
        sz <<= 1;
        out = (char*)realloc(out, sz);
        err = noret ?
            cplus_demangle_noret(mangled, out, sz) :
            cplus_demangle(mangled, out, sz);
    }

    // Double check if demangling succeeded
    if (err == DEMANGLE_ENAME)
        return "";

    // hmmmm, Solaris Demangler would sometimes directly return the illegal symbol without raising an error
    // Check if the symbol has actually changed after demangling
    if (!strncmp(out, mangled, strlen(mangled)))
        return "";

    return out;
}

std::string stripFunctionBase(const std::string &fullname) {

    // Skip trailing attributes (e.g. "foo()const")
    // (also handles if fullname.empty())
    int count = fullname.size() - 1;
    while (count && fullname[count] != ')') count--;
    if (!count) return "";

    int count_paren = 0;
    for (; count > 0; count--) {
        if (fullname[count] == '(')    count_paren--;
        if (fullname[count] == ')')    count_paren++;
        if (count_paren)    continue;
        break;
    }

    // Skip template brackets
    if (count && fullname[count - 1] == '>') {
        count--;    // Skip left paren of param list "("
        int count_brack = 0;
        for (; count > 0; count--) {
            if (fullname[count] == '<') count_brack--;
            if (fullname[count] == '>') count_brack++;
            if (count_brack)    continue;
            break;
        }
    }

    // Skip Function name base
    std::string stripped = fullname.substr(0, count);
    auto bindex = stripped.rfind("::");
    if (bindex == std::string::npos)
        return "";

    return stripped.substr(0, bindex);
}

std::string demangle(const char *mangled, int *isCtor) {
    const char *mangled_name = stripMcsemaFunctionName(mangled);

    switch (target_mode) {
    case ARCH_X86:
    {
        //(*LOG) << "Demangle err : " << st << "\n";
        llvm::ItaniumPartialDemangler ipd;
        ipd.partialDemangle(mangled_name);
        std::string df = llvm::demangle(std::string(mangled_name));
        if (ipd.isCtorOrDtor()) {
            //(*LOG) << llvm::demangle(f->getName().str()) << "\n";
            if (df.find("::~") == std::string::npos) {
                //(*LOG) << "Ctor : " << df << "\n";

                *isCtor = 1;

            } else {
                //(*LOG) << "Dtor : " << df << "\n";
                *isCtor = 0;
            }
        }

        return df;
    }
    case ARCH_SPARC:
    {
        std::string fullfn = demangleSolaris(mangled_name, false);
        std::string noretfn = demangleSolaris(mangled_name, true);
        if (!noretfn.empty()
          && fullfn == noretfn  // no return value, could be Ctor or Dtor
          && noretfn.find("::~") == std::string::npos) {  // check not Dtor
            *isCtor = 1;
        }
        return fullfn.empty() ? mangled : fullfn;
    }
    default:
        return "";
    }
}

std::string demangleClass(const char *mangled) {
    const char *mangled_name = stripMcsemaFunctionName(mangled);

    switch (target_mode) {
    case ARCH_X86:
    {
        llvm::ItaniumPartialDemangler ipd;
        if (!ipd.partialDemangle(mangled_name)) {
            const char *ctx = ipd.getFunctionDeclContextName(nullptr, nullptr);
            return ctx ? ctx : "";
        } else {
            if (verbose) {
                (*LOG) << "Cannot Demangle this : " << mangled << "\n";
            }
        }
        break;
    }
    case ARCH_SPARC:
    {
        std::string noretfn = demangleSolaris(mangled_name, true);
        return noretfn.empty() ? "" : stripFunctionBase(noretfn);
    }
    default:
        break;
    }

    return "";
}


// Heuristic check to identify the target function is in McSema Lifted format
bool isFuncTyLifted(llvm::FunctionType *fty) {
    return (fty->getNumParams() == 3 && fty->getParamType(0)->isPointerTy()
            && fty->getParamType(0)->getPointerElementType()->isStructTy()
            && !llvm::dyn_cast<llvm::StructType>(fty->getParamType(0)->getPointerElementType())->isLiteral()    // StructType is not Literal
            && fty->getParamType(0)->getPointerElementType()->getStructName().equals("struct.State"));
}
bool isFuncLifted(llvm::Function *f) {
    return isFuncTyLifted(f->getFunctionType());
}

// LLVM Optimizations would colide instructions into operators,
// recursively resolve the operators and get the `real` ssa variable(instruction)
llvm::Value *resolveLLVMOperator(llvm::Value *val) {
    llvm::Operator *op = llvm::dyn_cast<llvm::Operator>(val);

    // Skip PHI Node
    if (llvm::isa<llvm::PHINode>(val))
        return val;

    while (op) {
        val = op->getOperand(0);
        op = llvm::dyn_cast<llvm::Operator>(val);
    }

    return val;
}

// Create Sym based on given llvm Variable
Sym inferSym(llvm::Value *v, VerTabType &VerTab) {
    Sym s {Sym::None, 0, 0};

    llvm::ConstantInt *cst = llvm::dyn_cast<llvm::ConstantInt>(v);
    if (cst) {
        s.type_ = Sym::Constant;
        s.data_ = cst->getSExtValue();
        s.version_ = VerTab[SymBase(s.type_, s.data_)];
        return s;
    }

    llvm::Argument *arg = llvm::dyn_cast<llvm::Argument>(v);
    if (arg) {
        llvm::Function *f = arg->getParent();

        if (isFuncLifted(f)) {
            switch (arg->getArgNo()) {
            case 1:
                s.type_ = Sym::MemAddr;
                s.data_ = 1;
                s.version_ = VerTab[SymBase(s.type_, s.data_)];
                break;
            case 2:
                s.type_ = Sym::Memory;
                s.data_ = 2;
                s.version_ = VerTab[SymBase(s.type_, s.data_)];
                break;
            default:
                (*LOG) << "[debug] inferSym in " << f->getName() << " : " << *v << "\n";
                assert(false && "Expected the 2nd (PC) arg of lifted function");
            }
        } else {
            s.type_ = Sym::FuncArg;
            s.data_ = arg->getArgNo();
            s.version_ = VerTab[SymBase(s.type_, s.data_)];
        }

        return s;
    }

    // Note: this is SLOW!! It's probably safe to just break the dataflow here,
    //       as we will resolve all the indirect calls again after everything
    //
    //llvm::Operator *op = llvm::dyn_cast<llvm::Operator>(v);
    //if (op) {
    //    s.type_ = Sym::Variable;
    //    s.data_ = (size_t)resolveLLVMOperator(op);
    //    s.version_ = VerTab[SymBase(s.type_, s.data_)];
    //    return s;
    //}

    // LLVM Variable
    s.type_ = Sym::Variable;
    s.data_ = (size_t)v;
    s.version_ = VerTab[SymBase(s.type_, s.data_)];
    return s;
}

// list all struct types from bc
void collectStructTy() {
    auto sttypes = module->getIdentifiedStructTypes();
    for (llvm::StructType *st : sttypes) {
        llvm::StringRef stname = st->getName();
        if (stname.endswith("_type") || stname.contains("_type.")) {
            stname = stname.take_front(stname.find("_type"));
        }
        int dummy;
        std::string dn = demangle(stname.str().c_str(), &dummy);

        st->dump();
        (*LOG) << "DEBUG : " << dn << "\n";

        ObjTypeMap[dn] = st;
    }
}

// Choose whether or not this function is an entry point
bool FuncIsEntryPoint(std::string&& fname)
{
    //if (strcmp(fname.c_str(), "sub_4147c0__ZNSt12domain_errorC2EPKc") == 0) return true; else return false; // Debug

  // Find entry points
  std::size_t pos1 = fname.find("16RequestProcessor");
  if (pos1 != std::string::npos)
{
  std::size_t pos2 = fname.find("process", pos1 + 18);
  if (pos2 != std::string::npos)
    {
      (*LOG) << "Found entry point : " << fname << "\n";
      return (true);
    }
}
  
  // also set make as entry point
  pos1 = fname.find("main");
  if (pos1 != std::string::npos)
{
  (*LOG) << "Found entry point : " << fname << "\n";
  return (true);
}

  // also add Modeling stubs for request context methods
  pos1 = fname.find("RequestContextFake");
  if (pos1 != std::string::npos)
{
  (*LOG) << "Found entry point : " << fname << "\n";
  return (true);
}

  // Also add allocator stubs
  pos1 = fname.find("TrampolineAllocator");
  if (pos1 != std::string::npos)
{
  (*LOG) << "Found entry point : " << fname << "\n";
  return (true);
}

  // Also add deallocator stubs
  pos1 = fname.find("TrampolineDeallocator");
  if (pos1 != std::string::npos)
{
  (*LOG) << "Found entry point : " << fname << "\n";
  return (true);
}
  
  // This function is not an entry point
  return (false);
}


// Copy the oldSymMap to newSymMap, replacing all FuncArg symbols with args from Call instruction
Sym interpretSymbol(const Sym &sym, llvm::CallInst *inst, VerTabType &vertab, VerTabType &VerTab) {
    Sym s = sym;
    switch (s.type_) {
    case Sym::FuncArg:
        s = inferSym(inst->getArgOperand(s.data_), VerTab);
        break;
    case Sym::Return:
        // Shortcut for :  s = inferSym(inst);
        s.type_ = Sym::Variable;
        s.data_ = (size_t)inst;
        s.version_ = VerTab[SymBase(s.type_, s.data_)];
        break;
    case Sym::None: // Skip Sym::None
        break;
    default:
        // Rebase (Update) Sym Version For Internal Symbols
        //(*LOG) << "Debug Interpret Sym : " << s.type_ << " , " << (void*)s.data_ << " , " << s.version_;
        s.version_ += VerTab[SymBase(s.type_, s.data_)];
        //(*LOG) << " -> " << s.version_;
        size_t vn = vertab[SymBase(s.type_, s.data_)];
        //(*LOG) << " , while local ver# " << vn << "\n";
        vertab[SymBase(s.type_, s.data_)] = vn > s.version_ ? vn : s.version_;
        break;
    }

    return s;
}
SymValue interpretSymbolValue(const SymValue &symval, llvm::CallInst *inst, VerTabType &vertab, VerTabType &VerTab) {
    SymValue sv = symval;
    sv.data1_ = interpretSymbol(sv.data1_, inst, vertab, VerTab);
    sv.data2_ = interpretSymbol(sv.data2_, inst, vertab, VerTab);
    //(*LOG) << "debug " << sv.op_<< " : " << symval.op_ <<" : extra data : " << sv.nextra_ <<" : "<<symval.nextra_ <<"\n";
    for (auto i = 0; i < sv.nextra_; i++) {
        //(*LOG) << "Before Interpret Symbol Value: key " << sv.extra_data_[i].type_ << " , " << (void*)sv.extra_data_[i].data_<<" , " << sv.extra_data_[i].version_ <<"\n";
        sv.extra_data_[i] = interpretSymbol(sv.extra_data_[i], inst, vertab, VerTab);
        //(*LOG) << "After Interpret Symbol Value: key " << sv.extra_data_[i].type_ << " , " << (void*)sv.extra_data_[i].data_<<" , " << sv.extra_data_[i].version_ <<"\n";
    }
    return sv;
}
void copySymMap(SymTab &newSymMap, const SymTab &oldSymMap, VerTabType &VerTab, llvm::Instruction *inst_call) {
    llvm::CallInst *call = llvm::dyn_cast<llvm::CallInst>(inst_call);
    //(*LOG) << "DEBUG : " << inst_call->getFunction()->getName() << " : " << *inst_call << " : " << oldSymMap.size() <<"\n";
    VerTabType CurVerTab;
    for (auto &e: oldSymMap) {

        //(*LOG) << "check var : " << e.first.type_ << " : " << (void*)e.first.data_ << "\n";
        Sym s_zero {e.first.type_, e.first.data_, 0};
        assert (oldSymMap.find(s_zero) != oldSymMap.end()); // All syms version should start from 0 in the SymMap of every function

        Sym s = interpretSymbol(e.first, call, CurVerTab, VerTab);
        //(*LOG) << "Append key : " << s.type_ << " , " << (void*)s.data_ << " , " << s.version_ << "\n";

        for (auto &v : e.second) {
            newSymMap[s].insert(
                    interpretSymbolValue(v, call, CurVerTab, VerTab));
        }
    }

    // Update Global Version Table
    for (auto &e : CurVerTab) {
        //(*LOG) << e.second << " - " << VerTab[e.first] << " - " << e.first.type_ << " - " << (void*)e.first.data_ << "\n";
        assert (e.second >= VerTab[e.first]);
        VerTab[e.first] = e.second;
    }
}


// Replace the copySymMap with maintaing a flow-insensitive map per function
void enterFunc(SymTab &callerSymMap, SymTab &calleeSymMap, llvm::Instruction *inst_call, llvm::Function *callee) {
    llvm::CallInst *call = llvm::dyn_cast<llvm::CallInst>(inst_call);
    llvm::Function *caller = inst_call->getFunction();

    // Process Args
    if (isFuncLifted(callee)) { // For McSema Lifted function, only propogate the 2nd, 3rd arg
        Sym spc {Sym::MemAddr, 1, 0};    // should be version 0
        Sym smem {Sym::Memory, 2, 0};
        Sym srpc = inferSym(call->getArgOperand(1), FuncVerTab[caller]);
        Sym srmem = inferSym(call->getArgOperand(2), FuncVerTab[caller]);
        SymValue svrpc {srpc, SymValue::None, g_s_empty, 0, 0};
        SymValue svrmem {srmem, SymValue::None, g_s_empty, 0, 0};

        calleeSymMap[spc].insert(svrpc);
        calleeSymMap[smem].insert(svrmem);

        SymLookup[srpc] = caller;
        SymLookup[srmem] = caller;

    } else {    // Common(?) Function Call, propogate each arg
        Sym sarg {Sym::FuncArg, 0/*placeholder*/, 0/*version 0*/};
        for (auto i = 0; i < call->getNumArgOperands(); i++) {
            sarg.data_ = i;
            Sym sr = inferSym(call->getArgOperand(i), FuncVerTab[caller]);
            SymValue svr {sr, SymValue::None, g_s_empty, 0, 0};

            calleeSymMap[sarg].insert(svr);

            SymLookup[sr] = caller;
        }
    }

    // Process Ret
    Sym sret {Sym::Return, (size_t)callee, 0};
    if (!callee->getReturnType()->isVoidTy()) {
        SymValue svret {sret, SymValue::None, g_s_empty, 0, 0};
        Sym sc = inferSym(call, FuncVerTab[caller]);
        // Remove this assert - the return value of call could be used before the callinst is seen, in the loop back basicblock
        //assert (callerSymMap.find(sc) == callerSymMap.end());   // -Should be unique thanks to SSA-
        callerSymMap[sc].insert(svret);

        SymLookup[sret] = callee;
    }
}

void doPerFunction(llvm::Function *func, SymTab &SymMap, VerTabType &VerTab) {

    //(*LOG) << "[debug] do per function: " << func->getName() << "\n";

    // Check If we have already processed this function
    if (FuncState.find(func) != FuncState.end())
        return;

    // Update Function State
    FuncState[func] = SEEN;

    auto inst_iter_end = llvm::inst_end(func);
    for (llvm::inst_iterator inst_iter = llvm::inst_begin(func); inst_iter != inst_iter_end; inst_iter++) {

        llvm::Instruction *inst = &(*inst_iter);

        unsigned Op = inst->getOpcode();
        switch (Op) {
        case llvm::Instruction::Call:
        {
            //(*LOG) << "[debug] call inst at " << func->getName() << " : " << *inst << "\n";

            llvm::CallSite cs (inst);
            llvm::Value *callval = resolveLLVMOperator(cs.getCalledValue());
            if (callval) {
                llvm::Constant *cst = llvm::dyn_cast<llvm::Constant>(callval);
                if (cst) {
                    llvm::GlobalValue *gv = llvm::dyn_cast<llvm::GlobalValue>(cst);
                    if (gv) {
                        llvm::Function *f = llvm::dyn_cast<llvm::Function>(gv);
                        //(*LOG) << "Direct Call: " << f->getName() << "\n";

                        // In compatible with McSema LLVM 6 update - indirect calls are handled with __mcsema
                        if (f->getName().startswith("__mcsema_detach_call_value")) {    // check with "startswith" to avoid llvm aliasing
                            doIndirectCall(inst, false, f);
                            break;
                        }

                        if (isInternalFunction(f->getName().str())) // Skip McSema Internal Functions
                            break;

                        int isCtor = 0;
                        std::string fname = demangle(f->getName().data(), &isCtor);

                        // Check Cutoff
                        if (use_cutoff) {
                            bool found_cutoff = false;
                            for (auto cf = Cutoffs.begin(); !found_cutoff && cf != Cutoffs.end(); cf++) {
                                if (fname.find(*cf) != std::string::npos) {
                                    found_cutoff = true;
                                }
                            }
                            if (found_cutoff)
                                break;
                        }

                        if (isCtor) {
                            std::string classname = demangleClass(f->getName().data());
                            assert (!classname.empty());
                            //(*LOG) << "Ctor " << *inst << "\n";
                            doCtor(inst, classname);

                            // Log Ctor Called Inside the function
                            CtorCallGraph[func].insert(f);
                        } else {
                            // Log Direct Called Function inside the function
                            CallGraph[func].insert(f);
                        }

                        // Do Function Pass thro, should be enough by just checking FuncState
                        if (FuncState.find(f) != FuncState.end()) {
                            //(*LOG) << "debug function " << f->getName() << " not processed\n";
                            if (FuncState[f] == SEEN)   // Likely recursive calls, Just break the dataflow
                                break;
                        } else {
                            //(*LOG) << "debug function " << f->getName() << " processing\n";
                            // Haven't Analyzed this function yet, Do it Now
                            doPerFunction(f, FuncPassThro[f], FuncVerTab[f]);
                        }
                        // -Copy the SymMap && Change all the Sym(FuncArg) to Call Args-
                        //copySymMap(SymMap, FuncPassThro[f], FuncVerTab[func], inst);
                        // Update the callee/caller SymMap to complete inter-function dataflow
                        enterFunc(SymMap, FuncPassThro[f], inst, f);

                        break;
                    }
                }
            } // Else, might be an indirecrt call

            //(*LOG) << "ICall in " << func->getName() << " : " << *inst << "\n";
            doIndirectCall(inst);

            break;
        }
        case llvm::Instruction::GetElementPtr:
        {
            llvm::GetElementPtrInst *gep = llvm::dyn_cast<llvm::GetElementPtrInst>(inst);

            // Ughhhhh GEP is complicated, goes to AuxGEP for now
            if (!gep->getSourceElementType()->isStructTy()) {

                (*LOG) << "[debug] non-struct gep inst in " << func->getName() << " : " << *gep << "\n";
                //assert (false && "GEP base is non struct");

                SymBase symb(Sym::Variable, (size_t)inst);
                Sym sl {Sym::Variable, (size_t)inst, VerTab[symb]};
                SymValue svr {sl, SymValue::AuxGEP, g_s_empty, 0, 0};

                SymMap[sl].insert(svr);

                SymLookup[sl] = func;
                break;
            }

            // Filter out Literal Struct Type
            if (llvm::dyn_cast<llvm::StructType>(gep->getSourceElementType())->isLiteral()) {

                (*LOG) << "[debug] literal struct gep inst in " << func->getName() << " : " << *gep << "\n";

                SymBase symb(Sym::Variable, (size_t)inst);
                Sym sl {Sym::Variable, (size_t)inst, VerTab[symb]};
                SymValue svr {sl, SymValue::AuxGEP, g_s_empty, 0, 0};

                SymMap[sl].insert(svr);

                SymLookup[sl] = func;
                break;
            }

            // Struct-based GEP
            llvm::StringRef gepbasename = gep->getSourceElementType()->getStructName();
            if (gepbasename.startswith("struct.State")) {  // GEP to Get Register should have "struct.State *%0" as the base

                SymBase symbl(Sym::Variable, (size_t)inst);
                Sym sl {Sym::Variable, (size_t)inst, VerTab[symbl]};

                // Only Care about GPR registers
                if (!checkGepGPR(gep))
                    break;

                updateRegDefSet(gep, sl, SymMap, func);

                SymLookup[sl] = func;

            } else if (gepbasename.startswith("union.anon") || gepbasename.startswith("struct.anon")) { // Access Part of the register

                Sym sl {Sym::Variable, (size_t)inst, VerTab[SymBase(Sym::Variable, (size_t)inst)]};

                handleGepUnionAnon(gep, func, sl, SymMap, VerTab);

                SymLookup[sl] = func;

            } else {    // Complicated GEP instruction goes to AuxGEP

                (*LOG) << "[debug] unknown struct gep inst in " << func->getName() << " : " << *gep << "\n";
                //assert(false && "Unknown GEP Base Type Name");

                Sym sl {Sym::Variable, (size_t)inst, VerTab[SymBase(Sym::Variable, (size_t)inst)]};
                SymValue svr {sl, SymValue::AuxGEP, g_s_empty, 0, 0};

                //(*LOG) << "Debug GEP SymMap.size(): " << SymMap.size() << " ,SymMap[sl].size() : " << SymMap[sl].size() << "\n";
                //(*LOG) << sl.type_ << " , " << (void*)sl.data_ << " , " << sl.version_  << " : " << (SymMap.find(sl) == SymMap.end()) <<"\n";
                SymMap[sl].insert(svr);

                SymLookup[sl] = func;
            }

            break;
        }
        case llvm::Instruction::PtrToInt:
        case llvm::Instruction::IntToPtr:
        case llvm::Instruction::BitCast:
        {
            //(*LOG) << "[debug] cast inst: " << *inst << "\n";

            Sym sl {Sym::Variable, (size_t)inst, VerTab[SymBase(Sym::Variable, (size_t)inst)]};
            Sym sr = inferSym(inst->getOperand(0), VerTab);
            SymValue svr {sr, SymValue::Cast, g_s_empty, 0, 0};

            //(*LOG) << "Debug Cast SymMap.size(): " << SymMap.size() << " ,SymMap[sl].size() : " << SymMap[sl].size() << "\n";
            //(*LOG) << sl.type_ << " , " << (void*)sl.data_ << " , " << sl.version_  << " : " << (SymMap.find(sl) == SymMap.end()) <<"\n";
            SymMap[sl].insert(svr);

            SymLookup[sl] = func;
            SymLookup[sr] = func;
            break;
        }
        case llvm::Instruction::Load:
        {
            //(*LOG) << "[debug] load inst: " << *inst << "\n";

            Sym sl {Sym::Variable, (size_t)inst, VerTab[SymBase(Sym::Variable, (size_t)inst)]};
            Sym sr = inferSym(inst->getOperand(0), VerTab);
            SymValue svr {sr, SymValue::Deref, g_s_empty, 0, 0};

            //(*LOG) << "Debug Load SymMap.size(): " << SymMap.size() << " ,SymMap[sl].size() : " << SymMap[sl].size() << "\n";
            //(*LOG) << sl.type_ << " , " << (void*)sl.data_ << " , " << sl.version_  << " : " << (SymMap.find(sl) == SymMap.end()) <<"\n";
            SymMap[sl].insert(svr);

            SymLookup[sl] = func;
            SymLookup[sr] = func;
            break;
        }
        case llvm::Instruction::Store:
        {
            //(*LOG) << "[debug] store inst: " << *inst << "\n";

            Sym sl = inferSym(inst->getOperand(1), VerTab); // addr
            Sym sr = inferSym(inst->getOperand(0), VerTab); // val
            SymValue svr {sr, SymValue::Ref, g_s_empty, 0, 0};
            // Update Global Version Table if necessary
            if (SymMap.find(sl) != SymMap.end()
              || sl.type_ == Sym::FuncArg) {    // Shortcut Store to FuncArg, as version 0 has special usage to pass-in params
                sl.version_++;
                VerTab[SymBase(sl.type_, sl.data_)]++;
            }

            //(*LOG) << "Debug Store SymMap.size(): " << SymMap.size() << " ,SymMap[sl].size() : " << SymMap[sl].size() << "\n";
            //(*LOG) << sl.type_ << " , " << (void*)sl.data_ << " , " << sl.version_  << " : " << (SymMap.find(sl) == SymMap.end()) <<"\n";
            SymMap[sl].insert(svr);

            // Always propogate Version 0
            if (sl.version_) {
                Sym sz {sl.type_, sl.data_, 0};
                SymValue svz {sz, SymValue::None, g_s_empty, 0, 0};
                SymMap[sl].insert(svz);
            }

            SymLookup[sl] = func;
            SymLookup[sr] = func;
            break;
        }
        case llvm::Instruction::Add:
        {
            //(*LOG) << "[debug] add inst: " << *inst << "\n";

            Sym sl {Sym::Variable, (size_t)inst, VerTab[SymBase(Sym::Variable, (size_t)inst)]};
            Sym sr1 = inferSym(inst->getOperand(0), VerTab);
            Sym sr2 = inferSym(inst->getOperand(1), VerTab);
            SymValue svr {sr1, SymValue::Add, sr2, 0, 0};

            //(*LOG) << "Debug Add SymMap.size(): " << SymMap.size() << " ,SymMap[sl].size() : " << SymMap[sl].size() << "\n";
            //(*LOG) << sl.type_ << " , " << (void*)sl.data_ << " , " << sl.version_  << " : " << (SymMap.find(sl) == SymMap.end()) <<"\n";
            SymMap[sl].insert(svr);

            SymLookup[sl] = func;
            SymLookup[sr1] = func;
            SymLookup[sr2] = func;
            break;
        }
        case llvm::Instruction::Ret:
        {
            //(*LOG) << "[debug] ret at " << func->getName() << " : " <<*inst<<"\n";

            llvm::ReturnInst *ret = llvm::dyn_cast<llvm::ReturnInst>(inst);

            if (ret->getNumOperands()) {
                llvm::Value *retval = ret->getOperand(0);

                // Make sure return type is NOT struct.Memory*
                llvm::Type *retty = retval->getType();
                if (retty->isPointerTy() && retty->getPointerElementType()->isStructTy()
                  && !llvm::dyn_cast<llvm::StructType>(retty->getPointerElementType())->isLiteral() // Not Literal Struct
                  && retty->getPointerElementType()->getStructName().equals("struct.Memory"))
                    break;

                Sym sl {Sym::Return, (size_t)func/*fptr as ident*/, 0/*Dont Care*/};
                Sym sr = inferSym(retval, VerTab);
                SymValue svr {sr, SymValue::None, g_s_empty, 0, 0};   // Or use SymValue::Cast?

                SymMap[sl].insert(svr);

                SymLookup[sl] = func;
                SymLookup[sr] = func;
            }
            break;
        }
        case llvm::Instruction::PHI:
        {
            //(*LOG) << "[debug] phi node at " << func->getName() << " : " << *inst <<"\n";

            llvm::PHINode *phi = llvm::dyn_cast<llvm::PHINode>(inst);

            unsigned nin = phi->getNumIncomingValues();
            Sym sl {Sym::Variable, (size_t)inst, VerTab[SymBase(Sym::Variable, (size_t)inst)]};

            if (nin >= 2) {
                Sym sr1 = inferSym(phi->getIncomingValue(0), VerTab);
                Sym sr2 = inferSym(phi->getIncomingValue(1), VerTab);
                if (nin == 2) {
                    SymValue svr = {sr1, SymValue::Phi, sr2, 0, 0};
                    SymMap[sl].insert(svr);
                } else {
                    Sym *extra = new Sym[nin-2];
                    SymValue svr = {sr1, SymValue::Phi, sr2, nin-2, extra};
                    for (unsigned ii = 2, di = 0; ii < nin; ii++, di++) {
                        extra[di] = inferSym(phi->getIncomingValue(ii), VerTab);

                        SymLookup[extra[di]] = func;
                    }
                    SymMap[sl].insert(svr);
                }

                SymLookup[sl] = func;
                SymLookup[sr1] = func;
                SymLookup[sr2] = func;
            } else if (nin == 1) {  // It's not actually doing a PHI node thing.. Maybe should use SymValue::Cast|None?
                Sym sr1 = inferSym(phi->getIncomingValue(0), VerTab);
                SymValue svr = {sr1, SymValue::Phi, g_s_empty, 0, 0};

                SymMap[sl].insert(svr);

                SymLookup[sl] = func;
                SymLookup[sr1] = func;
            } else {
                (*LOG) << "[debug] wrong phi in func : " << func->getName() << " <<< " << *inst << "\n";
                assert (false && "No Incoming Val for PHI!");
            }
            break;
        }
        default:
            break;
        }
    }

    //(*LOG) << "[debug] finish func " << func->getName() << " : " << FuncPassThro[func].size() <<"\n";

    // Update Function State
    FuncState[func] = DONE;
}

int main(int argc, char **argv) {

    assert (llvm::cl::ParseCommandLineOptions(argc, argv));

    if (target_arch == "x86") {
        target_mode = ARCH_X86;
    } else if (target_arch == "sparc") {
        target_mode = ARCH_SPARC;
    } else {
        assert (false && "Unknown Target Arch");
    }

    std::error_code ec;
    if (!log_file.empty()) {
#if LLVM_VERSION_MAJOR == 8
        static llvm::raw_fd_ostream logfs_(log_file, ec, llvm::sys::fs::FA_Read | llvm::sys::fs::FA_Write);
#elif LLVM_VERSION_MAJOR == 6
        static llvm::raw_fd_ostream logfs_(log_file, ec, llvm::sys::fs::F_Excl | llvm::sys::fs::F_RW);
#endif
        LOG = &logfs_;
    }

    context_ = llvm::unwrap(LLVMGetGlobalContext());

    llvm::SMDiagnostic err;
    module = llvm::parseIRFile(input_bc, err, *context_);

    total_func = module->size();
    (*LOG) << "Total Funcs " << total_func << "\n";

    // First Pass : Generate Dataflow Table && inference indirect call class type on-the-fly
    // runOnModule
    //collectStructTy();

    for (llvm::Function &func : *module) {

        func_count++;

        if (func_count % 100 == 0) {
            llvm::outs() << "stats : " << func_count << " done out of " << total_func << "\n";
        }

        if (!FuncIsEntryPoint(func.getName().str()))
            continue;

        // Use a fresh new SymMap & Version Table for every entry point function
        doPerFunction(&func, FuncPassThro[&func], FuncVerTab[&func]);

    }



    // doFinalize
    dumpICallStat();

    // Second Pass : Resolve the indirect call one more time after everything
    // Some indirect calls might not be able to resolve at the time they are processed
    // Do one more final round && try to resolve them all
    for (auto &e : ICallObj) {
        llvm::CallInst *ic = llvm::dyn_cast<llvm::CallInst>(e.first);
        assert (ic);
        if (isIndirectCall(ic)) {
            doIndirectCall(ic, true/*use all versions of regs*/);
        } else {
            doIndirectCall(ic, true, (llvm::Function*)0xdeadbeef/*placeholder for not being null, won't be used anyway*/);
        }
    }
    dumpICallStat();

    // Print Possible PLT indirect calls
    //(*LOG) << "Identified " << PltICall.size() << " PLT Calls:\n";
    //for (auto &e : PltICall) {
    //    (*LOG) << "  " << e->getFunction()->getName() << " inst: " << *e << "\n";
    //}


    // Third Pass : Identify All functions related to the resolved class names
    std::set<std::pair<std::string, bool/*hasAddressTaken*/>> class_funcs;
    std::set<std::string> valid_vfuncs;
    std::set<std::string> non_callsite_funcs;
    std::set<std::string> resolved_ctor;
    std::set<std::string> direct_callees;
    // Collect resolved class names
    for (auto &e : ICallObj) {
        for (auto &c : e.second) {
            resolved_ctor.insert(c.first);
        }
    }
    // Slow: Collect all Callees to double verify function pointers
    for (llvm::Function &func : *module) {
        auto inst_iter_end = llvm::inst_end(func);
        for (llvm::inst_iterator inst_iter = llvm::inst_begin(func); inst_iter != inst_iter_end; inst_iter++) {
            llvm::Instruction *inst = &(*inst_iter);
            if (inst->getOpcode() == llvm::Instruction::Call) {
                llvm::CallSite cs (inst);
                llvm::Value *callval = cs.getCalledValue();
                if (llvm::isa<llvm::GlobalValue>(callval)
                  && llvm::isa<llvm::Function>(callval)) {
                    llvm::Function *f = llvm::dyn_cast<llvm::Function>(callval);
                    direct_callees.insert(f->getName().str());
                }
            }
        }
    }
    // Resolve Virtual Functions
    for (llvm::Function &func : *module) {
        std::string classctx = demangleClass(func.getName().data());
        if (!classctx.empty()) {
            //(*LOG) << " : " << classctx << "\n";
            if (resolved_ctor.find(classctx) != resolved_ctor.end()) {
                std::string fnstr = func.getName().str();
                class_funcs.insert(std::make_pair(fnstr, func.hasAddressTaken()));
                if (func.hasAddressTaken()) {   // Check hasAddressTaken to further filter out virtual functions
                    valid_vfuncs.insert(fnstr);
                } else if (direct_callees.find(fnstr) == direct_callees.end()) { // Double Check if function has any callsites
                    non_callsite_funcs.insert(fnstr);
                }
            }
        } else {    // Skip this, Somehow duplicated named functions
            //(*LOG) << " : Nooooooon\n";
        }
    }
    (*LOG) << "Virtual Functions " << valid_vfuncs.size() << " + Non-CallSite Funcs : " << non_callsite_funcs.size() << " / " << class_funcs.size() << " : \n";
    //for (auto &e : class_funcs) {
    //    (*LOG) << e.first << " hasAddressTaken : " << e.second << "\n";
    //}


    // Forth Pass: Minimize bc file
    std::set<std::string> vfuncs;
    vfuncs.insert(valid_vfuncs.begin(), valid_vfuncs.end());
    vfuncs.insert(non_callsite_funcs.begin(), non_callsite_funcs.end());
    calledfunccount::CalledFuncCount cfc;
    cfc.runOnModule(*module, vfuncs);
    cfc.doFinalization(*module);


    if (verbose) {
        for (auto &e : valid_vfuncs) {
            (*LOG) << e << "\n";
        }
        (*LOG) << "Non-CallSite\n";
        for (auto &e : non_callsite_funcs) {
            (*LOG) << e << "\n";
        }
    }


    // Output with bc
    if (!output_bc.empty()) {
        // Add Class Info into Indirect Call Metadata
        //for (auto &e : ICallObj) {
        //    std::vector<llvm::Metadata*> tup;
        //    for (auto &cname : e.second) {
        //        tup.emplace_back(llvm::MDString::get(*context_, cname.first));
        //    }
        //    e.first->setMetadata("h2h:ctor",
        //            llvm::MDNode::get(*context_, tup));
        //}

        // Output new bc file
#if LLVM_VERSION_MAJOR == 8
        llvm::raw_fd_ostream fileout(output_bc, ec, llvm::sys::fs::FA_Read | llvm::sys::fs::FA_Write);
        llvm::WriteBitcodeToFile(*module, fileout);
#elif LLVM_VERSION_MAJOR == 6
        llvm::raw_fd_ostream fileout(output_bc, ec, llvm::sys::fs::F_Excl | llvm::sys::fs::F_RW);
        llvm::WriteBitcodeToFile(module.get(), fileout);
#endif
    }

    return 0;
}
