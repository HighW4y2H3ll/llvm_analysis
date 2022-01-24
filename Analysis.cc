
#include <map>
#include <set>


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
static llvm::cl::opt<std::string> log_file ("l", llvm::cl::desc("log file"), llvm::cl::init(""));
static llvm::cl::opt<bool> verbose ("v", llvm::cl::desc("verbose output"));

llvm::raw_ostream *LOG = &llvm::errs();

size_t total_func;
size_t func_count = 0;

llvm::LLVMContext *context_ = nullptr;
std::unique_ptr<llvm::Module> module;

typedef enum {
    SEEN,   // Seen and is undergoing analyzing
    DONE,   // Done analyzing
} FunctionState;

std::map<llvm::Function*, FunctionState> FuncState;


void doPerFunction(llvm::Function *func) {

    //(*LOG) << "[debug] do per function: " << func->getName() << "\n";

    // Check If we have already processed this function
    if (FuncState.find(func) != FuncState.end())
        return;

    // Update Function State
    FuncState[func] = SEEN;

    (*LOG) << "[debug] finish func " << func->getName() <<"\n";

    // Update Function State
    FuncState[func] = DONE;
}

int main(int argc, char **argv) {

    assert (llvm::cl::ParseCommandLineOptions(argc, argv));

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

    for (llvm::Function &func : *module) {

        func_count++;

        if (func_count % 100 == 0) {
            llvm::outs() << "stats : " << func_count << " done out of " << total_func << "\n";
        }

        doPerFunction(&func);

    }

    return 0;
}
