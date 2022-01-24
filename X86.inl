
#define REG_X86(X) ((X86_REG)(((int)(X))/2))
#define ISREG_X86(X) ((int)(X) >= X86_RAX && (int)(X) < X86_REG_END)
typedef enum {
    X86_RAX = 0,
    X86_RBX,
    X86_RCX,
    X86_RDX,
    X86_RSI,
    X86_RDI,
    X86_RSP,
    X86_RBP,
    X86_R8,
    X86_R9,
    X86_R10,
    X86_R11,
    X86_R12,
    X86_R13,
    X86_R14,
    X86_R15,
    X86_RIP,
    X86_REG_END,
} X86_REG;
//Sym regs[X86_REG_END];

std::map<X86_REG, size_t> GRegVerTab_X86;   // Global Versioning for Registers


// bootstrap the dataflow analysis from the register
void initDataflowFromReg_X86(std::set<Sym> &toResolve, std::set<std::pair<std::string, size_t>> &result) {
    // Lookup the register
    Sym srcx {Sym::Register, X86_RCX, GRegVerTab_X86[X86_RCX]};
    Sym srdi {Sym::Register, X86_RDI, GRegVerTab_X86[X86_RDI]};

    result.insert(std::make_pair(RegObj[srcx], 0));
    result.insert(std::make_pair(RegObj[srdi], 0));

    toResolve.insert(RegUses[srcx].begin(), RegUses[srcx].end());
    toResolve.insert(RegUses[srdi].begin(), RegUses[srdi].end());
}

// Check the Sym is Register && is possibly been used as This Pointer
bool checkRegThisPtr_X86(Sym &s) {
    return (s.type_ == Sym::Register && (s.data_ == X86_RCX || s.data_ == X86_RDI));
}

// update the This Pointer register with Class Name, (when Ctor is seen)
void updateThisPtrRegVersion_X86(std::string cls) {
    Sym srcx {Sym::Register, X86_RCX, GRegVerTab_X86[X86_RCX]};
    Sym srdi {Sym::Register, X86_RDI, GRegVerTab_X86[X86_RDI]};

    if (RegObj.find(srcx) != RegObj.end()) {
        GRegVerTab_X86[X86_RCX]++;
        srcx.version_++;
    }
    if (RegObj.find(srdi) != RegObj.end()) {
        GRegVerTab_X86[X86_RDI]++;
        srdi.version_++;
    }

    RegObj[srcx] = cls;
    RegObj[srdi] = cls;
}

// Decoding the GEP Inst, check GPR register set dereference
bool checkGepGPR_X86(llvm::GetElementPtrInst *gep) {
    llvm::ConstantInt *cpufield = llvm::dyn_cast<llvm::ConstantInt>(gep->getOperand(2));
    return cpufield->equalsInt(6);
}

// Decoding the GEP Inst, update Def-Set table for register access
void updateRegDefSet_X86(llvm::GetElementPtrInst *gep, Sym &sl, SymTab &SymMap, llvm::Function *func) {

    llvm::ConstantInt *regno = llvm::dyn_cast<llvm::ConstantInt>(gep->getOperand(3));
    X86_REG reg = REG_X86(regno->getSExtValue());
    assert (ISREG_X86(reg));

    //(*LOG) << "GEP reg " << reg << " , " << *gep << "\n";

    // Do Global Register Versioning ONLY for possible class pointers - RCX/RDI
    if (reg == X86_RCX || reg == X86_RDI) {
        Sym sr {Sym::Register, reg, GRegVerTab_X86[reg]};
        SymValue svr {sr, SymValue::Cast, g_s_empty, 0, 0};
        if (gep->getNumIndices() == 5) {
            svr.op_ = SymValue::Deref;
        }

        SymMap[sl].insert(svr);
        RegUses[sr].insert(sl);
    }

    Sym fixed_sr {Sym::Register, reg, (size_t)func/*NOT version_, to differ reg from different functions*/};
    SymValue fixed_svr {fixed_sr, SymValue::Cast, g_s_empty, 0, 0};
    if (gep->getNumIndices() == 5) {
        fixed_svr.op_ = SymValue::Deref;
    }

    //(*LOG) << "Debug GEP SymMap.size(): " << SymMap.size() << " ,SymMap[sl].size() : " << SymMap[sl].size() << "\n";
    //(*LOG) << sl.type_ << " , " << (void*)sl.data_ << " , " << sl.version_  << " : " << (SymMap.find(sl) == SymMap.end()) <<"\n";
    //(*LOG) << "Debug fixed register " << fixed_sr.type_ << " , " << (void*)fixed_sr.data_ << " , " << (void*)fixed_sr.version_ << "\n";
    SymMap[sl].insert(fixed_svr);

    // Create Register entry in the per Function SymMap - to handle variable aliasing related to load/store
    SymValue use {sl, SymValue::Cast, g_s_empty, 0, 0};
    SymMap[fixed_sr].insert(use);

    SymLookup[fixed_sr] = func;
}

// Decoding GEP Inst, handle union.anon pointer dereference
void handleGepUnionAnon_X86(llvm::GetElementPtrInst *gep, llvm::Function *func, Sym &sl, SymTab &SymMap, VerTabType &VerTab) {

    assert(gep->getNumIndices() == 2);

    llvm::Value *ptr =  gep->getPointerOperand();
    Sym sr {Sym::Variable, (size_t)ptr, VerTab[SymBase(Sym::Variable, (size_t)ptr)]};
    SymValue svr {sr, SymValue::Deref, g_s_empty, 0, 0};

    //(*LOG) << "Debug GEP SymMap.size(): " << SymMap.size() << " ,SymMap[sl].size() : " << SymMap[sl].size() << "\n";
    //(*LOG) << sl.type_ << " , " << (void*)sl.data_ << " , " << sl.version_  << " : " << (SymMap.find(sl) == SymMap.end()) <<"\n";
    SymMap[sl].insert(svr);

    SymLookup[sr] = func;
}
