
#define REG_SPARC(X) ((SPARC_REG)(((int)(X))/2))
#define ISREG_SPARC(X) ((int)(X) >= SPARC_I0 && (int)(X) < SPARC_REG_END)
typedef enum {
    SPARC_I0 = 0,
    SPARC_I1,
    SPARC_I2,
    SPARC_I3,
    SPARC_I4,
    SPARC_I5,
    SPARC_I6,
    SPARC_I7,
    SPARC_L0,
    SPARC_L1,
    SPARC_L2,
    SPARC_L3,
    SPARC_L4,
    SPARC_L5,
    SPARC_L6,
    SPARC_L7,
    SPARC_O0,
    SPARC_O1,
    SPARC_O2,
    SPARC_O3,
    SPARC_O4,
    SPARC_O5,
    SPARC_O6,
    SPARC_O7,
    SPARC_G0,
    SPARC_G1,
    SPARC_G2,
    SPARC_G3,
    SPARC_G4,
    SPARC_G5,
    SPARC_G6,
    SPARC_G7,
    SPARC_REG_END,
} SPARC_REG;

std::map<SPARC_REG, size_t> GRegVerTab_SPARC;   // Global Versioning for Registers


// bootstrap the dataflow analysis from the register
void initDataflowFromReg_SPARC(std::set<Sym> &toResolve, std::set<std::pair<std::string, size_t>> &result) {
    // Lookup the register
    Sym so0 {Sym::Register, SPARC_O0, GRegVerTab_SPARC[SPARC_O0]};

    result.insert(std::make_pair(RegObj[so0], 0));

    toResolve.insert(RegUses[so0].begin(), RegUses[so0].end());
}

// Check the Sym is Register && is possibly been used as This Pointer
bool checkRegThisPtr_SPARC(Sym &s) {
    return (s.type_ == Sym::Register && s.data_ == SPARC_O0);
}

// update the This Pointer register with Class Name, (when Ctor is seen)
void updateThisPtrRegVersion_SPARC(std::string cls) {
    Sym so0 {Sym::Register, SPARC_O0, GRegVerTab_SPARC[SPARC_O0]};

    if (RegObj.find(so0) != RegObj.end()) {
        GRegVerTab_SPARC[SPARC_O0]++;
        so0.version_++;
    }

    RegObj[so0] = cls;
}

// Decoding the GEP Inst, check GPR register set dereference
bool checkGepGPR_SPARC(llvm::GetElementPtrInst *gep) {
    llvm::ConstantInt *cpufield = llvm::dyn_cast<llvm::ConstantInt>(gep->getOperand(2));
    return cpufield->equalsInt(1);
}

// Decoding the GEP Inst, update Def-Set table for register access
void updateRegDefSet_SPARC(llvm::GetElementPtrInst *gep, Sym &sl, SymTab &SymMap, llvm::Function *func) {

    llvm::ConstantInt *regno = llvm::dyn_cast<llvm::ConstantInt>(gep->getOperand(3));
    SPARC_REG reg = REG_SPARC(regno->getSExtValue());
    assert (ISREG_SPARC(reg));

    //(*LOG) << "GEP reg " << reg << " , " << *gep << "\n";

    // Do Global Register Versioning ONLY for possible class pointers - o0
    if (reg == SPARC_O0) {
        Sym sr {Sym::Register, reg, GRegVerTab_SPARC[reg]};
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
void handleGepUnionAnon_SPARC(llvm::GetElementPtrInst *gep, llvm::Function *func, Sym &sl, SymTab &SymMap, VerTabType &VerTab) {
    // Skip
}
