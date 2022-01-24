/*
** CalledFuncCount - an LLVM Module Pass to remove all unreachable functions.
**
** The algorithm is as follow:
**
** - First pass: collect entry points, indirect call targets, and control flow edges
** - Second pass: Prune indirect call targets based on argument number and alignment
** - Third pass: Reachability analysis starting from any entry points or pruned selected indirect targets
** - Fourth pass: Remove all unreachable functions from module
**
** Caveats: We include some indirect call targets based on the 'hasAddressTaken' flag, which is an
** over-approximation of all indirect call targets. Our pruning helps reducing the LLVM output file
** however the minimization is not optimal.
**
*/
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/CallSite.h"

#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Metadata.h"
#include "llvm/IR/DebugInfo.h"

#include "llvm/Analysis/CallGraph.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ExecutionEngine/ExecutionEngine.h"

#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Instructions.h"
#include <iterator>
#include <string>

#include "llvm/IR/SymbolTableListTraits.h"

namespace calledfunccount
{

using namespace llvm;
  
  struct CalledFuncCount// : public ModulePass
  {
  public:

    static char ID;

    // Persist total number of functions parsed
    unsigned int funcCount;
    unsigned int instCount;
    unsigned int callCount;
    unsigned int icallCount;
    unsigned int invokeCount;
    unsigned int errorCount;
    
    typedef std::pair<size_t,uint16_t>		intpair;
    typedef std::map<intpair, bool>		ArgSizeMap;

    // For each function in CallerMap, encode list of its direct callees in a CalleeMap
    typedef std::map<std::string, bool>		CalleeMap;
    typedef std::map<std::string, CalleeMap*>	CallerMap;

    //  These are computed in the first pass
    CalleeMap				cfgIndirectCalls; // stores all icall target names
    CalleeMap				cfgEntryPoints;   // stores all entry point names
    CallerMap				cfgAllEdges;	  // stores all direct call graphs edges

    // These are computed in a second pass
    CalleeMap				cfgWorkingSet;    // nodes to evaluate next
    CalleeMap				cfgWantedSet;     // nodes to retain
    CalleeMap				cfgWantedISet;    // nodes to retain
    CalleeMap				cfgUnionSet;	  // the union set of previous 2 wanted sets

    CalledFuncCount()// : ModulePass(ID) 
    { 
      funcCount = 0; 
      instCount = 0;
      callCount = 0;
      icallCount = 0;
      invokeCount = 0;
      errorCount = 0;
    }

    // This is called at the very beginning of the extension
    

    // This function is called at the end of it all. We dont run anything there currently.
    virtual bool doFinalization(Module& M)
    {
      
      float res = funcCount - cfgWantedSet.size();
      res = (100 * res) / funcCount;
      int  final = res;

      float res2 = funcCount - cfgWantedISet.size();
      res2 = (100 * res2) / funcCount;
      int  final2 = res2;

      float res3 = funcCount - cfgUnionSet.size();
      res3 = (100 * res3) / funcCount;
      int  final3 = res3;

      llvm::errs() << "TOTAL FUNC LIST COUNT WAS     = " << funcCount << "\n";
      llvm::errs() << "CHOSEN FUNC LIST FROM EPOINTS = " << cfgWantedSet.size() << "\n";
      llvm::errs() << "CHOSEN FUNC LIST FROM ICALLS  = " << cfgWantedISet.size() << "\n";
      llvm::errs() << "CHOSEN FUNC LIST UNION SET    = " << cfgUnionSet.size() << "\n";
      llvm::errs() << "REDUCED LLVM FILE BY " << final << "% (epoint set) \n";
      llvm::errs() << "REDUCED LLVM FILE BY " << final2 << "% (icalls set)\n";
      llvm::errs() << "REDUCED LLVM FILE BY " << final3 << "% (union set) \n";
      
      return (true);
    }


    // Note: this function is not used anymore - use hasAddressTaken flag instead to resolve icall targets.
    bool		PrintFuncType(Function *f)
    {
      
      FunctionType *ftype = f->getFunctionType();
      if (ftype != NULL)
	{
	  llvm::errs() << "RESOLVED function type \n";
	  
	  Type *ret = ftype->getReturnType();
	  if (ret != NULL)
	    {
	      Type::TypeID tid = ret->getTypeID();
	      llvm::errs() << "RESOLVED function return type = id " << tid << "\n";
	    }
	  else
	    llvm::errs() << "Unknown function return type \n";
	  unsigned int pnbr = ftype->getNumParams();
	  Type *curtype = NULL;
	  for (unsigned int i = 0; i < pnbr; i++)
	    {
	      curtype = ftype->getParamType(i);
	      if (curtype != NULL)
		{
		  Type::TypeID tid = curtype->getTypeID();
		  llvm::errs() << "RESOLVED function param type @" << i << " = id " << tid << "\n";
		}
	      else
		{
		  llvm::errs() << "Unknown function param type @" << i << "\n";
		}
	    }
	}
      else
	{
	  llvm::errs() << "Unknown function type \n";
	  return false;
	}

      return true;
    }

    
    // Choose whether or not this function is an entry point
    bool FuncIsEntryPoint(std::string& fname)
    {

      // Find entry points
      std::size_t pos1 = fname.find("16RequestProcessor");
      if (pos1 != std::string::npos)
	{
	  std::size_t pos2 = fname.find("process", pos1 + 18);
	  if (pos2 != std::string::npos)
	    {
	      llvm::errs() << "Found entry point : " << fname << "\n";
	      return (true);
	    }
	}
      
      // also set make as entry point
      pos1 = fname.find("main");
      if (pos1 != std::string::npos)
	{
	  llvm::errs() << "Found entry point : " << fname << "\n";
	  return (true);
	}

      // also add Modeling stubs for request context methods
      pos1 = fname.find("RequestContextFake");
      if (pos1 != std::string::npos)
	{
	  llvm::errs() << "Found entry point : " << fname << "\n";
	  return (true);
	}

      // Also add allocator stubs
      pos1 = fname.find("TrampolineAllocator");
      if (pos1 != std::string::npos)
	{
	  llvm::errs() << "Found entry point : " << fname << "\n";
	  return (true);
	}

      // Also add deallocator stubs
      pos1 = fname.find("TrampolineDeallocator");
      if (pos1 != std::string::npos)
	{
	  llvm::errs() << "Found entry point : " << fname << "\n";
	  return (true);
	}

  pos1 = fname.find("TrampolineNewDeleteAllocatorSingleton");
  if (pos1 != std::string::npos)
{
    llvm::errs() << "Found entry point : " << fname << "\n";
  return (true);
}

  pos1 = fname.find("TrampolineSetAllocatorRaw");
  if (pos1 != std::string::npos)
{
    llvm::errs() << "Found entry point : " << fname << "\n";
  return (true);
}
      pos1 = fname.find("__mcsema_constructor");
      if (pos1 != std::string::npos)
	{
	  llvm::errs() << "Found entry point : " << fname << "\n";
	  return (true);
	}

      pos1 = fname.find("__mcsema_destructor");
      if (pos1 != std::string::npos)
	{
	  llvm::errs() << "Found entry point : " << fname << "\n";
	  return (true);
	}

      pos1 = fname.find("__mcsema_detach_call_value");
      if (pos1 != std::string::npos)
	{
	  llvm::errs() << "Found entry point : " << fname << "\n";
	  return (true);
	}

      pos1 = fname.find("frame_dummy");
      if (pos1 != std::string::npos)
	{
	  llvm::errs() << "Found entry point : " << fname << "\n";
	  return (true);
	}

      pos1 = fname.find("_GLOBAL__sub_I_");
      if (pos1 != std::string::npos)
	{
	  llvm::errs() << "Found entry point : " << fname << "\n";
	  return (true);
	}

      pos1 = fname.find("return_the_number");
      if (pos1 != std::string::npos)
	{
	  llvm::errs() << "Found entry point : " << fname << "\n";
	  return (true);
    }
      pos1 = fname.find("returnNullPointer");
      if (pos1 != std::string::npos)
	{
	  llvm::errs() << "Found entry point : " << fname << "\n";
	  return (true);
    }
      pos1 = fname.find("DoNothing");
      if (pos1 != std::string::npos)
	{
	  llvm::errs() << "Found entry point : " << fname << "\n";
	  return (true);
    }
      pos1 = fname.find("returnTrue");
      if (pos1 != std::string::npos)
	{
	  llvm::errs() << "Found entry point : " << fname << "\n";
	  return (true);
    }
      pos1 = fname.find("basic_string_hooks");
      if (pos1 != std::string::npos)
	{
	  llvm::errs() << "Found entry point : " << fname << "\n";
	  return (true);
    }
      pos1 = fname.find("malloc");
      if (pos1 != std::string::npos)
	{
	  llvm::errs() << "Found entry point : " << fname << "\n";
	  return (true);
    }
      
      // This function is not an entry point
      return (false);
    }

    
    
    // This function is run on all functions of the LLVM file (see runOnModule)
    bool runOnFunction(Function& func) 
    {
      std::vector<std::string> called;
      std::string fname = func.getName();
      bool hat = func.hasAddressTaken();
      //bool dead = func.isDefTriviallyDead();

      // Find entry points
      if (FuncIsEntryPoint(fname))
	cfgEntryPoints[fname] = true;

      // Find indirect callees
      else if (hat)	
	{
	  /* llvm::errs() << "Found indirect call target : " << fname 
	     << "(dead = " << dead << ") "
	     << "(uses = " << func.getNumUses() << ") \n"; */
	  //cfgIndirectCalls[fname] = true;
	}


      funcCount++;

      // Create callee map for current function
      CalleeMap		*callee = new CalleeMap();
      cfgAllEdges[fname] = callee;      

      for (inst_iterator I = inst_begin(func), E = inst_end(func); I != E; ++I)
	{
	  Instruction &pinst = *I;
	  unsigned Opcode = pinst.getOpcode();
	  Constant *c = NULL;
	  GlobalValue *gv = NULL;
	  Function *f = NULL;
	  Value *fp = NULL;
	  CallSite *cs = NULL;
	  //unsigned as = 0;
	  
	  switch (Opcode)
	    {
	    case Instruction::Call:
	      cs = new CallSite(&pinst);
	      //as = cs->arg_size();
	      fp = cs->getCalledValue();
	      if (fp)
		{
		  c = dyn_cast<Constant>(fp); 
		  if (c)
		    {
		      gv = dyn_cast<GlobalValue>(c);
		      if (gv)
			{
			  f = dyn_cast<Function>(gv);
			  if (f)
			    {
			      
			      std::string targetFunc = f->getName();

			      /*
			       * This generates a lot of log so it is disabled by default
			       * 
			       llvm::errs() << "RESOLVED function name " << targetFunc
			       << " argsize=" << as
			       << " hat=" << (hat ? "Y" : "N") << "\n";
			      */
			      
			      // Add  the resolved target in the callee map of current function
			      callCount++;
			      (*callee)[targetFunc] = true;

			    }
			  else
			    {
			      errorCount++;
			      //llvm::errs() << "Unknown function object \n";
			    }
			}
		      else
			{
			  errorCount++;
			  //llvm::errs() << "Unknown GlobalValue \n";
			}
		    }
		  else
		    {
		      // Remember the number of icall counts
		      icallCount++;
		      //llvm::errs() << "Non-Constant Target \n";
		    }
		}
	      else
		{
		  errorCount++;
		  //llvm::errs() << "Unknown GetCalledValue \n";
		}

	      break;

	      // XXX: This is used in exceptions - currently unimplemented as unused by mcsema decompiler
	      // Plan is to have quite a similar code to the Instruction::Call case
	      // Exceptions are not used much in the Bloomberg C++ world so this is
	      // not an immediate priority.
	    case Instruction::Invoke:
	      invokeCount++;
	      break;
	    default:
	      break;
	    }
	  
	  instCount++;
	}
      
      /* llvm::errs() << "SUMMARY:" << func.getName() << ":" << instCount << ":" 
		   << callCount << ":" << icallCount << ":" << invokeCount << "\n";
      */

      return false;
    }
    

    // Compute the transitive closure of all callable function in workset and put results in wantset
    void	runOnWorkingSet(std::string label, CalleeMap &workset, CalleeMap &wantset)
    {
      CalleeMap addedSet;
      unsigned int iter = 0;

      llvm::errs() << label << " starting with initial Wanted/Working sets \n";
      
      // Main loop of the second phase
      while (workset.size() != 0) 
	{
	  for (CalleeMap::iterator it = workset.begin(); it != workset.end(); /* no increment */ )
	    {
	      std::string target = it->first;
	      workset.erase(it++);	    
	      
	      CalleeMap *callees = cfgAllEdges[target];
	      
	      //llvm::errs() << "Now parsing " << callees->size() << " new callees \n";
	      
	      for (CalleeMap::iterator it2 = callees->begin(); it2 != callees->end(); it2++)
		{
		  std::string callee = it2->first;
		  if (wantset.find(callee) == wantset.end())
		    {
		      wantset[callee] = true;
		      addedSet[callee] = true;
		    }
		}
	    }
	  
	  //llvm::errs() << "Added set of " << addedSet.size() << " elements \n";	  
	  workset.insert(addedSet.begin(), addedSet.end());
	  addedSet.clear();
	  iter++;
	  
	  //llvm::errs() << "Completed " << iter << " iteration : workset " 
	  //	       << workset.size() << " wantset " << wantset.size() << "\n";
	}

      // Print final list of functions to ship
      llvm::errs() << label << " SELECTED FUNC LIST COUNT: " << wantset.size() << " ITER#: " << iter << "\n";

      // There is no more workset element when we come back
    }


    /*
    void	    IPrint(llvm::Instruction *iop)
    {      
      llvm::errs() << "Transformed operand into instruction! \n";
      
      bool ins1 = isa<TerminatorInst>(iop);
      if (ins1) llvm::errs() << "IOP TerminatorInst \n";
      
      bool ins2 = isa<UnaryInstruction>(iop);
      if (ins2) llvm::errs() << "IOP UnaryInstr \n";
      
      bool ins3 = isa<BinaryOperator>(iop);
      if (ins3) llvm::errs() << "IOP BinaryOP \n";
      
      bool ins4 = isa<CmpInst>(iop);
      if (ins4) llvm::errs() << "IOP CmpInstr \n";
      
      bool ins5 = isa<StoreInst>(iop);
      if (ins5) llvm::errs() << "IOP StoreInst \n";
      
      bool ins6 = isa<FenceInst>(iop);
      if (ins6) llvm::errs() << "IOP FenceInst \n";
      
      bool ins7 = isa<AtomicCmpXchgInst>(iop);
      if (ins7) llvm::errs() << "IOP AtomicCmpXchgInst \n";
      
      bool ins8 = isa<AtomicRMWInst>(iop);
      if (ins8) llvm::errs() << "IOP AtomicRMWInst \n";
      
      bool ins9 = isa<GetElementPtrInst>(iop);
      if (ins9) llvm::errs() << "IOP GetElementPtr \n";
      
      bool ins10 = isa<CallInst>(iop);
      if (ins10) llvm::errs() << "IOP CallInst \n";
      
      bool ins11 = isa<SelectInst>(iop);
      if (ins11) llvm::errs() << "IOP SelectInst \n";
      
      bool ins12 = isa<ExtractElementInst>(iop);
      if (ins12) llvm::errs() << "IOP ExtractInst \n";
      
      bool ins13 = isa<InsertElementInst>(iop);
      if (ins13) llvm::errs() << "IOP InsertElemInst \n";
      
      bool ins14 = isa<ShuffleVectorInst>(iop);
      if (ins14) llvm::errs() << "IOP ShuffleVectorInst \n";
      
      bool ins15 = isa<InsertValueInst>(iop);
      if (ins15) llvm::errs() << "IOP InsertValueInst \n";
      
      bool ins16 = isa<PHINode>(iop);
      if (ins16) llvm::errs() << "IOP PHINode \n";
      
      bool ins17 = isa<LandingPadInst>(iop);
      if (ins17) llvm::errs() << "IOP LandingPadInst \n";
    }
    */


    // Print the kind of meta-data we are dealing with.
    // XXX: This is experimental code, not currently used.
    //void	ParseMetadata(Instruction* inst)
    //{
    //  MDNode *dbg = inst->getMetadata(LLVMContext::MD_dbg);
    //  if (dbg != NULL)
	//{
	//  llvm::errs() << "HAS DBG MD : \n";
	// 
	//  DILocation loc = llvm::DILocation(dbg);
	//  unsigned int line = loc.getLineNumber();
	//  std::string file = loc.getFilename();
	//  DIScope scope = loc.getScope();
	//  std::string scope_name = scope.getName();

	//  llvm::errs() << "Line: " << line << "\n";
	//  llvm::errs() << "File: " << file << "\n";
	//  llvm::errs() << "Scope: " << scope_name << "\n";

	//  DIDescriptor *desc = static_cast<DIDescriptor*>(&scope);
	//  if (desc != NULL) llvm::errs() << "ABLE to convert DIDescriptor \n";
	//  
	//  // ------ These flags look inaccurate to me. Some bools are true 
	//  // ------ when they should be false.
	//  
	//  bool ins1 = desc->isDerivedType();
	//  if (ins1) llvm::errs() << "DBG isDerivedType \n";
	//  
	//  bool ins2 = desc->isCompositeType();
	//  if (ins2) llvm::errs() << "DBG CTYPE \n";
	//  
	//  bool ins3 = desc->isBasicType();
	//  if (ins3) llvm::errs() << "DBG BTYPE \n";
	//  
	//  bool ins4 = desc->isVariable();
	//  if (ins4) llvm::errs() << "DBG VAR \n";
	//  
	//  bool ins5 = desc->isSubprogram();
	//  if (ins5) llvm::errs() << "DBG SP \n";
	//  
	//  bool ins6 = desc->isGlobalVariable();
	//  if (ins6) llvm::errs() << "DBG GV \n";

	//  bool ins7 = desc->isScope();
	//  if (ins7) llvm::errs() << "DBG SCOPE \n";

	//  bool ins8 = desc->isFile();
	//  if (ins8) llvm::errs() << "DBG FILE \n";

	//  bool ins9 = desc->isCompileUnit();
	//  if (ins9) llvm::errs() << "DBG CU \n";

	//  bool ins10 = desc->isNameSpace();
	//  if (ins10) llvm::errs() << "DBG NS \n";

	//  bool ins11 = desc->isLexicalBlockFile();
	//  if (ins11) llvm::errs() << "DBG LBF \n";

	//  bool ins12 = desc->isLexicalBlock();
	//  if (ins12) llvm::errs() << "DBG LB \n";

	//  bool ins13 = desc->isSubrange();
	//  if (ins13) llvm::errs() << "DBG SR \n";

	//  bool ins14 = desc->isEnumerator();
	//  if (ins14) llvm::errs() << "DBG ENUM \n";

	//  bool ins15 = desc->isType();
	//  if (ins15) llvm::errs() << "DBG TYPE \n";

	//  bool ins16 = desc->isUnspecifiedParameter();
	//  if (ins16) llvm::errs() << "DBG UP \n";

	//  bool ins17 = desc->isTemplateTypeParameter();
	//  if (ins17) llvm::errs() << "DBG TTP \n";

	//  bool ins18 = desc->isTemplateValueParameter();
	//  if (ins18) llvm::errs() << "DBG TVP \n";

	//  bool ins19 = desc->isObjCProperty();
	//  if (ins19) llvm::errs() << "DBG OBJC \n";

	//  bool ins20 = desc->isImportedEntity();
	//  if (ins20) llvm::errs() << "DBG IE \n";

	//  // ------


	//  DIType *type = static_cast<DIType*>(&scope);
	//  if (type != NULL) llvm::errs() << "ABLE to convert DIScope to DIType \n";

	//  DIFile *difile = static_cast<DIFile*>(&scope);
	//  if (difile != NULL) llvm::errs() << "ABLE to convert DIScope to DIFile \n";

	//  DICompileUnit *unit = static_cast<DICompileUnit*>(&scope);
	//  if (unit != NULL) llvm::errs() << "ABLE to convert DIScope to DICompileUnit \n";

	//  DISubprogram *prog = static_cast<DISubprogram*>(&scope);
	//  if (prog != NULL && ins5) 
	//    {
	//      llvm::errs() << "ABLE to convert DIScope to DISubprogram \n";

	//      /**** This fails in getName() data seems invalid

	//      const std::string& name = prog->getName();
	//      llvm::errs() << "NAME  = " << name  << "\n";

	//      const std::string& dname = prog->getDisplayName();
	//      llvm::errs() << "DNAME = " << dname << "\n";

	//      const std::string& lname = prog->getLinkageName();
	//      llvm::errs() << "LNAME = " << lname << "\n";

	//      DICompositeType ctype(prog->getType());
	//      MDString *mdname = ctype.getIdentifier();
	//      const std::string &tname = mdname->getString();
	//      llvm::errs() << "TNAME = " << tname << "\n";

	//      ***/

	//    }

	//  /*
	//  DILexicalBlock *block = static_cast<DILexicalBlock*>(&scope);
	//  if (block != NULL) llvm::errs() << "ABLE to convert DIScope to DILexicalBlock \n";

	//  DILexicalBlockFile *blockfile = static_cast<DILexicalBlockFile*>(&scope);
	//  if (blockfile != NULL) llvm::errs() << "ABLE to convert DIScope to DILexicalBlockFile \n";

	//  DINameSpace *ns = static_cast<DINameSpace*>(&scope);
	//  if (ns != NULL) llvm::errs() << "ABLE to convert DIScope to DINameSpace \n";
	//  */


	//  //llvm::errs() << "Type name: " << type.getName() << "\n";
	//  //llvm::errs() << "Type bitsize: " << type.getSizeInBits() << "\n";

	//  // Doesnt work -- llvm 8 only?!
	//  /*
	//  bool ins1 = isa<DlExpression>(dbg);
	//  if (ins1) llvm::errs() << "DBG DlExpression \n";
	//  
	//  bool ins2 = isa<DlGlobalVariableExpression>(dbg);
	//  if (ins2) llvm::errs() << "DBG DlGlobalVariableExpression \n";
	//  
	//  bool ins3 = isa<DlLocation>(dbg);
	//  if (ins3) llvm::errs() << "DBG DlLocation \n";
	//  
	//  bool ins4 = isa<DlMacroNode>(dbg);
	//  if (ins4) llvm::errs() << "DBG DlMacroNode \n";
	//  
	//  bool ins5 = isa<DlNode>(dbg);
	//  if (ins5) llvm::errs() << "DBG DlNode \n";
	//  
	//  bool ins6 = isa<MDTuple>(dbg);
	//  if (ins6) llvm::errs() << "DBG MDTuple \n";
	//  */

	//}

    //  MDNode *tbaa = inst->getMetadata(LLVMContext::MD_tbaa);
    //  if (tbaa != NULL)
	//{
	//  llvm::errs() << "HAS TBAA MD \n";
	//}

    //  MDNode *prof = inst->getMetadata(LLVMContext::MD_prof);
    //  if (prof != NULL)
	//{
	//  llvm::errs() << "HAS PROF MD \n";
	//}

    //  MDNode *fpmath = inst->getMetadata(LLVMContext::MD_fpmath);
    //  if (fpmath != NULL)
	//{
	//  llvm::errs() << "HAS FPMATH MD \n";
	//}

    //  MDNode *range = inst->getMetadata(LLVMContext::MD_range);
    //  if (range != NULL)
	//{
	//  llvm::errs() << "HAS RANGE MD \n";
	//}


    //  MDNode *tbaa_struct = inst->getMetadata(LLVMContext::MD_tbaa_struct);
    //  if (tbaa_struct != NULL)
	//{
	//  llvm::errs() << "HAS TBAA STRUCT MD \n";
	//}

    //  MDNode *invload = inst->getMetadata(LLVMContext::MD_invariant_load);
    //  if (invload != NULL)
	//{
	//  llvm::errs() << "HAS INVLOAD MD \n";
	//}

    //}

    //
    //// Try to resolve targets for function pointers
    //// XXX: This is experimental code currently disabled
    //bool	ResolveTargets(Function *parent, CallSite *cs)
    //{
    //  Value	*arg0 = NULL;
    //  Type	*t = NULL;
    //  int	id = 0;
    //  Value	*op = NULL;
    //  Instruction *inst = cs->getInstruction();
    //  bool	hasmd = inst->hasMetadata();

    //  //GlobalVariable *gv = NULL;
    //  //PointerType *gt = NULL;
    //  //Type *elmt = NULL;
    //  llvm::errs() << "ICallsite HAS " << (hasmd ? "" : "NO ") << "meta-data \n"; 
    //  if (hasmd) ParseMetadata(inst);

    //  arg0 = cs->getArgument(0);
    //  t = arg0->getType();
    //  if (t == NULL)
	//{
	//  llvm::errs() << "ResolveTarget: unable to get operand type \n";
	//  return (false);
	//}

    //  id = t->getTypeID();
    //  
    //  bool isptr = (id == Type::PointerTyID);
    //  bool isstruct = (id == Type::StructTyID);
    //  bool isint = (id == Type::IntegerTyID);
    //  
    //  llvm::errs() << "Found icall with arg0 type id " << id << " "
	//	   << "isstruct = " << isstruct << " "
	//	   << "isptr = " << isptr << " "
	//	   << "isint = " << isint << " "
	//	   << "classid = " << arg0->getValueID() << "\n";
    //  
  
    //  // First param was a global variable (likely the State structure of mcsema)
    //  // Check the first parameter in %edi which can be 'this' pointer to
    //  // an object, and attempt to get its type. 	  
    //  //gv = dyn_cast<GlobalVariable>(arg0);
    //  
    //  IntegerType *it = dyn_cast<IntegerType>(arg0->getType());
    //  if (it == NULL)
	//{
	//  llvm::errs() << " Unable to convert indirect call param to IntegerType \n";
	//  return (false);
	//}
    //  else
	//{
	//  llvm::errs() << " ABLE to convert indirect call param to IntegerType \n";
	//}	
    //  
    //  llvm::Instruction *user = dyn_cast<llvm::Instruction>(arg0);
    //  if (user == NULL)
	//{
	//  llvm::errs() << "Unable to convert Value to Instruction ! \n";
	//  return (false);
	//}
    //  else
	//{
	//  hasmd = user->hasMetadata();
	//  llvm::errs() << "ARG0 INSTR HAS " << (hasmd ? "" : "NO ") << "meta-data \n"; 
	//  llvm::errs() << "ABLE to convert Value to Instruction ! \n";
	//  if (hasmd) ParseMetadata(user);
	//}	
    //  
    //  /* Usually unable to convert */
    //  UnaryInstruction *cast = dyn_cast<UnaryInstruction>(user);
    //  if (cast == NULL)
	//{
	//  llvm::errs() << "Unable to convert Instruction to UnaryInstruction \n";
	//  return (false);
	//}
    //  else
	//{
	//  hasmd = cast->hasMetadata();
	//  llvm::errs() << "CAST INSTR HAS " << (hasmd ? "" : "NO ") << "meta-data \n"; 
	//  llvm::errs() << "ABLE to convert Instruction to UnaryInstruction \n";
	//  if (hasmd) ParseMetadata(cast);
	//}	
    //  
    //  LoadInst *load = dyn_cast<LoadInst>(cast);
    //  if (load == NULL)
	//{
	//  bool alloca = isa<AllocaInst>(cast);
	//  bool loadinst = isa<LoadInst>(cast);
	//  bool vaarginst = isa<VAArgInst>(cast);
	//  bool extract = isa<ExtractValueInst>(cast);
	//  std::string err;
	//  if (alloca)
	//    err = "FOUND ALLOCA \n";
	//  if (loadinst)
	//    err = "FOUND LOAD \n";
	//  if (vaarginst)
	//    err = "FOUND VAARG \n";
	//  if (extract)
	//    err = "FOUND EXTRACT \n";
	//  llvm::errs() << "UNABLE TO CAST INTO A LOAD : " << err;
	//  return (false);
	//}
    //  
    //  hasmd = load->hasMetadata();
    //  llvm::errs() << "LOAD INSTR HAS " << (hasmd ? "" : "NO ") << "meta-data \n"; 
    //  if (hasmd) ParseMetadata(load);

    //  op = load->getPointerOperand();
    //  t = op->getType();
    //  if (t != NULL)
	//{
	//  id = t->getTypeID();
	//  isptr = (id == Type::PointerTyID);
	//  isstruct = (id == Type::StructTyID);
	//  isint = (id == Type::IntegerTyID);
	//  
	//  llvm::errs() << "LOAD operand type id " << id << " "
	//	       << "isstruct = " << isstruct << " "
	//	       << "isptr = " << isptr << " "
	//	       << "isint = " << isint << " "
	//	       << "classid = " << op->getValueID() << "\n";
	//}
    //  
    //  llvm::Instruction *iop = dyn_cast<llvm::Instruction>(op);
    //  if (iop == NULL)
	//{
	//  llvm::errs() << "UNABLE TO CAST OPERAND INTO A INSTR \n";
	//  return (false);
	//}

    //  hasmd = iop->hasMetadata();
    //  llvm::errs() << "IOP INSTR HAS " << (hasmd ? "" : "NO ") << "meta-data \n"; 
    //  if (hasmd) ParseMetadata(iop);

    //  llvm::GetElementPtrInst *elm = dyn_cast<llvm::GetElementPtrInst>(iop);
    //  if (elm == NULL)
	//{
	//  llvm::errs() << "UNABLE TO CAST OPERAND INST INTO A GEP\n";
	//  return (false);	  
	//}

    //  hasmd = elm->hasMetadata();
    //  llvm::errs() << "GEP INSTR HAS " << (hasmd ? "" : "NO ") << "meta-data \n"; 
    //  if (hasmd) ParseMetadata(elm);

    //  op = elm->getPointerOperand();
    //  t = op->getType();	  
    //  if (t == NULL)
	//{
	//  llvm::errs() << "ResolveTarget: Unable to get GEP Operand Type\n";
	//  return (false);
	//}	  

    //  unsigned int idx = elm->getPointerOperandIndex();      
    //  id = t->getTypeID();
    //  isptr = (id == Type::PointerTyID);
    //  isstruct = (id == Type::StructTyID);
    //  isint = (id == Type::IntegerTyID);

    //  llvm::errs() << "GETI operand type id " << id << " "
	//	   << "isstruct = " << isstruct << " "
	//	   << "isptr = " << isptr << " "
	//	   << "isint = " << isint << " "
	//	   << "idx   = " << idx   << " "
	//	   << "classid = " << op->getValueID() << " "
	//	   << "parent func = " << parent->getName() << "\n";
    //  
    //  elm->dump();
    //  
    //  if (op->hasName())
	//{
	//  llvm::errs() << "GEP OP NAME: " << op->getName() << "\n";
	//  //uint64_t addr = ExecutionEngine::getGlobalValueAddress(op->getName());
	//  //const GlobalValue *gv = ExecutionEngine::getGlobalValueAtAddress((void *) addr);  
	//}
    //  
    //  // Note on state structure in llvm form:
    //  /*
	//@__mcsema_reg_state = internal global %struct.State { 
	//%struct.ArchState zeroinitializer, 
	//[32 x %union.VectorReg] zeroinitializer, 
	//%struct.ArithFlags zeroinitializer, 
	//%union.Flags zeroinitializer, 
	//%struct.Segments zeroinitializer, 
	//%struct.AddressSpace zeroinitializer, 
	//%struct.GPR { i64 0, %struct.Reg zeroinitializer, 
	//i64 0, %struct.Reg zeroinitializer, 
	//i64 0, %struct.Reg zeroinitializer, 
	//i64 0, %struct.Reg zeroinitializer, 
	//i64 0, %struct.Reg zeroinitializer, 
	//i64 0, %struct.Reg zeroinitializer, 
	//i64 0, %struct.Reg { 
	//%union.anon.1 { 
	//i64 ptrtoint (i64* getelementptr inbounds 
	//([131072 x i64]* @__mcsema_stack,
	//i64 0, i64 131064) to i64) 
	//} }, 
	//i64 0, %struct.Reg zeroinitializer, 
	//i64 0, %struct.Reg zeroinitializer, 
	//i64 0, %struct.Reg zeroinitializer, 
	//i64 0, %struct.Reg zeroinitializer, 
	//i64 0, %struct.Reg zeroinitializer, 
	//i64 0, %struct.Reg zeroinitializer, 
	//i64 0, %struct.Reg zeroinitializer, 
	//i64 0, %struct.Reg zeroinitializer, 
	//i64 0, %struct.Reg zeroinitializer, 
	//i64 0, %struct.Reg zeroinitializer }, 
	//%struct.X87Stack zeroinitializer, 
	//%struct.MMX zeroinitializer, 
	//%struct.FPUStatusFlags zeroinitializer, 
	//%union.XCR0 zeroinitializer, 
	//%union.FPU zeroinitializer }
    //  */
    //  
    //  if (idx == 0)
	//{	
	//  
	//  /* Not or User nor an instruction apparently... */
	//  /*
	//    llvm::User *user = dyn_cast<llvm::User>(op);
	//    if (user != NULL)
	//    {
	//    llvm::errs() << "Transformed GETI value into User\n";
	//    }	
	//    else
	//    {
	//    llvm::errs() << "GETI not a User type : ";
	//    op->dump();
	//    }
	//  */
	//  
	//  /* This is quite useless - 12 uses all with same pointer */
	//    unsigned int nbr = 0;
	//    for (auto i = op->use_begin(); i != op->use_end(); i++)
	//      {
	//	nbr++;
	//	Use &a = (*i);
	//	Value *v = a.get();
	//	v->dump();
	//	t = v->getType();			      
	//	if (t != NULL)
	//	  {
	//	    id = t->getTypeID();
	//	    isptr = (id == Type::PointerTyID);
	//	    isstruct = (id == Type::StructTyID);
	//	    isint = (id == Type::IntegerTyID);		  
	//	    llvm::errs() << "USE type id " << id << " "
	//			 << "isstruct = " << isstruct << " "
	//			 << "isptr = " << isptr << " "
	//			 << "isint = " << isint << " "
	//			 << "idx   = " << idx   << " "
	//			 << "classid = " << v->getValueID() << "\n";
	//	  }
	//      }
	//    llvm::errs() << "NBR of Value uses = " << nbr << "\n";
	//  
	//}
    //  
    //  /*
    //  // How does one convert the value to a void*? fp->...
    //  gv = getGlobalValueAtAddress(static_cast<void*>(...));
    //  if (gv)
    //  {
    //  gt = gv->getType();
    //  elmt = gt->getElementType();
    //  if (elmt != NULL)
    //  {
    //  id = elmt->getTypeID();
    //  isptr = (id == Type::PointerTyID);
    //  isstruct = (id == Type::StructTyID);				      
    //  llvm::errs() << "ICALL on Global Variable of element type id " << id << " "
    //  << "isstruct = " << isstruct << " "
    //  << "isptr = " << isptr << "\n";				      
    //  }
    //  else
    //  llvm::errs() << "Element type is NULL \n";
    //  }
    //  else
    //  llvm::errs() << "First argument is not a global variable \n";
    //  */
	//  
    //  return (true);
    //}
    
    
    // This function finds all the argument size for the indirect calls reachable from entry points
    void	PruneIndirectCallees(Module& M, CalleeMap& epoints, CalleeMap& indirects)
    {
      ArgSizeMap amap;
      ArgSizeMap smap;

      llvm::errs() << "Constructing pruning map... \n";

      // First compute arg size map for all entry points indirect calls
      for (CalleeMap::iterator it = epoints.begin(); it != epoints.end(); it++)
	{
	  std::string name = it->first;
	  Function *func = M.getFunction(name);
	  if (func == NULL)
	    continue;
	  
	  //llvm::errs() << "Pruning indirect callees for " << name << "\n";

	  unsigned int instnbr = 0;
	  unsigned int icallnbr = 0;

	  for (inst_iterator I = inst_begin(func), E = inst_end(func); I != E; ++I)
	    {
	      Instruction &pinst = *I;
	      unsigned Opcode = pinst.getOpcode();
	      Constant *c = NULL;
	      Value *fp = NULL;
	      CallSite *cs = new CallSite(&pinst);
	      size_t  as = 0;
	      size_t  aa = 0;
	      intpair p;

	      instnbr++;
	      switch (Opcode)
		{
		case Instruction::Call:
		  // Remember argument size/alignment for indirect calls  
		  as = cs->arg_size();
		  aa = cs->getParamAlignment(0);
		  fp = cs->getCalledValue();
		  if (fp)
		    {
		      c = dyn_cast<Constant>(fp); 
		      if (c)
			{
			  /* direct call, no extra collection */
			}
		      else
			{
			  icallnbr++;
			  p = std::make_pair(as, aa);
			  amap[p] = true;
			  
			  // Prints: %4684 = inttoptr i64 %4670 to i64 (i64, i64, i64, i64, i64, i64, i64, i64)* 
			  //fp->dump();			  
			  // XXX: Julien's experimental code here, do not enable by default
			  //bool res = ResolveTargets(func, cs);
			  //llvm::errs() << "ResolveTarget returned " << res << "\n";
			}
		    }		  
		  continue;
		  break;
		case Instruction::Ret:
		  //llvm::errs() << "Found return for " << name << "\n";
		  break;
		default:
		  break;
		} 	      
	    }	  
	  
	  //llvm::errs() << "Collected " << icallnbr << " icalls from " 
	  //	       << instnbr << " instrs in entry-point function " << name << "\n";
	  
	}

      llvm::errs() << "Done creating pruning map (size = " << amap.size() << ") "
		   << "Now filtering indirects want-set\n";

      // Remove all indirectly called functions from wanted set if they dont have matching 
      // argument size than those collected in the entry points set
      for (CalleeMap::iterator it = indirects.begin(); it != indirects.end(); /* no increment */ )
	{
	  std::string name = it->first;
	  Function *func = M.getFunction(name);
	  if (func == NULL)
	    continue;
	  size_t    as = func->arg_size();
	  uint16_t  aa = func->getParamAlignment(0);
	  intpair   p = std::make_pair(as, aa);
	  if (amap.find(p) != amap.end())
	    it++;
	  else
	    indirects.erase(it++);
	}

    }


    // Remove ctors as they may point to removed functions now
    void	EmptyCtorsDtors(Module& M, std::string varname)
    {   
      GlobalVariable *ctors = M.getGlobalVariable(varname);
      if (ctors != NULL)
	{
	  ConstantArray *OldCA = cast<ConstantArray>(ctors->getInitializer());
	  ArrayType *ATy = ArrayType::get(OldCA->getType()->getElementType(), 0);
	  SmallVector<Constant *, 10> CAList;
	  Constant *CA = ConstantArray::get(ATy, CAList);
	  llvm::errs() << "Found " + varname + " table \n";
	  GlobalVariable *newctors = new GlobalVariable(CA->getType(), ctors->isConstant(), ctors->getLinkage(),
							CA, "", ctors->getThreadLocalMode());
	  llvm::errs() << "Created " + varname + " copy \n";
	  M.getGlobalList().insert(M.getGlobalList().begin(), newctors);
	  llvm::errs() << varname << " : Inserted copy in global list \n";
	  newctors->takeName(ctors);
	  llvm::errs() << varname << " : Took name of old variable \n";
	  
	  // Nuke the old list, replacing any uses with the new one.
	  if (!ctors->use_empty()) 
	    {
	      Constant *V = newctors;
	      if (V->getType() != ctors->getType())
		{
		  V = ConstantExpr::getBitCast(V, ctors->getType());
		  llvm::errs() << varname + " bitcasted \n";
		}
	      ctors->replaceAllUsesWith(V);
	      llvm::errs() << varname << " : replaced all uses \n";
	    }
	  ctors->eraseFromParent();
	  llvm::errs() << varname << " : removed from parent \n";
	}
      else
	llvm::errs() << varname << " : no table present, skipping \n";
    }

    /* Prune Globals */
    int PruneGlobals(Module& M, bool countonly)
    {
      int rmglob = 0;

      for (auto i = M.getGlobalList().begin(); i != M.getGlobalList().end(); )
	{
	  GlobalVariable &curvar = *i;
	  unsigned int uses = 0;
	  for (Value::use_iterator i = curvar.use_begin(); i != curvar.use_end(); ++i)
	    uses++;
	  if (uses == 0)
	    {
	      i++;
	      std::string name = curvar.getName();
	      if (countonly == false)
		curvar.eraseFromParent();
	      //llvm::errs() << "REMOVED GVAR = " << name << " uses# = " << uses << "\n";
	      rmglob++;
	    }
	  else
	    i++;
	}      
      return (rmglob);
    }
    
    
    // Main function of the LLVM pass
    virtual bool runOnModule(Module& M, const std::set<std::string> &possible_vfuncs)
    {
      const std::string& nam = M.getModuleIdentifier();

      llvm::errs() << "********** MODULE NAME : " << nam << "\n";

      llvm::errs() << "Prelim pass: find how many globals are unused aet the very beginning \n";

      //int unusedglob = PruneGlobals(M, true);
      //llvm::errs() << "Could already prune " << unusedglob << " globals now \n";

      llvm::errs() << "Starting first pass : collect entry points, icall targets and call edges. \n";

      // First gather all entry points, all indirect targets and compute call graph when possible
      for (auto curFref = M.getFunctionList().begin(), endFref = M.getFunctionList().end(); 
	   curFref != endFref; ++curFref) 
	{
	  llvm::errs() << "M found function: " << curFref->getName() << "\n";
	  Function& func = *curFref;
	  runOnFunction(func);
	}

      // Initialize cfgIndirectCalls
      for (auto vf : possible_vfuncs) {
        cfgIndirectCalls[vf] = true;
      }
      
      // Get count for indirect calls and entry points
      unsigned int icalls = cfgIndirectCalls.size();
      unsigned int epoints = cfgEntryPoints.size();

      llvm::errs() << "Found " << funcCount   << " functions      \n";
      llvm::errs() << "Found " << epoints     << " entry points   \n";
      llvm::errs() << "Found " << callCount   << " directly called funcs   \n";
      llvm::errs() << "Found " << icalls      << " indirectly called funcs \n";
      llvm::errs() << "Found " << invokeCount << " invoke calls   \n";
      llvm::errs() << "Found " << errorCount  << " unknown calls  \n";

      llvm::errs() << "Starting second pass : perform control flow analysis \n";

      // Second, compute the transitive closure of wanted functions by control flow analysis
      // We keep all functions reachable from entry points and/or reachable from indirect call targets
      // Analysis of 360 BAS services show that this reduces LLVM file size by 60-80% on average
      cfgWorkingSet.insert(cfgEntryPoints.begin(), cfgEntryPoints.end());
      cfgWantedSet.insert(cfgWorkingSet.begin(), cfgWorkingSet.end());      
      runOnWorkingSet("EPOINTS", cfgWorkingSet, cfgWantedSet);
      
      // Filter indirect calls target 
      //PruneIndirectCallees(M, cfgWantedSet, cfgIndirectCalls);
      icalls = cfgIndirectCalls.size();
      llvm::errs() << "Number of indirect stubs after pruning: " << icalls << "\n";	

      // Do the same for callees of functions flagged as indirect call targets
      cfgWorkingSet.insert(cfgIndirectCalls.begin(), cfgIndirectCalls.end());
      cfgWantedSet.insert(cfgWorkingSet.begin(), cfgWorkingSet.end());      
      runOnWorkingSet("ICALLS", cfgWorkingSet, cfgWantedISet);
      
      // Compute Union set
      cfgUnionSet.insert(cfgWantedSet.begin(), cfgWantedSet.end());
      cfgUnionSet.insert(cfgWantedISet.begin(), cfgWantedISet.end());      
      
      llvm::errs() << "Starting final pass : removing unwanted functions \n";

      int rmfunc = 0;
      
      // Reparse the function list and remove all functions that are not in the wanted set
      for (auto curFref = M.getFunctionList().begin(), endFref = M.getFunctionList().end(); 
	   curFref != endFref; )
	{
	  //llvm::errs() << "M found function: " << curFref->getName() << "\n";
	  Function& func = *curFref;
	  std::string fname = func.getName();
	  if (cfgUnionSet.find(fname) == cfgUnionSet.end())
	    {    
	      //llvm::errs() << "Deleting refs on function " << fname << "\n";
	      func.replaceAllUsesWith(UndefValue::get((Type*)func.getType())); 
	      //llvm::errs() << "Erasing from parent function " << fname << "\n";
	      curFref++;
	      func.eraseFromParent();	      
	      //llvm::errs() << "REMOVED function " << fname << " from module \n";
	      rmfunc++;
	    }
	  else
	    curFref++;
	}

      // Remove ctors from LLVM file
      //EmptyCtorsDtors(M, "llvm.global_ctors");
      //EmptyCtorsDtors(M, "llvm.global_dtors");

      llvm::errs() << "Now removing unused global variables \n";
      
      //int rmglob = PruneGlobals(M, false);
      
    //  llvm::errs() << "Returning from minimization pass (removed "
	//	   << rmfunc << " funcs, " << rmglob << " globals) \n";

      return true;
    }
    
  };
  
} // namespace

char calledfunccount::CalledFuncCount::ID = 0;
//static RegisterPass<CalledFuncCount> X("calledfunccount", "Called function lists", false, false);
