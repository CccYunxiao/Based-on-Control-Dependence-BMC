
#include <llvm/IR/LLVMContext.h>
#include <llvm/IR/Module.h>
#include <llvm/IR/InstrTypes.h>
#include <llvm/Support/raw_ostream.h>
#include <llvm/ADT/DenseMap.h>
#include <llvm/IR/Constants.h>
#include <llvm/IR/Instructions.h>
#include <llvm/IR/CallSite.h>
#include <llvm/IRReader/IRReader.h>
#include <llvm/Support/SourceMgr.h>
#include <llvm/IR/Dominators.h>
#include <llvm/Analysis/LoopInfo.h>
#include <llvm/ADT/SmallVector.h>
#include <sstream>
#include <string>
#include <stdio.h>
#include <mathsat.h>
#include <assert.h>
#include <map>
#include <boost/iterator/iterator_concepts.hpp>
#include <llvm/Support/TargetSelect.h>
#include <llvm/IR/LegacyPassManager.h>
#include <llvm/Transforms/Scalar.h>

#include <llvm/IR/IRBuilder.h>
#include "newInterpreter.h"
using namespace llvm;
using namespace std;


    void newInterpreter::DomTrace(BasicBlock* topbb,BasicBlock* botbb,RoadInfo &rinfo)
    {
	DomTrace(topbb,domtree->getNode(botbb)->getIDom()->getBlock(),botbb,rinfo);
    }
    
    void newInterpreter::DomTrace(BasicBlock* topbb,BasicBlock* idombb,BasicBlock* botbb,RoadInfo &rinfo)
    {
// 	if(idombb == latch)
// 	{
// 	    rinfo.OneRoad++;
// 	    rinfo.fullstr = rinfo.fullstr + latch_cond_formula;
// 	}
	if(pdt->dominates(botbb,idombb))
	{
// 	    outs()<<topbb->getName()<<"---"<<idombb->getName()<<"---"<<botbb->getName()<<'\n';getchar();
	    if(topbb!=idombb)
	    {
// 		outs()<<topbb->getName()<<"---"<<idombb->getName()<<"---"<<botbb->getName()<<'\n';getchar();
		DomTrace(topbb,domtree->getNode(idombb)->getIDom()->getBlock(),idombb,rinfo);
	    }
// 	    else
// 	    {
// 		RoadInfo info;
// 		info.fullstr="";
// 		info.OneRoad=0;
// 		getCMPs(topbb,idombb,botbb,"",info);
// 		if(!info.fullstr.empty())
// 		{
// 		    rinfo.fullstr = rinfo.fullstr + info.fullstr;
// 		    rinfo.OneRoad ++;
// 		}
// 		
// 	    }
	}else
	{
	    if(idombb->getTerminator()->getNumSuccessors()>1)
	    {
		int n=0;
		string s;
		for(auto iter=pred_begin(botbb);iter!=pred_end(botbb);iter++)
		{
		    RoadInfo info;
		    info.fullstr="";
		    info.OneRoad=0;
		    getCMPs(idombb,*iter,botbb,"",info);
		    if(info.OneRoad>1)
		    {
			info.fullstr = "(and " + info.fullstr +")";
		    }
		    if(!info.fullstr.empty())
		    {
			n++;
			s = s + info.fullstr;
		    }
		}
		if(n>1)
		{
		    s = "(and " + s +")";
		}
		if(!s.empty())
		{
		    rinfo.fullstr = rinfo.fullstr + s;
		    rinfo.OneRoad ++;
		}
	    }
	    if(topbb!=idombb)
	    {
// 		outs()<<topbb->getName()<<"---"<<idombb->getName()<<"---"<<botbb->getName()<<'\n';getchar();
		DomTrace(topbb,domtree->getNode(idombb)->getIDom()->getBlock(),idombb,rinfo);
	    }
	}
	
    }

    
    void newInterpreter::getCMPs(BasicBlock* topbb, BasicBlock* idombb, BasicBlock* botbb, string str, RoadInfo &info)
    {
	string s;
	
// 	outs()<<topbb->getName()<<"---"<<idombb->getName()<<"---"<<botbb->getName()<<'\n';

	if(idombb->getTerminator()->getNumSuccessors()>1)
	{
	    BranchInst* brInst = dyn_cast<BranchInst>(idombb->getTerminator());
	    if(brInst)
	    {
		if(idombb->getTerminator()->getSuccessor(0)==botbb)
		{
		    s = calculateVarible(brInst->getCondition()) +str;
// 		    outs()<<s<<'\n';
		}
		else
		{
		    s ="(not "+ calculateVarible(brInst->getCondition())+") "+str;
// 		    outs()<<s<<'\n';
		}
	    }
	    
	    SwitchInst* swInst = dyn_cast<SwitchInst>(idombb->getTerminator());
	    if(swInst)
	    {
		string terValue = swInst->getName().str();
		string defStr = "(and ";
		for(SwitchInst::CaseIt i = swInst->case_begin(),e = swInst->case_end(); i != e; i++)
		{
		    string constant = InttoString(i.getCaseValue()->getZExtValue());
		    if(i.getCaseSuccessor() == botbb)
		    {
			s = "(= $"+terValue+" "+constant+") " + str;
			break;
		    }
		    defStr = defStr +"(not (= $"+terValue+" "+constant+") ) ";
		}
		if(swInst->getDefaultDest() == botbb)
		{
		    s = defStr+") "+str;
		}
	    }
	}
	
	if(topbb == idombb)
	{
	    if(!info.fullstr.empty())
	    {
		info.OneRoad ++;
	    }
	    
	    if(str.empty())
	    {
		info.fullstr = info.fullstr + s;
	    }
	    else
	    {
		info.fullstr = info.fullstr + "(and "+s+") ";
	    }
	    
	    
	}
	else
	{
	    for(auto iterbb = pred_begin(idombb) ; iterbb!=pred_end(idombb) ; iterbb++)
	    {
		BasicBlock* iter = *iterbb;
		getCMPs(topbb,iter,idombb,s,info);
	    }
	}

    }


    void newInterpreter::DominateInfo(Function* func)
    {
	pdt->runOnFunction(*func);
	DominatorTree dt = dta->run(*func);
	runToposort(*func);
	string domstr;
	string pdomstr;
	string cdstr;
	for(auto funcite=func->begin();funcite!=func->end();funcite++)
	{
	    BasicBlock* bb = dyn_cast<BasicBlock>(funcite);
	    
	    if(bb->getName().str()!="entry")
		domstr = domstr + bb->getName().str()+"  Idom:  "+dt.getNode(bb)->getIDom()->getBlock()->getName().str()+'\n';
	    else
		domstr =domstr + "entry  Idom:  Null\n";
	    
	    if(bb->getTerminator()->getOpcode()!=Instruction::Ret)
		pdomstr = pdomstr + bb->getName().str()+"  Pdom:  "+pdt->getNode(bb)->getIDom()->getBlock()->getName().str()+'\n';
	    else
		pdomstr = pdomstr + bb->getName().str()+"  Pdom:  Null\n";
	    
	    
	}
	outs()<<"DominateInfo:\n"<<domstr<<"Post-DominateInfo\n"<<pdomstr;
	
    }
    
    void newInterpreter::TraceCMPs(BasicBlock* top,BasicBlock* tracebot,BasicBlock* bot,BasicBlock* incomingBB,BasicBlock* tail,string str,RoadInfo& info)
    {
	string s;
	unsigned int n = tracebot->getTerminator()->getNumSuccessors();
	unsigned int m = incomingBB->getTerminator()->getNumSuccessors();
// 	outs()<<top->getName().str()<<'\n'<<tracebot->getName().str()<<'\n'<<bot->getName().str()<<'\n'<<tail->getName().str()<<'\n';
	
	if(m==2 && tracebot==bot)
	{
	    BranchInst* brInst = dyn_cast<BranchInst>(incomingBB->getTerminator());
	    if(brInst)
	    {
		if(incomingBB->getTerminator()->getSuccessor(0)==tail)
		{
		    s = calculateVarible(brInst->getCondition()) +str;
// 		    outs()<<"s= "<<s<<'\n';
		}else if(incomingBB->getTerminator()->getSuccessor(1)==tail)
		{
		    s ="(not "+ calculateVarible(brInst->getCondition())+") "+str;
// 		    outs()<<"s= "<<s<<'\n';
		}
	    }
	}
	
	if(n!=1 && tracebot!=bot)
	{
	    BranchInst* brInst = dyn_cast<BranchInst>(tracebot->getTerminator());
	    if(brInst)
	    {
		if(tracebot->getTerminator()->getSuccessor(0)==bot)
		{
		    s = calculateVarible(brInst->getCondition()) +str;
// 		    outs()<<"s= "<<s<<'\n';
		}else if(tracebot->getTerminator()->getSuccessor(1)==bot)
		{
		    s ="(not "+ calculateVarible(brInst->getCondition())+") "+str;
// 		    outs()<<"s= "<<s<<'\n';
		}
	    }
	    
	    SwitchInst* swInst = dyn_cast<SwitchInst>(tracebot->getTerminator());
	    if(swInst)
	    {
		string terValue = swInst->getName().str();
		string defStr = "(and ";
		for(SwitchInst::CaseIt i = swInst->case_begin(),e = swInst->case_end(); i != e; i++)
		{
		    string constant = InttoString(i.getCaseValue()->getZExtValue());
		    if(i.getCaseSuccessor() == bot)
		    {
			s = "(= $"+terValue+" "+constant+") " + str;
			break;
		    }
		    defStr = defStr +"(not (= $"+terValue+" "+constant+") ) ";
		}
		if(swInst->getDefaultDest() == bot)
		{
		    s = defStr+") "+str;
		}
	    }
	}
	else
	{
	    s = s + str;
	}
	
// 	outs()<<s<<'\n';

	if(top!=tracebot)
	{
	    for(pred_iterator ite = pred_begin(tracebot);ite!=pred_end(tracebot);ite++)
	    {
		BasicBlock* interBB = *ite;
		TraceCMPs(top,interBB,tracebot,incomingBB,tail,s,info);
	    }
	}
	else
	{
	    if(info.fullstr.empty())
	    {
		info.OneRoad = false;
	    }
	    else
	    {
		info.OneRoad = true;
	    }
	    if(str.empty())
	    {
		info.fullstr = info.fullstr + s;
	    }
	    else
	    {
		info.fullstr = info.fullstr + "(and "+s+") ";
	    }
	    return ;
	}
    }
    
    
    bool newInterpreter::recursiveDFSToposort( BasicBlock* BB)
    {
	ColorMap[BB]=newInterpreter::grey;
	 TerminatorInst *Tinst = BB->getTerminator();
	for(unsigned int i=0,NSucc=Tinst->getNumSuccessors();i<NSucc;i++)
	{
	    BasicBlock *Succ = Tinst->getSuccessor(i);
	    Color SuccColor = ColorMap[Succ];
	    if(SuccColor == newInterpreter::white)
	    {
		if(!recursiveDFSToposort(Succ))
		    return false;
	    }else if(SuccColor == newInterpreter::grey)
	    {
// 		outs()<<" Detected cycle: edge from "<<BB->getName()<<"to "<<Succ->getName()<<"\n";
		return false;
	    }
	}
	ColorMap[BB] = newInterpreter::black;
	SortedBBs.push_back(BB);
	return true;
    }
    
    void newInterpreter::runToposort( Function &F)
    {
// 	outs()<<"Topological sort of "<<F.getName()<<":\n";
	for( BasicBlock &bbi : F)
	{
	    ColorMap[&bbi] = newInterpreter::white;
	}
	bool success = recursiveDFSToposort(&F.getEntryBlock());
	if(success)
	{
// 	    outs()<<"-------------------start  outputting Topo infomation-------------------\n";
	    int n=1;
	    for(BBVector::reverse_iterator RI = SortedBBs.rbegin(),RE = SortedBBs.rend();
		RI != RE; ++RI)
	    {
		//BasicBlock *bb;bb->getTerminator()->getSuccessor(numSucc-1)->getName().str();
// 		outs()<<n<<"  "<<(*RI)->getName()<<"\n";
		int2bb[n]=(*RI);
		bb2int[(*RI)]=n;
		n++;
	    }
// 	    outs()<<"-------------------end outputting Topo infomation-------------------\n";
	}else
	{
	    outs()<<"Sorting failed\n";
	}
    }
    

    void newInterpreter::getIRModule(LLVMContext &context)
    {
	module = parseIRFile(file_name, Err, context);
	Mod = module.get();
	if(!Mod)
	{
	    outs()<<"the module is empty...\n";
	}
    }
    
    void newInterpreter::check_sat(LLVMContext &context)
    {
	while ( (unroll_time <= max_unroll_time) && has_loop)
	{
	    getIRModule(context);
// 	    latch_cond.clear();
// 	    assert_cond.clear();
	    skipSMT_continue_unroll = LoopUnroll(context);
	    if(skipSMT_continue_unroll)
	    {
		outs()<<"Time="<<unroll_time<<":UNSAT. continue unroll...\n";
		getchar();
		unroll_time++;
		continue;
	    }
	    
	    status = encodeIR();
	    reset();
// 	    latch_cond_formula.clear();
// 	    Transition_latch_exit.clear();
// 	    end_formula.clear();
	    
	    if((status == MSAT_UNSAT) || (status == MSAT_UNKNOWN))
	    {
		outs()<<"Time="<<unroll_time<<":UNSAT...\n";
		getchar();
		unroll_time++;
		end_MathSAT();
		return;
	    }else
	    {
// 		print_model(env);
// 		print_assertInfo(env);
		outs()<<"Time="<<unroll_time<<":SAT. You need to check whether to unroll...\n";
		getchar();
		unroll_time++;
		end_MathSAT();
		continue;
	    }
	}
	return;
    }
    
    msat_result newInterpreter::encodeIR()
    {
	init_MathSAT();
// 	pdt->runOnFunction(*func);
// 	DominatorTree dt = dta->run(*func);
// 	domtree = &dt;
// 	runToposort(*func);
// 	RoadInfo info;
// 	info.fullstr="";
// 	info.OneRoad=0;
// 	DomTrace(int2bb[1],int2bb[14],info);
// 	getCMPs(int2bb[5],int2bb[6],int2bb[7],"",info);
// 	if(info.OneRoad>1)
// 	{
// 	    outs()<<"(and "<<info.fullstr<<")\n";
// 	}else
// 	outs()<<info.fullstr<<'\n';
	declareVarible();
	
	assertVariable();
	
	status = msat_solve(env);
	
	return status;
    }
    
    void newInterpreter::reset()
    {
	pdt->releaseMemory();
	domtree = nullptr;
	ColorMap.clear();
	SortedBBs.clear();
	int2bb.clear();
	bb2int.clear();
	latch_cond_formula.clear();
	end_formula.clear();
	latch = nullptr;
    }

    
    bool newInterpreter::LoopUnroll(LLVMContext &context)
    {
	//unroll the loop
	llvm::legacy::PassManager lpm;
	lpm.add(createPromoteMemoryToRegisterPass());
	lpm.add(createLoopSimplifyPass());
	lpm.add(createLoopRotatePass());
	lpm.add(createLCSSAPass());
// 	int threshold = UINT_MAX;
// 	int unrollCount = unroll_time;
// 	int allowPartial = 1;
	lpm.add(createLoopUnrollPass(UINT_MAX,unroll_time,1));
	lpm.add(createInstructionNamerPass());
	//lpm.add(createLoopRerollPass());
	//lpm.add(new looptest());
	lpm.run(*Mod);
	
	func = Mod->getFunction("main");
	
	
// 	func->dump();
	assert(func);
	
	//get loop info
	DominatorTree dt;
	dt.recalculate(*func);
	LoopInfo li;
	li.analyze(dt);
	
	if(li.begin()==li.end())
	{
	    has_loop = false;
	}else
	{
	    has_loop = true;
	}
	
	for(LoopInfo::iterator i=li.begin(),e=li.end();i!=e;i++)
	{
	    Loop *L = *i;

	    BasicBlock* header = L->getHeader();
	    
	    latch = L->getLoopLatch();
	    TerminatorInst* latch_end = latch->getTerminator();
	    BranchInst* latch_term = dyn_cast<BranchInst>(latch_end);
	    
	    SmallVector<BasicBlock*,8> bb_Exits;
	    L->getExitBlocks(bb_Exits);
	    if(bb_Exits.empty())
		errs()<<"SmallVector is empty\n";
	    BasicBlock *exit_bb = bb_Exits[0];
	    
	    
	    //dump the names of header,latch and exit BasicBlock
	    outs()<<"\n-------------loop-info-start----------------\n";
	    outs()<<"header:"<<header->getName()<<'\n';
	    outs()<<"latch:"<<latch->getName()<<'\n';
	    outs()<<"exit:"<<exit_bb->getName()<<"\n";
	    for(int n=1;n<bb_Exits.size();n++)
	    {
		outs()<<"exit:"<<bb_Exits[n]->getName()<<"\n";
		if(exit_bb != bb_Exits[n])
		{
		    outs()<<"there are many exit block in the loop...\n";
		    assert(false);
		}
	    }
	    outs()<<"--------------loop-info-end-----------------\n";
	    
	    
	    if(latch_term->getNumSuccessors()==1)
	    {
		//continue unroll loop
		skipSMT_continue_unroll=true;
		return skipSMT_continue_unroll;
	    }
	    
	    
	    for(auto header_i = header->begin();header_i!=header->end();header_i++)
	    {
		
		PHINode* phi = dyn_cast<PHINode>(header_i);
		if(!phi)
		    break;
		
		
		for(unsigned int n=0;n < phi->getNumIncomingValues();n++)
		{

		    if(phi->getIncomingBlock(n) == latch)
		    {
			phi->removeIncomingValue(n);
			n--;
		    }
		    
		}
		
	    }
	    
	    
	    if(latch_term->getSuccessor(0)==header )
	    {
		latch_cond_formula =calculateVarible(latch_term->getCondition());
	    }
	    
	    latch_term->dropAllReferences();
	    latch_term->removeFromParent();
	    IRBuilder<> builder(context);
	    builder.SetInsertPoint(latch);
	    builder.CreateBr(exit_bb);
	    
	    func->dump();

	}
	skipSMT_continue_unroll = false;
	return skipSMT_continue_unroll;
    }
    
    void newInterpreter::init_MathSAT()
    {
	cfg = msat_create_config();
	msat_set_option(cfg,"model_generation","true");
	env = msat_create_env(cfg);
	
    }
    
    void newInterpreter::end_MathSAT()
    {
	msat_destroy_env(env);
	msat_destroy_config(cfg);
    }
    
    
    void newInterpreter::declareVarible()
    {
	if(!func)
	    return;

	string decla_formulas;

// 	outs()<<"(set-logic QF_BV)\n";
	for(iplist<BasicBlock>::iterator iter = func->getBasicBlockList().begin();
	    iter != func->getBasicBlockList().end();
            iter++)
	{
	    ///output declare bbi
// 	    decla_formulas = decla_formulas+ "(declare-fun $"+iter->getName().str()+" () Bool)";
// 	    outs()<<"(declare-fun $"<<iter->getName().str()<<" () Bool)\n";
	    
// 	    outs()<<iter->getName().str()<<" = "<<iter->getNumUses()<<'\n';
	    
	    ///declare transition
// 	    int succ_num = iter->getTerminator()->getNumSuccessors();
// 	    for(int i=0;i<succ_num;i++)
// 	    {
// 		decla_formulas = decla_formulas+ "(declare-fun $"+iter->getName().str()+"_"+iter->getTerminator()->getSuccessor(i)->getName().str()+" () Bool)";
// 		outs()<<"(declare-fun $"<<iter->getName().str()<<"_"<<iter->getTerminator()->getSuccessor(i)->getName().str()<<" () Bool)\n";
// 	    }

	    ///output declare varible
	    for(auto inst_i = iter->begin(),inst_e = iter->end();
		(inst_i != inst_e) && (!inst_i->isTerminator());
		inst_i++)
	    {

		string s;
		///Integer bitwith are i1 i2 i4 i8 i16 i32 ...
		if(inst_i->getType()->isIntegerTy())
		{
		    unsigned int bitwith = inst_i->getType()->getIntegerBitWidth();
		    if(bitwith > 1)
		    {
			s = "(declare-fun $"+inst_i->getName().str()+" () (_ BitVec "+InttoString(bitwith)+"))";
		    }else
		    {
			s = "(declare-fun $"+inst_i->getName().str()+" () Bool)";
		    }
		    
// 		    if(bitwith==1)
// 		    {
// 			s = "(declare-fun $"+inst_i->getName().str()+" () (_ BitVec 1))";
// 		    }else if(bitwith<=64)
// 		    {
// 		    ///create Int varible , the following note is the SMT-libv2 format
// 		    ///(declare-fun x () (_ BitVec 64))
// 			s = "(declare-fun $"+inst_i->getName().str()+" () (_ BitVec 64) )";
// 		    }else
// 		    {
// 			outs()<<"the BitVector's width is larger than the size of Int...\n";
// 		    }
		    
		}else if(!inst_i->hasName() && (inst_i->getOpcode() == Instruction::Call))
		{
		    continue;
		}else
		{
		    inst_i->dump();
		    outs()<<";this type of varible had not defined ...\n";
		}
		decla_formulas = decla_formulas+s;
		outs()<<s<<'\n';
	    }
	}
	
	
	const char *k = decla_formulas.c_str();
// 	outs()<<k<<'\n';
	formula = msat_from_smtlib2(env,k);
	assert(!MSAT_ERROR_TERM(formula));
	res = msat_assert_formula(env,formula);
	assert(res == 0);
	
    }
    
    void newInterpreter::assertVariable()
    {
	string full_formula;
	string assert_formula;

// 	full_formula = full_formula + latch_cond_formula;
// 	outs()<<latch_cond_formula<<'\n';
	
	pdt->runOnFunction(*func);
	DominatorTree dt = dta->run(*func);
	domtree = &dt;
	runToposort(*func);
	
	for (iplist<BasicBlock>::iterator iter = func->getBasicBlockList().begin();
            iter != func->getBasicBlockList().end();
            iter++)
	{
	    
	    BasicBlock *basicblock = &(*iter);

	    ///assert active
// 	    if(basicblock->getNumUses() > 1)
// 	    {
// 		string s = "(assert (= $"+basicblock->getName().str()+" (or ";
// 		for(BasicBlock *pred : predecessors(basicblock))
// 		{
// 		    string transition_name = "$"+pred->getName().str()+"_"+basicblock->getName().str();
// 		    s = s + transition_name + " ";
// 		}
// 		s = s + ") ) )";
// 		outs()<<s<<'\n';
// 		full_formula = full_formula + s ;
// 	    }else if(basicblock->getNumUses() == 1)
// 	    {
// 		string s = "(assert (= $"+basicblock->getName().str()+" $"+basicblock->getSinglePredecessor()->getName().str()+"_"+basicblock->getName().str()+") )";
// 		outs()<<s<<'\n';
// 		full_formula = full_formula + s ;
// 	    }else if(basicblock->getNumUses()==0 && basicblock->getName().str()=="entry")
// 	    {
// 		string s = "(assert $entry)";
// 		outs()<<s<<'\n';
// 		full_formula = full_formula + s ;
// 	    }else
// 	    {
// 		outs()<<"the function has many entry...\n";
// 	    }
	    
	    
	    ///assert varible 
	    for(auto inst_i = basicblock->begin(),inst_e = basicblock->end();
		(inst_i != inst_e) && (!inst_i->isTerminator());
		inst_i++)
	    {
		switch(inst_i->getOpcode())
		{
		    case Instruction::Add:
		    {
			string s = "(assert (= $"+inst_i->getName().str()+" (bvadd ";
			string tail = ")))";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s<<'\n';
			break;
		    }
		    case Instruction::Sub:
		    {
			string s = "(assert (= $"+inst_i->getName().str()+" (bvsub ";
			string tail = " )))";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s<<'\n';
			break;
		    }
		    case Instruction::Mul:
		    {
			string s = "(assert (= $"+inst_i->getName().str()+" (bvmul ";
			string tail = " )))";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s<<'\n';
			break;
		    }
		    case Instruction::PHI:
		    {
			PHINode* phi = dyn_cast<PHINode>(inst_i);
			if(!phi)
			    break;
			
			string s;
			unsigned int Num = phi->getNumOperands();
			
			//只有一个操作数的phi节点
			if(Num == 1)
			{
			    s = "(assert (= $"+phi->getName().str()+" "+calculateVarible(phi->getIncomingValue(0))+"))";
			    full_formula = full_formula + s;
			    outs()<<s<<'\n';
			    break;
			}
			
			vector<string> storeCmp;
			BasicBlock* domPhi = domtree->getNode(basicblock)->getIDom()->getBlock();
// 			outs()<<basicblock->getName()<<"  ---  "<<domPhi->getName()<<'\n';
			string ts;
			for(unsigned int n=0;n<Num-1;n++)
			{
			    BasicBlock* incomingBB = phi->getIncomingBlock(n);
			    RoadInfo info;
			    info.fullstr="";
			    info.OneRoad=0;
			    if(incomingBB->getTerminator()->getNumSuccessors()>1)
			    {
				BranchInst* terBr = dyn_cast<BranchInst>(incomingBB->getTerminator());
				if(terBr->getSuccessor(0)==basicblock)
				{
				    info.fullstr = calculateVarible(terBr->getCondition());
				}
				else
				{
				    info.fullstr = "(not "+calculateVarible(terBr->getCondition())+")";
				}
				info.OneRoad++;
			    }
			    if(incomingBB == latch)
			    {
				info.fullstr = "(not "+latch_cond_formula+")";
				info.OneRoad++;
			    }
			    DomTrace(domPhi,incomingBB,basicblock,info);
			    if(info.OneRoad>1)
			    {
				info.fullstr = " (and "+info.fullstr+") ";
			    }
// 			    outs()<<"phi cmp: "<<info.fullstr<<'\n';
			    s = s + "(ite " + info.fullstr + calculateVarible(phi->getIncomingValue(n));
			    ts=ts+")";
			}
			s = "(assert (= $"+phi->getName().str()+" "+s+calculateVarible(phi->getIncomingValue(Num-1))+ts+"))";
			outs()<<s<<'\n';
			full_formula = full_formula + s;


// 			for(unsigned int n=0;n<Num;n++)
// 			{
// 			    BasicBlock* incomingBB = phi->getIncomingBlock(n);
// 			    BasicBlock* RTraceHead = phi->getIncomingBlock(n);
// 			    BasicBlock* RTraceTail = basicblock;
// 			    int x = bb2int[incomingBB];
// 			    int y = bb2int[domPhi];
// // 			    outs()<<"x = "<<x<<"   y = "<<y<<'\n';
// 				
// 			    while(x>y)
// 			    {
// 			   
// 				if((x-1>0) && pdt->dominates(incomingBB,int2bb[x-1]))
// 				{
// 				    RTraceHead = int2bb[x-1];
// 				    RTraceTail = RTraceHead;
// 				}
// 				x--;
// 			    }
// 			    
// 			    RoadInfo info;
// 			    info.OneRoad = false;
// 			    TraceCMPs(domPhi,RTraceHead,RTraceTail,incomingBB,basicblock,"",info);
// 			    if(info.OneRoad)
// 			    {
// 				storeCmp.push_back("(or "+info.fullstr+")");
// // 				    outs()<<"(or "<<info.fullstr<<")\n";
// 			    }
// 			    else
// 			    {
// 				storeCmp.push_back(info.fullstr);
// // 				    outs()<< info.fullstr<<"\n";
// 			    }
// 				
// 			}
// 			    
// 			auto RI = storeCmp.begin();
// 			string ts;
// 			for(unsigned int n=0;n<Num-1;n++)
// 			{
// 			    s = s + "(ite " + (*RI)+" "+calculateVarible(phi->getIncomingValue(n));
// 			    RI++;
// 			    ts=ts+")";
// 			}
// 			s = "(assert (= $"+phi->getName().str()+" "+s+calculateVarible(phi->getIncomingValue(Num-1))+ts+"))";
// // 			outs()<<"phi:\n"<<s<<'\n';
// 			outs()<<s<<'\n';
// 			full_formula = full_formula + s;

			break;
		    }
		    case Instruction::ICmp:
		    {
			
			ICmpInst *icmpInst = dyn_cast<ICmpInst>(inst_i);
			if(!icmpInst)
			{
			    break;
			}
			///deal the unsigned int comparation
			switch (icmpInst->getPredicate() )
			{
			    case CmpInst::ICMP_EQ:
			    {
				string s = "(assert (= $"+icmpInst->getName().str()+" (= "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+")))";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_NE:
			    {
				string s = "(assert (= $"+icmpInst->getName().str()+" (not (= "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+"))))";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_UGT:
			    {
				string s = "(assert (= $"+icmpInst->getName().str()+" (bvugt "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+")))";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_UGE:
			    {
				string s = "(assert (= $"+icmpInst->getName().str()+" (bvuge "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+")))";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_ULT:
			    {
				string s = "(assert (= $"+icmpInst->getName().str()+" (bvult "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+")))";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_ULE:
			    {
				string s = "(assert (= $"+icmpInst->getName().str()+" (bvule "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+")))";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_SGT:
			    {
				string s = "(assert (= $"+icmpInst->getName().str()+" (bvsgt "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+")))";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_SGE:
			    {
				string s = "(assert (= $"+icmpInst->getName().str()+" (bvsge "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+")))";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_SLT:
			    {
				string s = "(assert (= $"+icmpInst->getName().str()+" (bvslt "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+")))";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    case CmpInst::ICMP_SLE:
			    {
				string s = "(assert (= $"+icmpInst->getName().str()+" (bvsle "+calculateVarible(icmpInst->getOperand(0))+" "+calculateVarible(icmpInst->getOperand(1))+")))";
				full_formula = full_formula + s;
				outs()<<s<<'\n';
				break;
			    }
			    default:
			    {
				errs()<< "this Function "<<icmpInst->getName() <<" will be realize in the future ..."<< '\n';
			    }
			}
			break;
		    }
		    case Instruction::SExt:
		    {
			SExtInst* sextInst = dyn_cast<SExtInst>(inst_i);
			assert(sextInst);
			unsigned int lbitwidth = sextInst->getType()->getIntegerBitWidth();
			unsigned int rbitwidth = sextInst->getOperand(0)->getType()->getIntegerBitWidth();
			if(rbitwidth > 1)
			{
			    string s = "(assert (= $"+sextInst->getName().str()+" ((_ sign_extend "+InttoString(lbitwidth-rbitwidth)+") "+calculateVarible(sextInst->getOperand(0))+")))";
			    full_formula = full_formula + s;
			    outs()<<s<<'\n';
// 			    string ss = "(assert (= $"+sextInst->getName().str()+" ((_ sign_extend "+InttoString(lbitwidth-rbitwidth)+") "+calculateVarible(sextInst->getOperand(0))+")))";
// 			    outs()<<ss<<'\n';
			    break;
			}else
			{
			    string s = "(assert (= $"+sextInst->getName().str()+" (ite "+calculateVarible(sextInst->getOperand(0))
					+" ((_ sign_extend "+InttoString(rbitwidth-lbitwidth)+") (_ bv1 1)) ((_ sign_extend "+InttoString(lbitwidth-rbitwidth)+") (_ bv0 1)))))";
			    full_formula = full_formula + s;
			    outs()<<s<<'\n';
			    break;
			}

// 			if(inst_i->getOperand(0)->getType()->getIntegerBitWidth() == 1)
// 			{
// 			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (ite $"+calculateVarible(inst_i->getOperand(0)) +" (_ bv1 64) (_ bv0 64) ) ) ) )";
// 			    assert_formula = assert_formula +s;
// // 			    outs()<<s<<'\n';
// 			    break;
// 			}else
// 			{
// 			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" "+calculateVarible(inst_i->getOperand(0))+") ) )";
// 			    assert_formula = assert_formula +s;
// // 			    outs()<<s<<'\n';
// 			    break;
// 			}
		    }
		    case Instruction::ZExt:
		    {
			unsigned int lbitwidth = inst_i->getType()->getIntegerBitWidth();
			unsigned int rbitwidth = inst_i->getOperand(0)->getType()->getIntegerBitWidth();
			if(rbitwidth > 1)
			{
			    string s = "(assert (= $"+inst_i->getName().str()+" ((_ zero_extend "+InttoString(lbitwidth-rbitwidth)+") "+calculateVarible(inst_i->getOperand(0))+")))";
			    full_formula = full_formula + s;
			    outs()<<s<<'\n';
			    break;
			}else
			{
			    string s = "(assert (= $"+inst_i->getName().str()+" (ite "+calculateVarible(inst_i->getOperand(0))
					+" ((_ zero_extend "+InttoString(lbitwidth-rbitwidth)+") (_ bv1 1)) ((_ zero_extend "+InttoString(lbitwidth-rbitwidth)+") (_ bv0 1)))))";
			    full_formula = full_formula + s;
			    outs()<<s<<'\n';
			    break;
			}
// 			if(inst_i->getOperand(0)->getType()->getIntegerBitWidth() == 1)
// 			{
// 			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (ite "+calculateVarible(inst_i->getOperand(0)) +" (_ bv1 64) (_ bv0 64) ) ) ) )";
// 			    assert_formula = assert_formula +s;
// // 			    outs()<<s<<'\n';
// 			    break;
// 			}else
// 			{
// 			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" "+calculateVarible(inst_i->getOperand(0))+") ) )";
// 			    assert_formula = assert_formula +s;
// // 			    outs()<<s<<'\n';
// 			    break;
// 			}
		    }
		    case Instruction::Trunc:
		    {
			unsigned int lbitwidth = inst_i->getType()->getIntegerBitWidth();
			unsigned int rbitwidth = inst_i->getOperand(0)->getType()->getIntegerBitWidth();
			if(lbitwidth == rbitwidth)
			{
			    outs()<<"this value trunc is invalid...\n";
			}
			if(lbitwidth > 1)
			{
			    string s = "(assert (= $"+inst_i->getName().str()+" ((_ extract "+InttoString(lbitwidth-1)+" 0) "+calculateVarible(inst_i->getOperand(0))+")))";
			    full_formula = full_formula + s;
			    outs()<<s<<'\n';
			    break;
			}else
			{
			    string s = "(assert (= $"+inst_i->getName().str()+" (ite (= ((_ extract 0 0) "+calculateVarible(inst_i->getOperand(0))+") #b1) true false)))";
			    full_formula = full_formula + s;
			    outs()<<s<<'\n';
			    break;
			}
// 			if(inst_i->getType()->getIntegerBitWidth() == 1)
// 			{
// 			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" (ite (= "+calculateVarible(inst_i->getOperand(0))+" (_ bv0 64) ) true false) ) ) )";
// 			    assert_formula = assert_formula +s;
// // 			    outs()<<s<<'\n';
// 			    break;
// 			}else
// 			{
// 			    string s = "(assert (=> $"+basicblock->getName().str()+" (= $"+inst_i->getName().str()+" "+calculateVarible(inst_i->getOperand(0))+") ) )";
// 			    assert_formula = assert_formula +s;
// // 			    outs()<<s<<'\n';
// 			    break;
// 			}
		    }
		    case Instruction::BitCast:
		    {
			unsigned int lbitwidth = inst_i->getType()->getIntegerBitWidth();
			unsigned int rbitwidth = inst_i->getOperand(0)->getType()->getIntegerBitWidth();
			string s ;
			if(lbitwidth == rbitwidth)
			{
			    s = "(assert (= $"+inst_i->getName().str()+" "+calculateVarible(inst_i->getOperand(0))+" ))";
			}else
			{
			    outs()<<"this value BitCast is invalid...\n";
			}
			full_formula = full_formula + s;
			outs()<<s<<'\n';
			break;
		    }
		    case Instruction::AShr:
		    {
			string s = "(assert (= $"+inst_i->getName().str()+" (bvashr ";
			string tail = " )))";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::LShr:
		    {
			string s = "(assert (= $"+inst_i->getName().str()+" (bvlshr ";
			string tail = " )))";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::Shl:
		    {
			string s = "(assert (= $"+inst_i->getName().str()+" (bvshl ";
			string tail = " )))";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::Xor:
		    {
			string s = "(assert (= $"+inst_i->getName().str()+" (bvxor ";
			string tail = " )))";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::Or:
		    {
			string s = "(assert (= $"+inst_i->getName().str()+" (bvor ";
			string tail = " )))";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::And:
		    {
			string s = "(assert (= $"+inst_i->getName().str()+" (bvand ";
			string tail = " )))";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::SRem:
		    {
			string s = "(assert (= $"+inst_i->getName().str()+" (bvsrem ";
			string tail = " )))";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::URem:
		    {
			string s = "(assert (= $"+inst_i->getName().str()+" (bvurem ";
			string tail = " )))";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::SDiv:
		    {
			string s = "(assert (= $"+inst_i->getName().str()+" (bvsdiv ";
			string tail = " )))";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::UDiv:
		    {
			string s = "(assert (= $"+inst_i->getName().str()+" (bvudiv ";
			string tail = " )))";
			s = s+ calculateVarible(inst_i->getOperand(0),inst_i->getOperand(1))+tail;
			full_formula = full_formula + s;
			outs()<<s+'\n';
			break;
		    }
		    case Instruction::Call:
		    {
			const CallInst *callInst = cast<CallInst>(inst_i);
			ImmutableCallSite cs(callInst);
			auto callTgt = cs.getCalledFunction();
			string func_name = callTgt->getName().str();
			if(callTgt->isDeclaration())
			{
			    if(func_name.find("__VERIFIER_nondet",0) == 0)
			    {
				
			    }else if(func_name.find("__VERIFIER_assert",0) == 0)
			    {
				Value* arg = cast<Value>(cs.arg_begin()) ;
				string s;
				RoadInfo info;
				info.fullstr="";
				info.OneRoad=0;
				DomTrace(int2bb[1],basicblock,info);
				if(info.OneRoad>1)
				{
				    info.fullstr = "(and "+ info.fullstr + ") ";
				}
				end_formula = end_formula + info.fullstr;
// 				const string bbName = "$"+basicblock->getName().str();
// 				const string argName = "$"+arg->getName().str();
// 				s = s+" (and "+bbName+" (= "+argName+" (_ bv0 "+InttoString(arg->getType()->getIntegerBitWidth())+")))";
				if(info.fullstr.empty())
				{
				    s = "(= $"+arg->getName().str()+" (_ bv0 "+InttoString(arg->getType()->getIntegerBitWidth())+")) ";
				}
				else
				{
				    s = "(and "+info.fullstr+"(=> "+info.fullstr+" (= $"+arg->getName().str()+" (_ bv0 "+InttoString(arg->getType()->getIntegerBitWidth())+")))) ";
				}
				assert_formula = assert_formula + s;
// 				outs()<<s+'\n';
// 				verify_formula = verify_formula + s;
// 				assert_cond.push_back(bbName);
// 				assert_cond.push_back(argName);
			    }else if(func_name.find("__VERIFIER_assume",0) == 0)
			    {
				Value* arg = cast<Value>(cs.arg_begin()) ;
				string s;
				s = s+"(assert (= "+calculateVarible(arg)+" (_ bv1 "+InttoString(arg->getType()->getIntegerBitWidth())+")))";
				full_formula = full_formula + s;
				outs()<<s+'\n';
				
			    }else
			    {
				outs()<<"this extend function is not defined\n";
			    }
			}else
			{
			    outs()<<"this function is not extend function, and neet to use inline pass\n";
			}
		    }
		}
		
	    }

	    
	    if(basicblock == latch)
	    {
		string s;
		RoadInfo info;
		info.fullstr="";
		info.OneRoad=0;
		DomTrace(int2bb[1],basicblock,info);
// 		if(info.OneRoad>1)
// 		{
// 		    info.fullstr = "(and "+ info.fullstr + ")";
// 		}
		if(info.OneRoad>1)
		{
		    info.fullstr = "(and " + info.fullstr+") ";
		}
		end_formula = end_formula + info.fullstr;
		if(info.fullstr.empty())
		{
		    s = latch_cond_formula;
		}
		else
		{
		    s = "(and "+info.fullstr+" (=> "+info.fullstr+" "+latch_cond_formula+")) ";
		}
		assert_formula = assert_formula + s;
// 		outs()<<s+'\n';
	    }

	}
	
	//restrick the condition if the program just visit the exit without visit the basicblock whitch has assert formula..
	//This condition is true , but the SMT solver will set the result is SAT.
// 	if(!end_formula.empty())
// 	{
// 	    end_formula = "(assert (=> (not (or " + end_formula+")) false))";
// 	    full_formula = full_formula + end_formula;
// 	    outs()<<end_formula<<'\n';
// 	}
	
	//add the assert formulas into the whole formulas.
	//there is only one the assert formula violate the assert, so use disconjunction operation to link the assert formulas.
	assert_formula = "(assert (or "+assert_formula+"))";
	outs()<<assert_formula<<'\n';
	full_formula = full_formula +assert_formula;
	
	//add assert_formula to SMT solver
	const char *k = full_formula.c_str();
	formula = msat_from_smtlib2(env,k);
	assert(!MSAT_ERROR_TERM(formula));
	res = msat_assert_formula(env,formula);
	assert(res == 0);
	

    }
    
    ///change llvm::Value to std::string
    string newInterpreter::calculateVarible(Value *v )
    {
	string s;
	if(auto cv1 = dyn_cast<Constant>(v))
	{
	    s = calculateConstant(cv1)+" ";
	}else
	{
	    s = "$"+ v->getName().str()+" ";
	}
	return s;
    }
    
    ///change llvm::Value to std::string
    string newInterpreter::calculateVarible(Value *v1 , Value *v2)
    {
	string s;
	if(auto cv1 = dyn_cast<Constant>(v1))
	{
	    s = calculateConstant(cv1)+" ";
	}else
	{
	    s = "$"+v1->getName().str()+" ";
	}
	if(auto cv2 = dyn_cast<Constant>(v2))
	{
	    s = s+calculateConstant(cv2);
	}else
	{
	    s = s+"$"+v2->getName().str();
	}
	return s;
    }
    
    ///change llvm::Constant to std::string 
    string newInterpreter::calculateConstant(Constant *cv)
    {
	string s;
	if(cv->getValueID() == Value::ConstantIntVal )
	{
	    ConstantInt *cInt = cast<ConstantInt>(cv);
	    unsigned int intvalue = cInt->getSExtValue();
	    if(cv->getType()->getIntegerBitWidth() != 1)
	    {
		s = "(_ bv"+InttoString(intvalue)+" "+InttoString(cv->getType()->getIntegerBitWidth())+")";
	    }else
	    {
		bool b = (bool)intvalue;
		if(b)
		{
		    s = "true";
		}else
		{
		    s = "false";
		}
	    }
// 	    outs()<<"\n"<<intvalue<<'\n';
	    
	}else
	{
	    outs()<<"\n;this type of constant had not defined in this function ...\n";
	}
	return s;
    }
    
    ///change Integer to std::string
    string newInterpreter::InttoString(unsigned int v)
    {
	string s;
	std::stringstream ss;
	ss << v;
	ss >> s;
	return s;
    }
    
