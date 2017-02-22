//===- Hello.cpp - Example code from "Writing an LLVM Pass" ---------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements two versions of the LLVM "Hello World" pass described
// in docs/WritingAnLLVMPass.html
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/PassManager.h"
#include <set>
#include <iomanip>
#include "llvm/IR/CFG.h"

using namespace llvm;

#define DEBUG_TYPE "hello"

//STATISTIC(HelloCounter, "Counts number of functions greeted");
/*
namespace {
class Edge {
    public:
      BasicBlock *U;
      BasicBlock *V;
      Edge(BasicBlock*, BasicBlock*);
    
  };

  Edge::Edge(BasicBlock *U, BasicBlock *V) {
    this->U = U;
    this->V = V;
  }

  class Path {
    public:
      BasicBlock *U;
      BasicBlock *V;
      int dist;
      Path(BasicBlock*, BasicBlock*);
      bool operator==(const Path& that) { return this->U == that.U && this->V == that.V; }
  };

  Path::Path(BasicBlock *U, BasicBlock *V) {
    this->U = U;
    this->V = V;
  }

  std::list<Edge> getLoopInfo(Function *F) {
    std::list<Edge> edgeList;
    for (Function::iterator bi = F->begin(), be = F->end(); bi != be; bi++) {
      BasicBlock *BB = &bi;
      //This allows me to see all paths from BB to other Basic Blocks.
      for (succ_iterator pi = succ_begin(BB), e = succ_end(BB); pi != e; ++pi) {
        Edge E(BB, *pi);
        edgeList.push_back(E);
      }
    }
    return edgeList;
  }

  bool functionName(Function *F) {
    errs().write_escaped(F->getName()) << '\n';
    return false;
  }

struct WarshallLoopDetector : public FunctionPass {
    static char ID;
    WarshallLoopDetector() : FunctionPass(ID) {}
    
    virtual bool runOnFunction(Function &F) {
      functionName(&F);
      std::list<Edge> edgeList = getLoopInfo(&F);
      std::list<Path*> paths;
      //Initialize the distance between any 2 points to be at max, 0 for distance to itself.
      errs() << "checkpoint0";
      for (Function::iterator it1 = F.begin(), e1 = F.end(); it1 != e1; it1++) {
        for (Function::iterator it2 = F.begin(), e2 = F.end(); it2 != e2; it2++) {
          Path path(it1, it2);
          path.dist = std::numeric_limits<int>::max();
          paths.push_front(&path);
        }
      } 
      for (Function::iterator it1 = F.begin(); it1 != F.end(); it1++) {
         Path path(it1, it1);
         for (std::list<Path*>::iterator p = paths.begin(); p != paths.end(); p++) {
           if ((*p) == &path) {
             (*p)->dist = 0;
             
           }
         }
         paths.push_back(&path);
      }
      errs() << "checkpoint1"; 
      //Set up edges in the paths
      for (std::list<Edge>::iterator edge_it = edgeList.begin(), e = edgeList.end(); edge_it != e; ++edge_it) {
        Path path(edge_it->U, edge_it->V);
        for (std::list<Path*>::iterator p = paths.begin(); p != paths.end(); p++) {
          if ((*p) == &path) {
            (*p)->dist = 1;    
          }
        }
      }
      errs() << "checkpoint2";
      //Now it's time to find shortest path from all points to every other point.
      Function::iterator i = F.begin(), e1 = F.end();
      Function::iterator j = F.begin(), e2 = F.end();
      Function::iterator k = F.begin(), e3 = F.end();
      for (; k != e3; k++) {
        for (; i != e1; i++) {
          for (; j != e2; j++) {
            Path IJ(i, j);
            Path JK(j, k);
            Path IK(i, k);
            for (std::list<Path*>::iterator P = paths.begin(); P != paths.end(); P++) {
              if ((*P) == &IJ) {
                IJ = *(*P); 
              }
              if ((*P) == &JK) {
                JK = *(*P);
                
              }
              if ((*P) == &IK) {
                IK = *(*P);
              }
            }
            
            if (IK.dist > IJ.dist + IK.dist) {
              IK.dist = IJ.dist + JK.dist;
            }
          }
        }
      }
      errs() << "checkpoint3\n";
      //Now loop detection time
      int numLoops = 0;
      for (Function::iterator BB1 = F.begin(); BB1 != F.end(); BB1++) {
        for (Function::iterator BB2 = F.begin(); BB2 != F.end(); BB2++) {
          if (BB1 == BB2) { continue; }
          Path *to_path;
          Path *from_path;
          for (std::list<Path*>::iterator path = paths.begin(); path != paths.end(); path++) {
            if ((*path)->U == BB1 && (*path)->V == BB2) {
              to_path = *path;
            }
            if ((*path)->V == BB1 && (*path)->U == BB2) {
              from_path = *path;
            }
          }
          errs() << "My blockss: " << BB1->getName() << ", " << BB2->getName() << "\n";
        }
      }
      errs() << '\t' << "Num of Loops with Warshall's Alg: " << numLoops << '\n';
      return false; 
    }
  };
}
*/

namespace {
  // Hello - The first implementation, without getAnalysisUsage.
  struct Hello : public FunctionPass {
    static char ID; // Pass identification, replacement for typeid
    Hello() : FunctionPass(ID) {}
    std::vector<std::vector<bool>> adjacencyMatrix;
    int numBBs;
    std::set<int > loopEntry;
    int totalCycleCount=0, totalCycleCount2=0;
    void DFSUtil(int v, bool *visited, int &cycleFound)
    {
        // Mark the current node as visited and print it
        visited[v] = true;
        //errs()<< v << "visited ";

        // Recur for all the vertices adjacent to this vertex
        for (int j=0;j<numBBs;j++ ) {
            if (!adjacencyMatrix[v][j]) continue;
            if (visited[j] && loopEntry.find(j) == loopEntry.end() ) {
                cycleFound++;
                loopEntry.insert(j);
                //errs()<<" loop header:"<<j<<"  ";
            }
            if (!visited[j])
                DFSUtil(j, visited, cycleFound);

        }
    }
        std::set<BasicBlock*> setOfBBs;
        std::map<BasicBlock*,unsigned int> basicBlockIDmap;
        std::vector<BasicBlock*> basicBlockArray;
    bool runOnFunction(Function &F) override {
        adjacencyMatrix.clear();
        unsigned int basicBlockIDcounter=0;
        setOfBBs.clear();
        basicBlockIDmap.clear();
        basicBlockArray.clear();

        for(Function::iterator bb=F.begin(); bb!=F.end(); ++bb) {
            BasicBlock *thisBB  = &*bb;
            //errs()<<"\n basicblock ::"<<*(thisBB->getFirstNonPHI());
            if (setOfBBs.insert(thisBB ).second == true)  {
                basicBlockIDmap[thisBB]=basicBlockIDcounter++;
                basicBlockArray.push_back(thisBB);
            }
        }
        numBBs = setOfBBs.size();
        for (int i=0;i<numBBs;i++ ){
            std::vector<bool> dummyRow;
            for (int j=0;j<numBBs;j++ ){
                dummyRow.push_back(0);
            }
            adjacencyMatrix.push_back(dummyRow );
        }
        for (auto thisBB:setOfBBs ) {
            const TerminatorInst *TInst = thisBB->getTerminator(); 
            unsigned int thisBBID = basicBlockIDmap[thisBB ];
            //errs()<<"\n "<<thisBBID<<" has successors::";
            for (unsigned index=0, n_succ=TInst->getNumSuccessors(); index<n_succ; ++index) {
                    auto bb_succ = TInst->getSuccessor(index); //identify edge b->a        
                    unsigned int succBBID = basicBlockIDmap[bb_succ];
                    adjacencyMatrix[thisBBID][succBBID] = 1;
                   // errs()<<succBBID<<" ";
            }
        }
           /* errs()<<"\n";
        for (int i=0;i<numBBs;i++ ){
            for (int j=0;j<numBBs;j++ )
                errs()<<" "<<adjacencyMatrix[i][j];
            errs()<<"\n";
        }*/
        bool *visited = new bool[numBBs];
        for (int i=0;i<numBBs;i++ ) visited[i]=0;
        int numCycles=0;
        errs()<<"num:"<<numBBs;
        errs().write_escaped(F.getName()) << '\n'<<"dfs order::";
        loopEntry.clear();
        //errs()<<"\n\n";
        DFSUtil(0,visited,numCycles );
        errs()<<"\n\n\n num cycles::"<<numCycles;
        totalCycleCount+=numCycles;
        errs()<<"\n\n\n Total num DFS cycles::"<<totalCycleCount;
        //return false;
        /*for (int i=0;i<numBBs;i++ ){
            for (int j=0;j<numBBs;j++ )
                errs()<<" "<<adjacencyMatrix[i][j];
            errs()<<"\n";
        }*/

        std::vector<std::vector<int>> warshallMatrix; //=adjacencyMatrix;
        std::vector<std::vector<int>> shortestPathNode; 
        int infWeight = numBBs*numBBs;
        for (int i=0;i<numBBs;i++ ){
            std::vector<int > dummyRow, dummyRow2;
            for (int j=0;j<numBBs;j++ ) {
                if (i==j)dummyRow.push_back(0);
                else dummyRow.push_back( adjacencyMatrix[i][j]?1:infWeight );
                dummyRow2.push_back( adjacencyMatrix[i][j]?0:-1);
            }
            warshallMatrix.push_back(dummyRow);
            shortestPathNode.push_back(dummyRow2);
            //errs()<<"\n";
        }

        for (int k=0;k<numBBs;k++ ) {
            for (int i=0;i<numBBs;i++ ){
                for (int j=0;j<numBBs;j++ ) {
                    //if (adjacencyMatrix[i][j] ) continue;
                    //if (! (adjacencyMatrix[i][k] && adjacencyMatrix[k][j] )) continue;
                    if ((warshallMatrix[i][j] >  (warshallMatrix[i][k] + warshallMatrix[k][j]))){// || (warshallMatrix[i][j] ==-1 && (warshallMatrix[i][k]!=-1 && warshallMatrix[k][j]!=-1)) ) {
                        warshallMatrix[i][j] = (warshallMatrix[i][k] + warshallMatrix[k][j]);
                        shortestPathNode[i][j] = k;
                    }
                }
            }
        }
        errs()<<"\n warshal::\n";
        for (int i=0;i<numBBs;i++ ){
            for (int j=0;j<numBBs;j++ ) {
                if (warshallMatrix[i][j] == infWeight)
                    warshallMatrix[i][j] = -1;
                //errs()<<" "<<warshallMatrix[i][j];
            }
            //errs()<<"\n";
        }/*
        for (int i=0;i<numBBs;i++ ){
            for (int j=0;j<numBBs;j++ )
                errs()<<" "<<shortestPathNode[i][j];
            errs()<<"\n";
        }*/
        /*for (int i=0;i<numBBs;i++ ){
            for (int j=0;j<numBBs;j++ )
                if (warshallMatrix[i][j]&&warshallMatrix[j][i]) 
            errs()<<"\n";
        }*/

        int nCycles = getCycles(warshallMatrix, shortestPathNode,numBBs) ;
        totalCycleCount2+=nCycles;
        errs()<<"\n total warshal cycles="<<totalCycleCount2;
        return false;
    }
    typedef std::vector<std::vector<int>> intMatrix;
    typedef std::set<int> intSetType;
    void getShortestPath(intMatrix shortestPathNode, int src, int dest, intSetType &setCycle){        
        if (shortestPathNode[src][dest] == 0|| src==dest ) return;
        assert(shortestPathNode[src][dest]!=-1);
        setCycle.insert(shortestPathNode[src][dest] );
        getShortestPath(shortestPathNode,src,shortestPathNode[src][dest], setCycle);
        getShortestPath(shortestPathNode,shortestPathNode[src][dest], dest, setCycle );
    }
    int  getCycles(intMatrix warshallMatrix, intMatrix shortestPathNode, int numBBs) {

        std::set<intSetType> setOfAllCycles;
        for (int i=0;i<numBBs;i++ ){
            for (int j=i+1;j<numBBs;j++ ) {
                if (warshallMatrix[i][j]==1 ||warshallMatrix[j][i]==1) {//cycle between i and j
                if (warshallMatrix[i][j]>0 && warshallMatrix[j][i]>0 ) {//cycle between i and j
                    int src,dest;
                    if (warshallMatrix[i][j]>warshallMatrix[j][i] )
                        {src = i; dest=j;}
                    else 
                        {src = j; dest=i;}
                    
                    intSetType setCycle={src,dest };
                    getShortestPath(shortestPathNode,src,dest, setCycle);
                    setOfAllCycles.insert(setCycle);
                }
                }
            }
            //errs()<<"\n";
        }
        
        for (auto setIds: setOfAllCycles ) {
            errs()<<"\n Set is ::";
            for (auto id: setIds ) 
                errs()<<","<<id;

        }
        errs()<<"\n total cycles:"<<setOfAllCycles.size();
        int totalCycles = 0;
        for (auto s: setOfAllCycles ) {
            totalCycles+=checkPredsBB(s );
        }
        errs()<<"\n total multi loop cycles:"<<totalCycles;
        return totalCycles;
        return setOfAllCycles.size();
    }
    int checkPredsBB(intSetType setOfBBs  ){
        int numPredsNotinSet=0;

        for (auto bbId: setOfBBs ) {
            BasicBlock *BB = basicBlockArray[bbId];
            for (pred_iterator PI = pred_begin(BB), E = pred_end(BB); PI != E; ++PI) {
                BasicBlock *pred = *PI;
                int predId = basicBlockIDmap[pred];
                if (setOfBBs.find(predId )== setOfBBs.end() ) {
                    numPredsNotinSet++;
                    break;
                }
            }
        }
        return numPredsNotinSet;

    }
    void getAnalysisUsage(AnalysisUsage &AU) const override {
        AU.setPreservesAll();
        AU.addRequired<DominatorTreeWrapperPass>();
        AU.addRequired<LoopInfoWrapperPass>();
    }
  };
}

char Hello::ID = 0;
static RegisterPass<Hello> X("hello", "Hello World Pass");

namespace {
  // Statistics:: Average, max, min bsic blocks
  //    CFG edges, single entry loops, loop basic blocks, 
  //average dominators 
    struct Hello2 : public FunctionPass {
        static char ID; // Pass identification, replacement for typeid
        Hello2() : FunctionPass(ID) {}
        int min_loop=-1;
        int max_loop=0;
        int avg_loop=0, totalFuncCount=0 ;
        int avg_bb_stat=0,max_bb_stat=0,min_bb_stat=-1 ;
        int avg_loop_stat=0,max_loop_stat=0,min_loop_stat=-1 ;
        int avg_cfg_stat=0,max_cfg_stat=0,min_cfg_stat=-1 ;
        int avg_loopbb_stat=0,max_loopbb_stat=0,min_loopbb_stat=-1 ;
        int avg_doms_stat=0,max_doms_stat=0,min_doms_stat=-1;
        int totalBBCount=0,totalCFGCount=0,totalLoopCount=0,totalLoopBBCount=0;
        int totalOutermostLoopCount=0, totalLoopExitEdgeCount=0, aloopExitC=0;
        float totalDomCount=0;
        template<typename T> 
        T getMin( T varA,  T varB ) {if ( varA<0 || varA > varB)  return varB ; return varA;  }
         template<typename T> 
        T getMax( T varA,  T varB ) {if  ( varA < varB)  return varB; return varA;  }
        //int getMax( int varA,  int varB ) {  varA < varB ? return varB: return varA;  }
        bool runOnFunction(Function &F) override {                                   
            errs()<<"\n Func Name::"<<F.getName();
            int funcBBCount=0,funcCFGCount=0,funcLoopCount=0,funcLoopBBCount=0, funcDomCount=0;
            totalFuncCount++;                                                                
            int backedge_cnt = 0;                                                      
            std::set<BasicBlock*> setOfBBs;
            std::set<BasicBlock*> setOfLoopBBs;
            std::set<Loop*> setOfLoops;

            for(Function::iterator bb=F.begin(); bb!=F.end(); ++bb) {                                                                              
                BasicBlock *tmpB  = &*bb;
                setOfBBs.insert(tmpB );
            }
            //DominatorTreeBase<BasicBlock>* DT;                                         
            //DT = new DominatorTreeBase<BasicBlock>(true);                              
            DominatorTree *DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
            LoopInfo &LI = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
            int num_loops=0;
            /*for (auto loopI = LI.begin(); loopI != LI.end(); loopI++ ){
                num_loops++;
                errs()<<"\n loop:"<<**loopI;
                errs()<<"\n num back edges="<<(*loopI)->getNumBackEdges();
                errs()<<"\n Sub loops inside this loop::"<<(*loopI)->getSubLoops().size();
            }*/
            errs()<<"\n num loops::"<<num_loops;

            for(Function::iterator bb=F.begin(); bb!=F.end(); ++bb) {                                                                              
                for(auto bb_other: setOfBBs ) {
                    if (bb_other != bb && DT->dominates(bb_other,(BasicBlock*)&*bb ) ) 
                        funcDomCount++;
                }
                BasicBlock *thisBB = &*bb;
                bool isLoopBB=0;
                    Loop *l = LI.getLoopFor(thisBB );
                    if (l) {
                        if (l->isLoopExiting(thisBB )) {
                            aloopExitC++;
                        }
                        if (setOfLoops.find(l) == setOfLoops.end() ) {
                        if (LI.getLoopDepth(thisBB)==1 ) 
                            totalOutermostLoopCount++;
                            setOfLoops.insert(l);
                            num_loops++;
                        }
                    }
                if (LI.getLoopDepth(thisBB)!=0 ) {
                    isLoopBB=1;
                }

                if (LI.getLoopFor(thisBB ) && setOfLoopBBs.find(thisBB ) == setOfLoopBBs.end() )  {
                    funcLoopBBCount++;
                    setOfLoopBBs.insert(thisBB );
                }
                funcBBCount++;
                Loop *thisBBLoop = LI.getLoopFor(thisBB );
                const TerminatorInst *TInst = thisBB->getTerminator();                       
                for (unsigned index=0, n_succ=TInst->getNumSuccessors(); index<n_succ; ++index) {
                    funcCFGCount++;
                    auto bb_succ = TInst->getSuccessor(index); //identify edge b->a        
                    if (isLoopBB && !thisBBLoop->contains(bb_succ )) {
                        totalLoopExitEdgeCount++;
                        errs()<<"\n one loop exit cfg"<<*TInst;
                    }
                    if (DT->dominates(bb_succ, &(*bb))) { //if a < b, then it is backedge  
                        backedge_cnt ++;                                                     
                        funcLoopCount++;/*
                        errs()<<"\n funcLoopCount::"<<funcLoopCount;
                        
                           errs()<<"\n This guy ";
                           errs()<<* bb_succ->getFirstNonPHI() ; 
                           errs()<<* bb_succ->getTerminator() ; 
                           errs() << "\n dominates";
                           errs () <<* bb->getTerminator();*/
                    }                                                                      
                }                                                                        
            }                                                                          
            funcLoopCount = num_loops;

            min_bb_stat = getMin(min_bb_stat,funcBBCount);
            max_bb_stat = getMax( max_bb_stat, funcBBCount);
            totalBBCount += funcBBCount;
            min_cfg_stat = getMin(min_cfg_stat,funcCFGCount);
            max_cfg_stat = getMax( max_cfg_stat, funcCFGCount);
            totalCFGCount += funcCFGCount;
            min_loop_stat = getMin(min_loop_stat,funcLoopCount);
            max_loop_stat = getMax( max_loop_stat, funcLoopCount);
            totalLoopCount += funcLoopCount;
            min_loopbb_stat = getMin(min_loopbb_stat,funcLoopBBCount);
            max_loopbb_stat = getMax( max_loopbb_stat, funcLoopBBCount);
            totalLoopBBCount += funcLoopBBCount;
            //errs()<<"\n total dom count before avf::"<<funcDomCount;
            totalDomCount += funcDomCount;
            //errs()<<"\n total dom count aftere avf::"<<totalDomCount;

            if(backedge_cnt > max_loop) {                                      
                max_loop = backedge_cnt;                                         
            }                                                                          
            if(backedge_cnt < min_loop || min_loop == -1) {                                      
                min_loop = backedge_cnt;                                         
            }                                                                          
            avg_loop = (avg_loop*totalFuncCount+backedge_cnt)/totalFuncCount;      
            errs()<<"\n total loop count::"<<totalLoopCount;
            errs()<<"\n func count:"<<totalFuncCount;
            errs() <<"\n The number of loops in all functions in the input C file: "<<totalLoopCount;
            errs()<< "\n The number of loops that are outermost loops: "<<totalOutermostLoopCount;
            errs()<< "\n The total number of loop exit CFG edges for all loops: "<<totalLoopExitEdgeCount;
            errs()<< "\n The total number of loop exit CFG edges for all loops: "<<aloopExitC;
            /*errs() << "BackEdgeCnt: ";                                                 
              errs().write_escaped(F.getName()) << '\n';                                 
              errs() << "backedge_cnt: " << backedge_cnt << '\n';                        */


            return false;                                                              
        }                                                                            

        bool doFinalization(Module &M) override {                                    
            float avg_bb = totalBBCount/totalFuncCount;
            float avg_cfg = totalCFGCount/totalFuncCount;
            float avg_loop = totalLoopCount/totalFuncCount ;
            float avg_loopbb = totalLoopBBCount/totalFuncCount ;
            float avg_dom = totalDomCount/totalBBCount ;
            errs() << "\n Average, Maximum, Minimum number of basic blocks inside functions: " <<avg_bb  << ", "<< max_bb_stat<<", "<<min_bb_stat<<"\n";
            errs() << "\n Average, Maximum, Minimum number of CFG edges inside functions: " << avg_cfg << ", "<<max_cfg_stat<<", "<<min_cfg_stat<<"\n";
            errs() << "\n Average, Maximum, Minimum number of loops inside functions: " << avg_loop<< ", "<<max_loop_stat<<", "<<min_loop_stat<<"\n";
            errs() << "\n Average, Maximum, Minimum number of loop basic blocks inside functions: " << avg_loopbb << ", "<<max_loopbb_stat<<", "<<min_loopbb_stat<<"\n";
            errs() << "\n Average number of dominators for a basic blocks across all functions: " << avg_dom  <<"\n";
            return false;                                                              
        }                                                                            

        // We don't modify the program, so we preserve all analyses.
        void getAnalysisUsage(AnalysisUsage &AU) const override {
            AU.setPreservesAll();
            AU.addRequired<DominatorTreeWrapperPass>();
            AU.addRequired<PostDominatorTree>();
            AU.addRequired<LoopInfoWrapperPass>();
        }

    };
}
char Hello2::ID = 0;
static RegisterPass<Hello2>
Y("hello2", "Hello World Pass (with getAnalysisUsage implemented)");

//namespace {
//  // Statistics:: Average, max, min bsic blocks
//  //    CFG edges, single entry loops, loop basic blocks, 
//  //average dominators 
//    struct FindCycles : public FunctionPass {
//        static char ID; // Pass identification, replacement for typeid
//        FindCycles() : FunctionPass(ID) {}
//        bool runOnFunction(Function &F) override {                                   
//
//            for(Function::iterator bb=F.begin(); bb!=F.end(); ++bb) {                                                                              
//                BasicBlock *tmpB  = &*bb;
//                setOfBBs.insert(tmpB );
//            }
//            //DominatorTreeBase<BasicBlock>* DT;                                         
//        }                                                                          
//
//            min_bb_stat = getMin(min_bb_stat,funcBBCount);
//            max_bb_stat = getMax( max_bb_stat, funcBBCount);
//            totalBBCount += funcBBCount;
//            min_cfg_stat = getMin(min_cfg_stat,funcCFGCount);
//            max_cfg_stat = getMax( max_cfg_stat, funcCFGCount);
//            totalCFGCount += funcCFGCount;
//            min_loop_stat = getMin(min_loop_stat,funcLoopCount);
//            max_loop_stat = getMax( max_loop_stat, funcLoopCount);
//            totalLoopCount += funcLoopCount;
//            min_loopbb_stat = getMin(min_loopbb_stat,funcLoopBBCount);
//            max_loopbb_stat = getMax( max_loopbb_stat, funcLoopBBCount);
//            totalLoopBBCount += funcLoopBBCount;
//            //errs()<<"\n total dom count before avf::"<<funcDomCount;
//            totalDomCount += (funcDomCount/setOfBBs.size());
//            //errs()<<"\n total dom count aftere avf::"<<totalDomCount;
//
//            if(backedge_cnt > max_loop) {                                      
//                max_loop = backedge_cnt;                                         
//            }                                                                          
//            if(backedge_cnt < min_loop || min_loop == -1) {                                      
//                min_loop = backedge_cnt;                                         
//            }                                                                          
//            avg_loop = (avg_loop*totalFuncCount+backedge_cnt)/totalFuncCount;      
//            /*errs() << "BackEdgeCnt: ";                                                 
//              errs().write_escaped(F.getName()) << '\n';                                 
//              errs() << "backedge_cnt: " << backedge_cnt << '\n';                        */
//
//
//            return false;                                                              
//        }                                                                            
//
//        bool doFinalization(Module &M) override {                                    
//            float avg_bb = totalBBCount/totalFuncCount;
//            float avg_cfg = totalCFGCount/totalFuncCount;
//            float avg_loop = totalLoopCount/totalFuncCount ;
//            float avg_loopbb = totalLoopBBCount/totalFuncCount ;
//            float avg_dom = totalDomCount/totalFuncCount ;
//            errs() << "\n Average, Maximum, Minimum number of basic blocks inside functions: " <<avg_bb  << ", "<< max_bb_stat<<", "<<min_bb_stat<<"\n";
//            errs() << "\n Average, Maximum, Minimum number of CFG edges inside functions: " << avg_cfg << ", "<<max_cfg_stat<<", "<<min_cfg_stat<<"\n";
//            errs() << "\n Average, Maximum, Minimum number of loops inside functions: " << avg_loop<< ", "<<max_loop_stat<<", "<<min_loop_stat<<"\n";
//            errs() << "\n Average, Maximum, Minimum number of loop basic blocks inside functions: " << avg_loopbb << ", "<<max_loopbb_stat<<", "<<min_loopbb_stat<<"\n";
//            errs() << "\n Average number of dominators for a basic blocks across all functions: " << avg_dom  <<"\n";
//            errs() <<"\n The number of loops in all functions in the input C file: "<<totalLoopCount;
//            //errs()<< "\n The number of loops that are outermost loops: "<<totalOutermostLoopCount;
//            //errs()<< "\n The total number of loop exit CFG edges for all loops: "<<totalLoopExitEdgeCount;
//            return false;                                                              
//        }                                                                            
//
//        // We don't modify the program, so we preserve all analyses.
//        void getAnalysisUsage(AnalysisUsage &AU) const override {
//            AU.setPreservesAll();
//            AU.addRequired<DominatorTreeWrapperPass>();
//            AU.addRequired<LoopInfoWrapperPass>();
//        }
//
//    };
//}
//char FindCycles::ID = 0;
//static RegisterPass<FindCycles>
//Z("find-loops", "Find MultiEntry Loops");

