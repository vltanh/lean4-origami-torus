// Regression checks for the unit-propagation engine, not a proof oracle.
// g++ -O3 -std=c++17 solver_check_rup_test.cpp -o solver_check_rup_test
#define main certificate_checker_main
#include "solver_check_rup.cpp"
#undef main
#include <random>

void reset_database(int variables){
 N=variables;db.clear();active.clear();watched.clear();units.clear();
 lookup.clear();empty_count=0;watches.assign(2*N+1,{});
}

// Independent fixed-point implementation: scan every active clause.
bool scan_rup(const Clause &candidate){
 vector<int> assignment(N+1);
 for(int literal:candidate){
  int variable=abs(literal), wanted=literal>0?-1:1;
  if(assignment[variable]==-wanted)return true;
  assignment[variable]=wanted;
 }
 bool changed=true;
 while(changed){
  changed=false;
  for(size_t id=0;id<db.size();++id)if(active[id]){
   bool satisfied=false;int count=0,last=0;
   for(int literal:db[id]){
    int value=assignment[abs(literal)]*(literal>0?1:-1);
    if(value==1)satisfied=true;
    if(value==0){++count;last=literal;}
   }
   if(satisfied)continue;
   if(count==0)return true;
   if(count==1){assignment[abs(last)]=last>0?1:-1;changed=true;}
  }
 }
 return false;
}

bool clause_true(const Clause &clause,unsigned values){
 for(int literal:clause)
  if(bool(values&(1u<<(abs(literal)-1)))==(literal>0))return true;
 return false;
}

// Exhaustive semantics is independent of either propagation algorithm.
bool entails(const Clause &candidate){
 for(unsigned values=0;values<(1u<<N);++values){
  if(clause_true(candidate,values))continue;
  bool model=true;
  for(size_t id=0;id<db.size();++id)
   if(active[id]&&!clause_true(db[id],values)){model=false;break;}
  if(model)return false;
 }
 return true;
}

int main(){
 reset_database(2);
 add({1,2});add({-1,2});assert(rup({2}));
 erase_clause({-1,2});assert(!rup({2}));
 add({-1,2});add({-1,2});erase_clause({-1,2});assert(rup({2}));
 erase_clause({-1,2});assert(!rup({2}));assert(rup({1,-1}));
 add({-2});assert(rup({1}));add({-1});assert(rup({}));
 reset_database(1);add({});assert(rup({}));erase_clause({});assert(!rup({}));

 mt19937 random(704267);int comparisons=0,semantic_checks=0;
 for(int trial=0;trial<250;++trial){
  reset_database(2+random()%7);
  for(int step=0;step<80;++step){
   Clause candidate;
   int size=random()%6;
   for(int j=0;j<size;++j){
    int literal=1+random()%N;
    candidate.push_back(random()%2?literal:-literal);
   }
   bool result=rup(candidate);
   assert(result==scan_rup(candidate));++comparisons;
   if(result){assert(entails(candidate));++semantic_checks;}
   // Exercise watch movement, early conflicts, duplicate clauses, and
   // deletions across repeated queries with fresh assignments.
   if(step%2==0 && !candidate.empty())add(candidate);
   if(step%3==0 && !db.empty())erase_clause(db[random()%db.size()]);
   if(step%11==0 && !db.empty())add(db[random()%db.size()]);
  }
 }
 cout<<"PASS "<<comparisons<<" full-scan comparisons and "<<semantic_checks
     <<" exhaustive entailment checks, including state changes\n";
}
