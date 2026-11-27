// Independently verify a generated Boolean chamber-coverage RUP trace.
// g++ -O3 -std=c++17 solver_check_rup.cpp -o solver_check_rup
// Do not disable assertions. No solver library is used.
#include <algorithm>
#include <array>
#include <cassert>
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using Clause=vector<int>;
int N=0;
vector<Clause> db;
vector<unsigned char> active;
vector<vector<int>> occ;
vector<int> units;
map<Clause,vector<int>> lookup;
int empty_count=0;
Clause canonical(Clause c){sort(c.begin(),c.end());c.erase(unique(c.begin(),c.end()),c.end());return c;}
void add(Clause c){
 c=canonical(c);int id=db.size();
 for(int x:c){assert(x && abs(x)<=N);occ[x+N].push_back(id);}
 if(c.size()==1)units.push_back(id);
 if(c.empty())++empty_count;
 db.push_back(c);active.push_back(1);lookup[c].push_back(id);
}
bool present(const Clause &c){auto it=lookup.find(canonical(c));return it!=lookup.end()&&!it->second.empty();}
void erase_clause(const Clause &c){
 auto it=lookup.find(canonical(c));if(it==lookup.end()||it->second.empty())return;
 int id=it->second.back();it->second.pop_back();assert(active[id]);active[id]=0;
 if(c.empty())--empty_count;
}
bool rup(const Clause& c){
 if(empty_count)return true;
 vector<signed char> as(N+1);vector<int> queue;queue.reserve(N);
 auto set=[&](int l){int v=abs(l),s=l>0?1:-1;if(as[v]==-s)return false;
  if(as[v]==0){as[v]=s;queue.push_back(l);}return true;};
 for(int l:c)if(!set(-l))return true;
 for(int id:units)if(active[id]&&!set(db[id][0]))return true;
 for(size_t q=0;q<queue.size();++q){
  int f=-queue[q];for(int id:occ[f+N])if(active[id]){
   int u=0,cnt=0;bool sat=false;
   for(int l:db[id]){int v=as[abs(l)]*(l>0?1:-1);if(v==1){sat=true;break;}if(!v){u=l;if(++cnt>1)break;}}
   if(sat||cnt>1)continue;if(cnt==0)return true;if(!set(u))return true;
  }
 }
 return false;
}
int main(int argc,char**argv){
 assert(argc==3);int n=0,expected=0;ifstream f(argv[1]);assert(f);string line;getline(f,line);
 {istringstream s(line);string p,cnf;s>>p>>cnf>>n>>expected;assert(p=="p"&&cnf=="cnf"&&n>0&&expected>=0);N=n+1;occ.resize(2*N+1);}
 int input=0;
 while(getline(f,line)){istringstream s(line);Clause c;int v;bool end=false;
  while(s>>v){if(!v){end=true;break;}assert(abs(v)<=n);c.push_back(v>0?v+1:v-1);}
  assert(end);add(c);++input;
 }
 assert(input==expected);
 // Extend the original formula by the guard and redundant clauses.
 for(int i=2;i<=N;++i)add({1,i});add({1});
 ifstream g(argv[2]);assert(g);int no=0,ni=0,nrup=0,nd=0;bool done=false;
 while(getline(g,line)){
  ++no;if(line.empty())continue;char type=line[0];
  istringstream s(type=='i'||type=='d'?line.substr(1):line);Clause c;int v;bool end=false;
  while(s>>v){if(!v){end=true;break;}assert(abs(v)<=N);c.push_back(v);}assert(end);
  if(type=='d'){erase_clause(c);++nd;continue;}
  // Logged "input" clauses are NOT trusted: require exact presence or RUP.
  if(type=='i'){if(!present(c)&&!rup(c)){cerr<<"bad input "<<no<<" "<<line<<"\n";return 1;}++ni;}
  else if(rup(c)){++nrup;}
  else {cerr<<"non-RUP proof step "<<no<<" "<<line<<"\n";return 1;}
  add(c);if(c.empty()){done=true;break;}
 }
 assert(done);
 cout<<"PASS UNSAT: "<<input<<" original clauses, "<<ni<<" checked input lines, "<<nrup<<" RUP additions, "<<nd<<" deletions\n";
}
