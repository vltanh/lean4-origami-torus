#include <bits/stdc++.h>
using namespace std;
int n,m; vector<vector<int>> c; long long nodes=0; vector<int> asn, trail;
int val(int l){return l>0?asn[l]:-asn[-l];}
void setl(int l){asn[abs(l)]=(l>0?1:-1);trail.push_back(abs(l));}
void undo(size_t k){while(trail.size()>k){asn[trail.back()]=0;trail.pop_back();}}
vector<int> decisions;
bool solve(){
 ++nodes;size_t k=trail.size();
 while(true){bool change=false;for(auto &cl:c){int cnt=0,last=0;bool sat=false;for(int l:cl){int v=val(l);if(v==1){sat=true;break;} if(v==0){cnt++;last=l;}} if(sat)continue;if(cnt==0){undo(k);return false;}if(cnt==1){setl(last);change=true;}}if(!change)break;}
 vector<long long> score(n+1);bool any=false;
 for(auto &cl:c){int cnt=0;bool sat=false;for(int l:cl){int v=val(l);if(v==1){sat=true;break;}if(!v)cnt++;}if(sat)continue;any=true;long long w=1LL<<(20-min(cnt,20));for(int l:cl)if(!val(l))score[abs(l)]+=w;}
 if(!any)return true;
 int v=0;for(int i=1;i<=n;i++)if(!asn[i]&&score[i]>score[v])v=i;
 size_t a=trail.size();
 for(int l:{v,-v}){setl(l);decisions.push_back(l);if(solve())return true;decisions.pop_back();undo(a);}
 undo(k);return false;
}
int main(){string s;cin>>s>>s>>n>>m;c.resize(m);asn.resize(n+1);for(auto &cl:c){int l;while(cin>>l&&l)cl.push_back(l);}bool b=solve();cout<<(b?"SAT":"UNSAT")<<" nodes "<<nodes<<endl;}
