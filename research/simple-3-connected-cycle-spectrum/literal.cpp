// Independent direct tests on unlabeled-purpose input: only vertex/edge lists,
// target integer and simple graph conditions; no hub, theta or path formula is used.
#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <set>
#include <string>
#include <vector>
using namespace std;
void check(bool x){if(!x){cerr<<"check failed\n";exit(1);}}
unsigned long long count(const vector<vector<int>>&A){
 int n=A.size();vector<bool>seen(n);unsigned long long twice=0;
 for(int s=0;s<n;s++){
  auto dfs=[&](auto&self,int v,int depth)->void{
   for(int w:A[v]){
    if(w==s&&depth>=3){twice++;continue;}
    if(w<=s||seen[w])continue;
    seen[w]=true;self(self,w,depth+1);seen[w]=false;
   }
  };dfs(dfs,s,1);
 }
 check(twice%2==0);return twice/2;
}
void verify3(const vector<vector<int>>&A){
 int n=A.size();check(n>=4);
 // x,y=-1 means no deletion; x==y means one.
 for(int x=-1;x<n;x++)for(int y=x;y<n;y++){
  vector<bool> seen(n);if(x>=0)seen[x]=true;if(y>=0)seen[y]=true;
  int s=0;while(seen[s])s++;
  vector<int>q{s};seen[s]=true;
  while(!q.empty()){int v=q.back();q.pop_back();for(int u:A[v])if(!seen[u]){seen[u]=true;q.push_back(u);}}
  check(find(seen.begin(),seen.end(),false)==seen.end());
 }
}
void checkfile(const string&filename,bool unique){
 ifstream f(filename);check(bool(f));int k,n,m,rows=0,maxn=0;set<int>S;
 while(f>>k){check(bool(f>>n>>m));check(k>=1&&n>=4&&n<=200&&m<=n*(n-1)/2);
  vector<vector<int>>A(n);set<pair<int,int>>E;
  for(int i=0,a,b;i<m;i++){check(bool(f>>a>>b));check(0<=a&&a<b&&b<n);check(E.insert({a,b}).second);A[a].push_back(b);A[b].push_back(a);}
  verify3(A);check(count(A)==(unsigned)k);if(unique)check(S.insert(k).second);
  maxn=max(n,maxn);rows++;
 }
 check(f.eof()&&rows>0);
 cout<<filename<<": "<<rows<<" simple 3-connected graphs checked by direct enumeration; max order "<<maxn<<"\n";
}
int main(){checkfile("core-samples.txt",false);checkfile("residual-graphs.txt",true);}
