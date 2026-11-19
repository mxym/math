// Independent pure graph certificate checks, including every 132..2678 witness.
// No joining formula is used: inspect actual edge subsets in the binary cycle space.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <set>
#include <vector>
using namespace std;
void check(bool b){if(!b){cerr<<"invalid certificate\n";exit(2);}}
using U=uint64_t;
struct Graph{
 int n;vector<pair<int,int>> E; vector<vector<int>> A; vector<vector<int>> id;
 Graph(int n0):n(n0),A(n),id(n,vector<int>(n,-1)){}
 void add(int a,int b){
   check(a>=0&&a<n&&b>=0&&b<n&&a!=b&&id[a][b]<0&&E.size()<63);
   id[a][b]=id[b][a]=E.size();E.emplace_back(a,b); A[a].push_back(b);A[b].push_back(a);
 }
 void topology(){
   for(auto&s:A)check(s.size()==3);
   for(int drop=0;drop<n;drop++){
     int root=drop?0:1; set<int>S{root};vector<int>Q{root};
     while(!Q.empty()){int a=Q.back();Q.pop_back();for(int b:A[a])if(b!=drop && S.insert(b).second)Q.push_back(b);}
     check((int)S.size()==n-1);
   }
 }
 void planar(ifstream&f,int c){
   check(c==n); vector<vector<int>> rot(n); vector<vector<bool>> live(n,vector<bool>(n));
   for(int i=0;i<n;i++){
     for(int j=0,v;j<3;j++){check(bool(f>>v));check(v>=0&&v<n&&id[i][v]>=0&&!live[i][v]);rot[i].push_back(v);live[i][v]=true;}
   }
   int faces=0;
   for(int a=0;a<n;a++)for(int b:rot[a])if(live[a][b]){
     faces++;int s=a,t=b;
     do{check(live[s][t]);live[s][t]=false;auto it=find(rot[t].begin(),rot[t].end(),s);check(it!=rot[t].end());int v=rot[t][(it-rot[t].begin()+1)%3];s=t;t=v;}while(s!=a||t!=b);
   }
   check(n-(int)E.size()+faces==2);
 }
 void nonplanar(ifstream&f,int c){
   check(c>=9&&c<=(int)E.size());vector<set<int>> B(n);set<int> active;
   for(int i=0,a,b;i<c;i++){
      check(bool(f>>a>>b));check(a>=0&&a<n&&b>=0&&b<n&&id[a][b]>=0&&B[a].insert(b).second);B[b].insert(a);
   }
   for(int a=0;a<n;a++)if(B[a].size()==2){
      int x=*B[a].begin(),y=*B[a].rbegin();check(B[x].erase(a)&&B[y].erase(a)&&!B[x].count(y));
      B[x].insert(y);B[y].insert(x);B[a].clear();
   }
   for(int a=0;a<n;a++)if(!B[a].empty()){check(B[a].size()==3);active.insert(a);}
   check(active.size()==6);set<int>L=B[*active.begin()],R;for(int a:active)if(!L.count(a))R.insert(a);
   check(L.size()==3&&R.size()==3);
   for(int a:L)check(B[a]==R);for(int a:R)check(B[a]==L);
 }
 int cycles(){
   // Fundamental cycles on a BFS tree, then Gray code in that basis.
   vector<int>d(n,-1),Q{0}; vector<U> path(n); d[0]=0; U tree=0;
   for(size_t i=0;i<Q.size();i++){int a=Q[i];for(int b:A[a])if(d[b]<0){
      d[b]=d[a]+1;Q.push_back(b);U e=U(1)<<id[a][b];path[b]=path[a]^e;tree|=e;
   }}
   vector<U> basis;for(size_t i=0;i<E.size();i++)if(!((tree>>i)&1)){
      auto [a,b]=E[i];basis.push_back((U(1)<<i)^path[a]^path[b]);
   }
   check(basis.size()<31);U m=0;int tot=0;
   for(unsigned j=1;j<(1u<<basis.size());j++){
     m^=basis[__builtin_ctz(j)]; // At each visited non-isolated vertex exactly two occupied edges.
     int e=__builtin_ctzll(m),a=E[e].first,start=a;U left=m;
     do{int b=-1;for(int w:A[a])if(left&(U(1)<<id[a][w])){b=w;left^=U(1)<<id[a][w];break;}
        check(b>=0);a=b;}while(a!=start);
     tot+=left==0;
   }
   return tot;
 }
};
int main(){
 ifstream f("witnesses.txt");int small,tail;check(bool(f>>small>>tail)&&small==351&&tail==2547);
 set<int>G,P,H;int nP=0,nN=0,maxn=0;
 for(int i=0;i<small+tail;i++){
   int n,k,m,c;char t;check(bool(f>>n>>k>>m));check(4<=n&&n<=28&&m==3*n/2);
   Graph g(n);for(int j=0,a,b;j<m;j++){check(bool(f>>a>>b));g.add(a,b);}g.topology();
   check(bool(f>>t>>c));if(t=='P'){g.planar(f,c);if(i<small)nP++;}else{check(t=='N');g.nonplanar(f,c);if(i<small)nN++;}
   check(g.cycles()==k);
   if(i<small){check(1<=k&&k<=131);G.insert(k);if(t=='P')P.insert(k);}
   else{check(t=='P'&&132<=k&&k<=2678&&H.insert(k).second);maxn=max(n,maxn);}
 }
 string extra;check(!(f>>extra));check(H.size()==2547);
 cout<<"Verified "<<small<<" simple hosts by cycle space, including "<<nP<<" sphere rotations and "<<nN<<" K3,3 subdivisions.\n";
 cout<<"General missing (1..131):";for(int k=1;k<=131;k++)if(!G.count(k))cout<<" "<<k;
 cout<<"\nPlanar missing (1..131):";for(int k=1;k<=131;k++)if(!P.count(k))cout<<" "<<k;
 cout<<"\nAll "<<tail<<" explicit 132..2678 witnesses have verified planarity, cubicity, 2-connectivity, and exact cycle counts; max order "<<maxn<<".\nPASS\n";
}
