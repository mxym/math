// Exhaustive bounded cycle census. C++17, standard library; build/run in a fresh directory.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <vector>
#include <unordered_map>
using namespace std;
using UI=uint32_t; using U=uint64_t;
constexpr int N=32; int L=131;
struct G {
 int n=0,k=0,m=0,dup=0; array<pair<unsigned char,unsigned char>,48> E{};
 unsigned char nn[N][3]{}; unsigned char deg[N]{},mat[N][N]{};
 U label[N]{}; UI bits[N]{};
 void add(int a,int b) {
   if(a==b||deg[a]>=3||deg[b]>=3) abort();
   E[m++]={min(a,b),max(a,b)}; nn[a][deg[a]++]=b;nn[b][deg[b]++]=a;
   if(mat[a][b]++) ++dup;
   ++mat[b][a];
   bits[a]|=1u<<b;bits[b]|=1u<<a;
 }
 int dfs(int a,int b,UI used,int budget){
   if(a==b)return 1;
   used|=1u<<a;
   int r=0;
   for(int i=0;i<deg[a];++i){int v=nn[a][i];if((used>>v)&1u)continue;r+=dfs(v,b,used,budget-r);if(r>budget) break;}
   return r;
 }
};
U mix(U z){z=(z^(z>>30))*0xbf58476d1ce4e5b9ULL; z=(z^(z>>27))*0x94d049bb133111ebULL;return z^(z>>31);}
// A distance-layer hash only buckets candidates. A hash match never discards a graph.
U inv(G&g) {
 U A=0;UI level[N];
 for(int s=0;s<g.n;s++){
   UI seen=level[0]=1u<<s; int h=0;U z=0;
   while(level[h]){
     UI reach=0; int d=0,inner=0;
     for(UI S=level[h];S;S&=S-1){int v=__builtin_ctz(S);reach|=g.bits[v];d+=3-__builtin_popcount(g.bits[v]);inner+=__builtin_popcount(g.bits[v]&level[h]);}
     z=mix(z+1+__builtin_popcount(level[h])+64*d+4096*inner);
     level[++h]=reach&~seen;seen|=reach;
   }
   A+=g.label[s]=z;
 }
 return A;
}
// Exact injective backtracking. For every newly matched pair retain only equal
// adjacency multiplicities to every earlier matched vertex.
bool iso(const G&a,const G&b){
 if(a.n!=b.n||a.k!=b.k||a.dup!=b.dup)return false;
 UI p[N]={}; int n=a.n;
 for(int i=0;i<n;i++){for(int j=0;j<n;j++)if(a.label[i]==b.label[j])p[i]|=1u<<j;if(!p[i])return false;}
 auto search=[&](auto&self,UI todo,UI used,UI row[])->bool{
   if(!todo)return true;
   int v=-1,k=999;
   for(UI t=todo;t;t&=t-1){int i=__builtin_ctz(t);int c=__builtin_popcount(row[i]&~used);if(c<k){k=c;v=i; if(k==0)return false;}}
   UI T=todo^(1u<<v);
   for(UI js=row[v]&~used;js;js&=js-1){
     int j=__builtin_ctz(js);
     UI nx[N]={},nu=used|(1u<<j);bool ok=true;
     for(UI t=T;t;t&=t-1){int i=__builtin_ctz(t);UI x=row[i]&~nu;if(a.mat[v][i]==0)x&=~b.bits[j];else {
         x&=b.bits[j]; UI valid=0;for(UI u=x;u;u&=u-1){int z=__builtin_ctz(u);if(a.mat[v][i]==b.mat[j][z])valid|=1u<<z;}x=valid;
       }if(!x){ok=false;break;}nx[i]=x;
     }
     if(ok && self(self,T,nu,nx))return true;
   }
   return false;
 };
 return search(search,(1u<<n)-1,0,p);
}
int main(int argc,char**argv){
 if(argc>1){L=atoi(argv[1]);if(L<3||L>131) return 1;}
 G b;b.n=2;b.k=3;b.add(0,1);b.add(0,1);b.add(0,1);
 vector<G> cur{b};int n=2; set<int> simple;
 ofstream of("simple.txt"); if(!of) return 2;
 while(!cur.empty()){
  vector<G> nxt;unordered_map<U,vector<int>> map;
  long count=0,simp=0,tries=0;
  for(const G&g:cur){
    if(g.dup==0){
      simp++;simple.insert(g.k);
      of<<g.n<<' '<<g.k;
      for(int i=0;i<g.m;i++){auto [u,v]=g.E[i];of<<' '<<(int)u<<','<<(int)v;}of<<'\n';
    }
    if(g.k>=L) continue; // An ear strictly increases the number of cycles.
    UI skipPair[N]={};vector<int> reps;
    for(int u=0;u<g.m;u++){auto [a,b]=g.E[u];if(!((skipPair[a]>>b)&1u)){reps.push_back(u);skipPair[a]|=1u<<b;}}
    for(int iu=0;iu<(int)reps.size();iu++)for(int iv=iu;iv<(int)reps.size();iv++){
      int u=reps[iu],v=reps[iv];auto [a,b]=g.E[u];auto [c,d]=g.E[v];
      // For one endpoint-pair type try the same occurrence, AND two different
      // parallel occurrences if they exist. Permuting identical copies changes no graph.
      int pp=(u==v && g.mat[a][b]>1)?2:1;
      for(int dcase=0;dcase<pp;dcase++){
        int vv=v;
        if(dcase==1){for(vv=u+1;vv<g.m && g.E[vv]!=g.E[u];vv++);if(vv==g.m)abort();}
        G h;h.n=n+2;if(h.n>=N)abort();int x=n,y=n+1;
        for(int i=0;i<g.m;i++)if(i!=u && i!=vv)h.add(g.E[i].first,g.E[i].second);
        if(u==vv){h.add(a,x);h.add(x,y);h.add(y,b);}
        else{h.add(a,x);h.add(x,b);h.add(c,y);h.add(y,d);}
        // Enumerate all x-y paths before adding the ear.
        int budget=L-g.k; int k=h.dfs(x,y,0,budget);
        if(k>budget)continue;
        h.add(x,y);h.k=g.k+k;count++;
        // No look-ahead and no multiple-edge pruning.
        U hash=inv(h); bool found=false;
        auto&bucket=map[hash];for(int i:bucket){tries++;if(iso(h,nxt[i])){found=true;break;}}
        if(!found){bucket.push_back(nxt.size());nxt.push_back(h);}
      }
    }
  }
  fprintf(stderr,"order %d: representatives=%zu simple=%ld accepted child occurrences=%ld iso tests=%ld\n",n,cur.size(),simp,count,tries);
  cur.swap(nxt);n+=2;of.flush(); if(!of) return 3;
 }
 printf("missing general:");for(int i=1;i<=L;i++)if(!simple.count(i))printf(" %d",i);puts("");
}
