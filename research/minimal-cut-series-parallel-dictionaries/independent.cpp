// c++ -O2 -std=c++17 independent.cpp -o /tmp/mincut-independent && /tmp/mincut-independent
#include <algorithm>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <set>
#include <vector>
using namespace std;
using G=vector<int>; using I=vector<int>;
void need(bool a, const char*m){if(!a){cerr<<m<<"\n";exit(1);}}
void edge(G&g,int x,int y){need(x!=y,"loop");g[x]|=1<<y;g[y]|=1<<x;}
int lo(int s){return s & -s;} int pos(int bit){return __builtin_ctz((unsigned)bit);}
int flood(const G&g,int allowed,int bit){
 int seen=bit,fr=bit;
 while(fr){int b=lo(fr);fr^=b;int add=g[pos(b)]&allowed&~seen;fr|=add;seen|=add;}return seen;
}
struct St{I glob,clean,sep;};
St calc(const G&g){
 int n=g.size(),N=1<<n;St s{I(N),I(N),I(N)};
 I anyG(N),anyR(N);
 for(int del=0;del<N;++del){
  int live=N-1-del,cc=0,separated=0;
  for(int left=live;left;){int comp=flood(g,live,lo(left));left^=comp;++cc;
    if((live&3)==3 && (comp&3)==1)separated=1;}
  // True for a proper subset iff some immediately preceding mask already
  // contains such a subset. This does not use monotonicity of disconnecting.
  int sg=0,sr=0;for(int left=del;left;left^=lo(left)){int t=del^lo(left);sg|=anyG[t];sr|=anyR[t];}
  s.glob[del]=(cc>1&&!sg);s.clean[del]=(cc==2&&separated&&!sr);
  s.sep[del]=separated;anyG[del]=sg||(cc>1);anyR[del]=sr||separated;
 }
 return s;
}
int count1(const I&v){return accumulate(v.begin(),v.end(),0);}
G capped(G g){edge(g,0,1);return g;}
int remap(int set,const I&m){int y=0;for(;set;set^=lo(set))y|=1<<m[pos(lo(set))];return y;}
struct Pair {G g;I a,b;int w;};
Pair glue(const G&A,const G&B,bool ser){
 int na=A.size(),nb=B.size(),n=na+nb-2+(int)ser,w=n-1;
 Pair p{G(n),I(na),I(nb),w};iota(p.a.begin(),p.a.end(),0);p.a[1]=ser?w:1;
 p.b[0]=ser?w:0;p.b[1]=1;for(int i=2;i<nb;++i)p.b[i]=na-2+i;
 auto add=[&](const G&g,const I&m){for(int i=0;i<(int)g.size();++i)for(int j=0;j<i;++j)if(g[i]>>j&1)edge(p.g,m[i],m[j]);};
 add(A,p.a);add(B,p.b);return p;
}
struct Atom {G g;St s,cap;int c,h,d;};
void insert(vector<Atom>&a,const G&g){auto s=calc(g),c=calc(capped(g));auto k=count1(s.glob);
 a.push_back({g,s,c,k,count1(s.clean),max(k,count1(c.glob))});}
long long pairs=0,nonplan=0,cutCases=0,terminal=0,nonterminal=0,rootOnly=0;
void checkpair(const Atom&A,const Atom&B){
 for(bool ser:{false,true}){
  auto p=glue(A.g,B.g,ser);auto st=calc(p.g),cap=calc(capped(p.g));auto N=st.glob.size();
  I expected(N),local(N),cappedLocal(N);
  auto push=[&](const Atom&X,const I&m){for(int s=0;s<(int)X.s.glob.size();++s){
   local[remap(s,m)]|=X.s.glob[s];cappedLocal[remap(s,m)]|=X.cap.glob[s];
   if(ser)expected[remap(s,m)]|=X.s.clean[s];}};
  push(A,p.a);push(B,p.b);
  if(!ser){for(int x=0;x<(int)A.s.clean.size();++x)if(A.s.clean[x])for(int y=0;y<(int)B.s.clean.size();++y)
   if(B.s.clean[y])expected[remap(x,p.a)|remap(y,p.b)]=1;
  }else{
   int a=(1<<A.g.size())-1-2,b=(1<<B.g.size())-1-1;
   if(flood(A.g,a,lo(a))==a&&flood(B.g,b,lo(b))==b)expected[1<<p.w]=1;
  }
  need(expected==st.clean,"rooted identity as sets, incl clean join condition");
  int c=count1(st.glob),d=max(c,count1(cap.glob));
  if(ser){
    for(int z=0;z<(int)N;++z)if(st.glob[z])need(z==(1<<p.w)||local[z],"unrooted series locality");
    need(c<=A.c+B.c+1&&d<=A.d+B.d+A.h*B.h+A.h+B.h+9,"series counts");
  }else{
    for(auto* sx:{&st,&cap})for(int z=0;z<(int)N;++z)if(sx->glob[z]){
     ++cutCases;if((z&~3)==0){++rootOnly;continue;}
     if(sx->sep[z]){++terminal;need(sx==&st&&expected[z],"crossing roots not a clean product");}
     else{++nonterminal;need(cappedLocal[z],"parallel nonterminal cut not localized");}
    }
    need(d<=A.d+B.d+A.h*B.h+4,"parallel bound");
  }
 }
 ++pairs;
}
int main(){
 vector<Atom> a;
 // Keep one representative per orbit under permutations fixing each terminal.
 for(int n=2;n<=5;++n){set<G> seen;I v(n);iota(v.begin(),v.end(),0);
  for(int mask=0;mask<1<<(n*(n-1)/2);++mask){
   G g(n);int k=0;for(int i=0;i<n;++i)for(int j=0;j<i;++j,++k)if(mask>>k&1)edge(g,i,j);
   if(flood(g,(1<<n)-1,1)!=(1<<n)-1||seen.count(g))continue;
   insert(a,g);do{G m(n);for(int i=0;i<n;++i)m[v[i]]=remap(g[i],v);seen.insert(m);}while(next_permutation(v.begin()+2,v.end()));
  }
 }
 size_t prefix=a.size();
 // K3,3 with same/opposite shores marked, and K5 with two distinct pendant terminals.
 for(auto shore:{I{0,1,2},I{0,2,3}}){G g(6);for(int x:shore){for(int y=0;y<6;++y){
    if(find(shore.begin(),shore.end(),y)==shore.end())edge(g,x,y);}}
  insert(a,g);}
 G g(7);edge(g,0,2);edge(g,1,3);for(int i=2;i<=6;++i)for(int j=2;j<i;++j)edge(g,i,j);insert(a,g);
 for(size_t i=0;i<a.size();++i)for(size_t j=0;j<a.size();++j){checkpair(a[i],a[j]);if(i>=prefix||j>=prefix)++nonplan;}
 cout<<"Rooted connected isomorphism types through five vertices: "<<prefix<<"\n";
 cout<<"Ordered pairs checked after three additional nonplanar seeds: "<<pairs<<" (explicit nonplanar seed in "<<nonplan<<")\n";
 cout<<"Parallel cut instances, both uncapped/capped: "<<cutCases<<" ; root-only "<<rootOnly<<", roots split + interior cut "<<terminal<<", localized interior cut "<<nonterminal<<"\n";
 cout<<"PASS: direct inclusion-minimal sets, exact clean recurrences and capped/global bounds\n";
 // Families with an explicit embedding, so no planarity oracle. Begin with the
 // k-bipyramid, delete any subset of ring edges, and optionally subdivide the
 // remaining triangular faces by a single stellar insertion. Construct the
 // cofacial graph from the resulting faces, not from the cuts.
 long long embeddings=0,largeCuts=0,longCuts=0;
 for(int k=3;k<=9;++k)for(int ring=0;ring<(1<<k);++ring)for(int stellar:{-1,0,1}){
  G graph(k+2);vector<I> faces;
  for(int i=0;i<k;++i){int u=i+2,v=2+(i+1)%k;edge(graph,0,u);edge(graph,1,u);
   if(ring>>i&1){edge(graph,u,v);faces.push_back({0,u,v});faces.push_back({1,v,u});}
   else faces.push_back({0,u,1,v});}
  if(stellar>=0){int f=-1;for(int i=0;i<(int)faces.size();++i)if(faces[i].size()==3&&faces[i][0]==stellar){f=i;break;}
   if(f<0)continue;
   auto tri=faces[f];faces.erase(faces.begin()+f);
   int q=graph.size();graph.push_back(0);for(int i=0;i<3;++i){edge(graph,q,tri[i]);faces.push_back({q,tri[i],tri[(i+1)%3]});}}
  G latch(graph.size());for(auto&f:faces)for(int u:f)for(int v:f)if(u<v)edge(latch,u,v);
  auto s=calc(graph);for(int z=0;z<(int)s.glob.size();++z)if(s.glob[z]&&__builtin_popcount((unsigned)z)>=3){
   need(flood(latch,z,lo(z))==z,"cofacial cut not connected");
   for(int left=z;left;left^=lo(left))need(__builtin_popcount((unsigned)(latch[pos(lo(left))]&z))==2,"cofacial degree");
   ++largeCuts;if(__builtin_popcount((unsigned)z)>3)++longCuts;}
  ++embeddings;
 }
 cout<<"Explicit 2-connected embeddings in bipyramid deletion/stellar family: "<<embeddings<<"; checked global cuts of size >=3: "<<largeCuts<<" (of size >=4: "<<longCuts<<")\n";
 cout<<"PASS: one-way induced-cycle criterion\n";
}
