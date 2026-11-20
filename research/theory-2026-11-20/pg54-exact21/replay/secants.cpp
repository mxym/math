#include "common.hpp"
using namespace Q;
const int NN=1365;struct Mask{array<uint64_t,22>w{};inline bool test(int y)const{return (w[y>>6]>>(y%64))&1;}inline void set(int y){w[y>>6]|=1ull<<(y%64);}inline void unset(int y){w[y>>6]&=~(1ull<<(y%64));}bool intersect(const Mask&x)const{uint64_t c=0;for(int j=0;j<22;j++)c|=w[j]&x.w[j];return c;}void orin(const Mask&x){for(int i=0;i<22;i++)w[i]|=x.w[i];}};
struct Tri{uint16_t v[3];};Tri lines[1024][1024];Tri sec(int a,int b){Tri t;for(int j=1;j<=3;j++)t.v[j-1]=id[a^mult[j][b]];return t;}
Mask occ,delta[1024];bitset<1024> adj[1024];int goal;long long nodes,cap;int sol[40];vi bases;
bool comp(int x,int y){auto t=lines[x][y];if(delta[x].intersect(delta[y]))return false;for(int p:t.v)if(occ.test(p)||delta[x].test(p)||delta[y].test(p))return false;return true;}
bool go(bitset<1024> C,int k){
 if(k==goal){vi Z=bases;for(int j=0;j<k;j++)Z.push_back(1024+sol[j]);validate(Z);cout<<"FOUND";for(int x:Z)cout<<" "<<x;cout<<endl;return false;}
 assert(nodes<LLONG_MAX);nodes++;if(int(C.count())<goal-k)return false;
 bitset<1024> U=C;int seq[1024],cols[1024],j=0;
 for(int col=1;U.any();col++){auto V=U;for(int x=V._Find_first();x<1024;x=V._Find_next(x)){seq[j]=x;cols[j++]=col;V&=~adj[x];U.reset(x);}}
 while(j--){if(cols[j]<goal-k)return false;auto x=seq[j];C.reset(x);auto V=C&adj[x];int need=goal-k-1;if(int(V.count())<need)continue;
  for(int y=V._Find_first();y<1024;y=V._Find_next(y))if(!comp(x,y))V.reset(y);
  if(int(V.count())<need)continue;
  auto prev=occ;occ.orin(delta[x]);for(int y=V._Find_first();y<1024;y=V._Find_next(y))for(int p:lines[x][y].v)delta[y].set(p);
  sol[k]=x;if(go(V,k+1))return true;
  for(int y=V._Find_first();y<1024;y=V._Find_next(y))for(int p:lines[x][y].v)delta[y].unset(p);
  occ=prev;
 }return false;
}
int main(int ac,char**av){init();assert(ac==3);int target=atoi(av[2]),hn=atoi(av[1]);for(int i=0;i<1024;i++)for(int j=0;j<i;j++)lines[i][j]=lines[j][i]=sec(1024+i,1024+j);
 string ln;int s=0;while(getline(cin,ln)){s++;istringstream f(ln);vi A;int a;while(f>>a)A.push_back(a);assert(A.size()==hn);validate(A);
 auto aut=isos(A,A);vi orb(1024,-1);vector<vi> O;
 for(int x=1;x<1024;x++)if(orb[x]==-1){bool ok=1;for(int b:A)for(int c:A)for(int j=0;j<4;j++)for(int k=0;k<4;k++)if((mult[j][b]^mult[k][c])==x)ok=0;
  if(!ok){orb[x]=-2;continue;}set<int>t;for(auto&g:aut)t.insert(g[x]);for(int z:t){assert(orb[z]==-1);orb[z]=O.size();}
  O.emplace_back(t.begin(),t.end());}
 sort(O.begin(),O.end(),[](const vi&a,const vi&b){return a.size()!=b.size()?a.size()>b.size():a[0]<b[0];});
 for(int j=0;j<O.size();j++)for(int y:O[j])orb[y]=j;
 for(int o=0;o<(int)O.size();o++){int q=O[o][0];bases=A;bases.push_back(1024);bases.push_back(1024+q);goal=target-bases.size();occ=Mask();for(int p:bases){assert(!occ.test(id[p]));occ.set(id[p]);}
  for(int j=0;j<bases.size();j++)for(int h=0;h<j;h++)for(int v:sec(bases[j],bases[h]).v){assert(!occ.test(v));occ.set(v);}
  bitset<1024>C;for(int v=0;v<1024;v++)if(orb[v]>=o&&orb[v^q]>=o){
   int p=v+1024;delta[v]=Mask();delta[v].set(id[p]);bool ok=!occ.test(id[p]);for(int y:bases)for(int z:sec(y,p).v){ok&=!occ.test(z)&&!delta[v].test(z);delta[v].set(z);}
   if(ok)C.set(v);}
  for(int v=0;v<1024;v++)adj[v].reset();
  for(int x=C._Find_first();x<1024;x=C._Find_next(x))for(int y=C._Find_next(x);y<1024;y=C._Find_next(y))if(orb[x^y]>=o&&comp(x,y)){adj[x].set(y);adj[y].set(x);}
  nodes=0;bool found=go(C,0);
  assert(!found);cout<<"BRANCH "<<hn<<" "<<target<<" "<<s<<" "<<o<<" "<<O.size()<<" "<<nodes<<endl;
 }
 }}
