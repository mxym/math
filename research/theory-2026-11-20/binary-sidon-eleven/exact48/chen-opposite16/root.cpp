#ifdef NDEBUG
#error "The replay requires assertions to be enabled."
#endif
#include <array>
#include <limits>
#ifndef WIDTH
#define WIDTH 8
#endif
constexpr int CAP=64*WIDTH;

#include <vector>
#include <set>
#include <map>
#include <cstdint>
#include <cstdlib>
#include <cstdio>
#include <cstring>
#include <cassert>
#include <algorithm>
using namespace std;
using W=unsigned long long;
struct B{W a[WIDTH]={}; void set(int i){a[i/64]|=1ULL<<(i%64);}void del(int i){a[i/64]&=~(1ULL<<(i%64));}int first(){for(int i=0;i<WIDTH;i++)if(a[i])return 64*i+__builtin_ctzll(a[i]);return -1;}bool has(int i){return (a[i/64]>>(i%64))&1;}};
int vals[2048],num,ord[2048],indices[2048],N,need,sidon,chosen[100],dep=0; B edges[2048]; long long nodes;
vector<int> inp;int D;long long sols=0;int maxw=-1;int Awt[2048];
void had(int*a){for(int h=1;h<D;h*=2)for(int i=0;i<D;i+=2*h)for(int j=i;j<i+h;j++){int p=a[j],q=a[j+h];a[j]=p+q;a[j+h]=p-q;}}
void record(){
 int inc=1;
 if(maxw>=0){
   vector<int>r;for(int i=0;i<dep;i++)r.push_back(vals[chosen[i]]);sort(r.begin(),r.end());
   for(int x:r)if(x){vector<int>t;for(int y:r)t.push_back(x^y);sort(t.begin(),t.end());if(t<r)return;}
   int b[2048]={};for(int y:r)b[y]=1;had(b);/* No external maximum or spectral filter is assumed here. */
   for(int x:inp)printf("%d ",x);for(int x:r)printf("%d ",x+D);puts("");assert(r.size()>2);inc=r.size(); // translation-stabilizer is trivial for Sidon sets of size >2
 }
 assert(sols<=std::numeric_limits<long long>::max()-inc);sols+=inc;
}
bool solve(B P){
 assert(nodes < std::numeric_limits<long long>::max());++nodes;if(dep>=need){record();return false;}
 int cnt=0;for(auto v:P.a)cnt+=__builtin_popcountll(v);if(dep+cnt<need)return false;int ls[CAP],cs[CAP],sz=0,nc=0;B avail=P;
 while(avail.first()>=0){B Q=avail;nc++;int x;
  while((x=Q.first())>=0){avail.del(x); Q.del(x);ls[sz]=x;cs[sz++]=nc;for(int w=0;w<WIDTH;w++)Q.a[w]&=~edges[x].a[w];}
 }
 while(sz){sz--;if(dep+cs[sz]<need)return false;int x=ls[sz];P.del(x);B Q;
  for(int w=0;w<WIDTH;w++)Q.a[w]=P.a[w]&edges[x].a[w];
  if(sidon)for(int i=0;i<dep;i++)for(int j=0;j<i;j++){int id=indices[vals[x]^vals[chosen[i]]^vals[chosen[j]]];if(id>=0)Q.del(id);}
  chosen[dep++]=x;if(solve(Q))return true;dep--;
 }
 return false;
}
int main(int ac,char**av){assert(ac==4||ac==5);need=atoi(av[1]);D=atoi(av[2]);sidon=atoi(av[3]);int k;vector<int>A;while(scanf("%d",&k)==1)A.push_back(k);inp=A;assert(!A.empty()&&need>=1&&D<=2048);
 if(ac==5){maxw=atoi(av[4]);assert(maxw>=0 && maxw==int(A.size())-need);for(int x:A)Awt[x]=1;had(Awt);
 }
 bool forb[2048]={};for(int a:A)for(int b:A)forb[a^b]=true;memset(indices,-1,sizeof(indices));vector<pair<int,int>>V;
 for(int i=1;i<D;i++)if(!forb[i]){int dg=0;for(int j=1;j<D;j++)dg+=!forb[j]&&!forb[j^i];V.emplace_back(-dg,i);}sort(V.begin(),V.end());vals[0]=0;indices[0]=0;int n=1;for(auto [d,x]:V){indices[x]=n;vals[n++]=x;}
 assert(n<=CAP);B P;for(int i=1;i<n;i++){P.set(i);for(int j=0;j<n;j++)if(!forb[vals[i]^vals[j]])edges[i].set(j);}
 chosen[dep++]=0;solve(P);printf("%lld\n",sols);}
