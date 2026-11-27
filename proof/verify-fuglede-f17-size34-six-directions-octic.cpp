#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
constexpr int P=17,K=12,L=255;
const array<int,K>s{0,1,2,3,4,5,6,7,8,9,11,15};
int inv[P],pw[P][11],lambda[K];
int m(int a){a%=P;return a<0?a+P:a;}
struct Profile{array<int,9> c{};int w;};
vector<Profile>A;
using Row=array<vector<int>,K>;
vector<int> bank[9][P][P],wide[9][P],all6;
struct Interp{int e[K][K]{};vector<int>free,det;};
array<Interp,1<<K> M;
long long leaders=0,centers=0,paths[7]={},radon=0,physical=0;
void init(int mask){
 auto&b=M[mask];if(!b.free.empty())return;
 for(int i=0;i<K;i++)((mask>>i)&1?b.free:b.det).push_back(i);
 for(int i:b.det)for(int j:b.free){
  int y=m(lambda[i]*inv[lambda[j]]);
  for(int k:b.free)if(k!=j)y=m(y*(s[i]-s[k])*inv[m(s[j]-s[k])]);
  b.e[i][j]=y;
 }
}
void recur(int d,const Row& R){
 if(d<0){int total=0;for(auto&v:R){if(v.size()!=1)abort();total+=A[v[0]].w;}if(total!=L)return;radon++;
  for(int x=0;x<P;x++)for(int y=0;y<P;y++){int t=-22;for(int i=0;i<K;i++){int u=m(x+s[i]*y),v=0;for(int j=8;j>=0;j--)v=m(v*u+A[R[i][0]].c[j]);t+=v;}if(t!=0&&t!=17)return;}
  physical++;cerr<<"Physical witness "<<physical<<endl;return;
 }
 struct Slot{array<vector<int>,P> bag;int mn[P],small=999;vector<int> value;};
 array<Slot,K> C;
 array<int,K> order; iota(order.begin(),order.end(),0);
 int base=0;
 for(int i=0;i<K;i++){
  auto& c=C[i];fill(c.mn,c.mn+P,999);
  for(int u:R[i]){int v=A[u].c[d];if(!d&&i==0)v=m(v-22);c.bag[v].push_back(u);c.mn[v]=min(c.mn[v],A[u].w);c.small=min(c.small,A[u].w);}
  if(c.small==999)return;
  for(int v=0;v<P;v++)if(c.mn[v]!=999)c.value.push_back(v);
  base+=c.small;
 }
 if(base>L)return;
 sort(order.begin(),order.end(),[&](int i,int j){return C[i].value.size()<C[j].value.size()||(C[i].value.size()==C[j].value.size()&&i<j);});
 int mask=0,n=11-d;
 for(int i=0;i<n;i++)mask|=1<<order[i];
 init(mask);const auto& B=M[mask];int actual[K]={};
 auto go=[&](auto&& self,int k,int amount)->void{
  if(k<n){int i=order[k];for(int u:C[i].value){int v=amount+C[i].mn[u]-C[i].small;if(v<=L){actual[i]=u;self(self,k+1,v);}}return;}
  for(int i:B.det){
   int z=0; for(int j:B.free)z+=B.e[i][j]*actual[j];z%=P;
   if(C[i].mn[z]==999)return;
   amount+=C[i].mn[z]-C[i].small;if(amount>L)return;
   actual[i]=z;
  }
  paths[d]++;
  Row next;for(int i=0;i<K;i++)next[i]=C[i].bag[actual[i]];
  recur(d-1,next);
 };
 go(go,0,base);
}

vector<pair<int,Profile>> centered(int cap,int first,int last){
 vector<pair<int,Profile>> out;
 for(int d=first;d<=last;d++){
  int B[P][P]={},eval[P][P]={};
  for(int i=0;i<=d;i++){
   vector<int> g{1};int den=1;
   for(int j=0;j<=d;j++)if(i!=j){
    vector<int> h(g.size()+1);
    for(size_t k=0;k<g.size();k++){h[k]=m(h[k]-j*g[k]);h[k+1]=m(h[k+1]+g[k]);}
    g.swap(h);den=m(den*(i-j));
   }
   for(int k=0;k<=d;k++)B[i][k]=m(g[k]*inv[den]);
   for(int x=0;x<P;x++){int v=0;for(int k=d;k>=0;k--)v=m(v*x+B[i][k]);eval[x][i]=v;}
  }
  int r=-1,t=-1,D=0;
  for(int i=0;i<=d&&r<0;i++)for(int j=i+1;j<=d;j++){
   D=m(B[i][d-1]*B[j][d]-B[j][d-1]*B[i][d]);
   if(D){r=i;t=j;break;}
  }
  if(r<0)abort();
  const int aD=inv[D];
  vector<int> F;for(int i=0;i<=d;i++)if(i!=r&&i!=t)F.push_back(i);
  int a[P]={},lead=1;
  auto dfs=[&](auto&& self,int i,int W,int sq,int u,int v)->void{
   if(i<(int)F.size()){
    const int k=F[i],lo=max(0,34-W-(P-1-i)*cap),hi=min(cap,34-W);
    for(int z=lo;z<=hi;z++){a[k]=z;self(self,i+1,W+z,sq+z*z,u+z*B[k][d-1],v+z*B[k][d]);}
    return;
   }
   int e=lead-v,x=m(aD*(-u*B[t][d]-e*B[t][d-1])),y=m(aD*(B[r][d-1]*e+B[r][d]*u));
   if(x>cap||y>cap||W+x+y>34)return;
   a[r]=x;a[t]=y;W+=x+y;sq+=x*x+y*y;
   for(int j=d+1;j<P;j++){
    int z=0;for(int k=0;k<=d;k++)z+=eval[j][k]*a[k];z%=P;
    if(z>cap||W+z>34||W+z+(P-1-j)*cap<34)return;
    W+=z;sq+=z*z;
   }
   if(W!=34)return;
   Profile z{};z.w=(sq-68)/2;
   if(z.w<=0||sq%2)abort();
   for(int k=0;k<=d;k++){int x=0;for(int j=0;j<=d;j++)x+=a[j]*B[j][k];z.c[k]=m(x);}
   if(z.c[d]!=lead||z.c[d-1])abort();
   out.push_back({d,z});
  };
  for(int i=0;i<gcd(d,16);i++){dfs(dfs,0,0,0,0,0);lead=m(3*lead);}
 }
 return out;
}
int main(int argc,char**argv){
 int sc0=argc>1?atoi(argv[1]):0,sc1=argc>2?atoi(argv[2]):8;
 for(int x=0;x<P;x++){for(int y=1;y<P;y++)if(x*y%P==1)inv[x]=y;pw[x][0]=1;for(int j=1;j<=10;j++)pw[x][j]=m(x*pw[x][j-1]);}
 for(int i=0;i<K;i++){int v=1;for(int j=0;j<K;j++)if(i!=j)v=m(v*(s[i]-s[j]));lambda[i]=inv[v];}
 int reps[9]={};
 for(const auto& [d,z]:centered(6,6,8)){const auto c=z.c;const int w=z.w;reps[d]++;
  bool seen[P]={};
  for(int a=1;a<P;a++){
   int lead=m(c[d]*pw[a][d]);if(seen[lead])continue;seen[lead]=true;
   for(int h=0;h<P;h++){
    Profile z{};z.w=w;for(int k=d;k>=0;k--){for(int j=d;j>0;j--)z.c[j]=m(z.c[j-1]-h*z.c[j]);z.c[0]=m(c[k]*pw[a][k]-h*z.c[0]);}
    int mass=0,sq=0;
    for(int x=0;x<P;x++){int v=0;for(int j=d;j>=0;j--)v=m(v*x+z.c[j]);if(v>6)abort();mass+=v;sq+=v*v;}
    if(mass!=34||(sq-68)/2!=w)abort();
    int id=A.size();A.push_back(z);
    bank[d][lead][z.c[d-1]].push_back(id);wide[d][lead].push_back(id);if(d==6)all6.push_back(id);
   }
  }
 }
 if(reps[6]!=2||reps[7]!=3||reps[8]!=136||A.size()!=17*(16+48+272))abort();
 for(int sc=sc0;sc<sc1;sc++){
  int scale=pw[3][sc],part=0;
  for(int p0=0;p0<P;p0++)for(int p1=0;p1<P;p1++)for(int p2=0;p2<P;p2++){
   if((p0?p0:(p1?p1:p2))!=1)continue;
   int a[K]={},piv[2]={-1,-1},f[K]={};for(int i=0;i<K;i++){a[i]=m(scale*lambda[i]*(p0+p1*s[i]+p2*pw[s[i]][2]));if(a[i]&&piv[1]<0){if(piv[0]<0)piv[0]=i;else piv[1]=i;}}
   if(piv[1]<0)abort();
   for(int i=0;i<K;i++)f[i]=m(lambda[i]*(s[i]-s[piv[0]])*(s[i]-s[piv[1]]));
   leaders++;part++;
   for(int q0=0;q0<P;q0++)for(int q1=0;q1<P;q1++){
    Row r;
    for(int i=0;i<K;i++){int b=m(f[i]*(q0+q1*s[i]));
     r[i]=a[i]?bank[8][a[i]][b]:(b?wide[7][b]:all6);
    }centers++;recur(6,r);
   }
  }
  cerr<<"scale_index="<<sc<<" leaders="<<part<<" cumulative";
  for(int d=6;d>=0;d--)cerr<<' '<<paths[d];cerr<<" Radon "<<radon<<" physical "<<physical<<endl;
 }
 if(sc0==0&&sc1==8&&(leaders!=2456||centers!=709784||paths[6]!=971106||paths[5]!=338||paths[4]||radon||physical))abort();
 cout<<"leaders="<<leaders<<" centers="<<centers;
 for(int d=6;d>=0;d--)cout<<" d"<<d<<'='<<paths[d];
 cout<<" Radon="<<radon<<" physical="<<physical<<endl;
}
