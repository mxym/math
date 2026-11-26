#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <numeric>
#include <utility>
#include <vector>

using namespace std;
constexpr int q=8, mod=43, N=262144, chunk=4096;
int mul(int x){return (x<<1)^((x&4)?11:0);}
constexpr int weights[q][q]={
 {40,40,40,40,40,40,40,40},
 {12,39,2,38,38,30,15,27},
 {12,30,39,38,2,27,38,15},
 {12,15,27,39,30,38,2,38},
 {12,27,30,2,39,15,38,38},
 {12,2,38,15,38,39,27,30},
 {12,38,15,30,27,38,39,2},
 {12,38,38,27,15,2,30,39}
};
struct Word {int sum,rot,mul; array<int,6>a;};
Word words[N];
int phase[42]={1,3,9,27,38,28,41,37,25,32,10,30,4,12,36,22,23,26,35,19,14,42,40,34,16,5,15,2,6,18,11,33,13,39,31,7,21,20,17,8,24,29}, inv[43], delta[chunk], advance_state[chunk][q], coeff[chunk][q];

void setup(){
 for(int j=1;j<mod;j++){for(int i=1;i<mod;i++)if(i*j%mod==1)inv[j]=i; assert(inv[j]);}
 for(int a=0;a<q;a++)for(int t=0;t<q;t++)assert(weights[a][t]==weights[mul(a)][mul(t)]);
 for(int i=0;i<N;i++){
  Word &w=words[i];int d=i,p=1;
  for(int k=0;k<6;k++){int a=d%q;d/=q;w.a[k]=a;w.mul+=mul(a)*p;w.sum^=a;p*=q;}
  w.sum%=q;w.rot=i/q+w.a[0]*(N/q);
 }
 for(int j=0;j<chunk;j++){
  int d=j;array<int,4>a{};
  for(int k=0;k<4;k++){a[k]=d%q;d/=q;}
  delta[j]=a[0]^a[1]^a[2]^a[3];
  for(int x=0;x<q;x++){
   int t=x,c=1;
   for(int u:a){c=c*weights[u][t]%mod;t^=u;}
   coeff[j][x]=c;advance_state[j][x]=t;
  }
 }
}

int trace(int i,int j){
 const auto &a=words[i].a,&b=words[j].a; int f[3];
 for(int t=0;t<3;t++)f[t]=a[2*t]+q*b[2*t]+64*a[2*t+1]+512*b[2*t+1];
 if((delta[f[0]]^delta[f[1]]^delta[f[2]]))return 0;
 int sum=0;
 for(int x=0;x<q;x++){
  int y=advance_state[f[0]][x],z=advance_state[f[1]][y];
  sum+=coeff[f[0]][x]*coeff[f[1]][y]*coeff[f[2]][z];
 }
 return sum%mod;
}

using Orbit=vector<pair<int,int>>;
struct Basis {vector<int> reps;vector<Orbit> vec;};
Basis eigenspace(int charge,int j,int k){
 vector<bool> done(N);Basis B;
 for(int v=0;v<N;v++){
  if(words[v].sum!=charge||done[v])continue;
  Orbit orb;bool ok=true;
  for(int m=0,w=v;m<(charge==0?7:1);m++,w=words[w].mul)
   for(int r=0,z=w;r<6;r++,z=words[z].rot){
    done[z]=true;int c=phase[(420-7*j*r-6*k*m)%42];
    auto it=find_if(orb.begin(),orb.end(),[&](auto a){return a.first==z;});
    if(it==orb.end())orb.emplace_back(z,c);
    else if(it->second!=c)ok=false;
   }
  if(ok){B.reps.push_back(v);B.vec.push_back(orb);}
 }
 return B;
}

int rank_mod(vector<vector<uint16_t>>& a,int n){
 int rk=0; const int m=a.size(); vector<uint16_t> lookup(mod*n);
 for(int j=0;j<n;j++){
  int piv=rk;while(piv<m&&!a[piv][j])piv++;
  if(piv==m)continue;
  swap(a[rk],a[piv]);const auto &b=a[rk];
  int denom=inv[b[j]];
  for(int c=1;c<mod;c++)for(int v=j+1;v<n;v++)lookup[c*n+v]=b[v]*c%mod;
  for(int i=rk+1;i<m;i++){
   auto &row=a[i];if(!row[j])continue;
   const uint16_t *d=lookup.data()+(mod-(row[j]*denom)%mod)*n;
   for(int v=j+1;v<n;v++){int x=row[v]+d[v];row[v]=x>=mod?x-mod:x;}
   row[j]=0;
  }
  rk++;
 }
 return rk;
}

int main(){
 setup();
 constexpr int nonzero[6]={5464,5460,5460,5464,5460,5460};
 constexpr int zero[6][2]={{794,793},{768,768},{792,792},{768,768},{792,792},{768,768}};
 vector<array<int,3>> tasks;
 for(int j=0;j<4;j++)tasks.push_back({1,j,0});
 for(int j=0;j<4;j++)tasks.push_back({0,j,0});
 for(int k=1;k<=3;k++)for(int j=0;j<6;j++)tasks.push_back({0,j,k});
 vector<int> output(tasks.size());
 #pragma omp parallel for schedule(dynamic)
 for(unsigned i=0;i<tasks.size();i++){
  auto [h,j,k]=tasks[i];
  auto B=eigenspace(h,j,k),C=eigenspace(h,j,k);
  int n=h?nonzero[j]:zero[j][k!=0];
  assert((int)B.reps.size()==n&&(int)C.vec.size()==n);
  vector<vector<uint16_t>> a(n,vector<uint16_t>(n));
  for(int u=0;u<n;u++)for(int v=0;v<n;v++){
   int s=0;for(auto [w,c]:C.vec[v])s+=c*trace(B.reps[u],w);
   a[u][v]=s%mod;
  }
  output[i]=rank_mod(a,n);
  #pragma omp critical
  {fprintf(stderr,"h=%d j=%d k=%d dim=%d rank=%d\n",h,j,k,n,output[i]);}
 }
 bool ok=true;
 for(unsigned i=0;i<tasks.size();i++){
  auto [h,j,k]=tasks[i];int n=h?nonzero[j]:zero[j][k!=0];
  int ideal=n;
  if(output[i]!=ideal)ok=false;
 }
 puts(ok?"rank 262144 certified over F_43":"some blocks do not achieve the target ranks");
 return ok?0:1;
}
