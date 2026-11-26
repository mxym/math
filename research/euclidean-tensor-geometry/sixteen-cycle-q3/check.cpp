#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <vector>
#include <iomanip>
using namespace std;
constexpr int p=41,q=3,N=6561,tail=N/q,ell=8;
using A=array<int,ell>;
A digits[N];
int rot[N],charge[N], ph[ell],inv[p];
using M=array<array<int,q>,q>;
M tr[N];
M weight[q]={{{{1,3,7},{17,5,13},{37,19,11}}},{{{4,9,8},{18,25,16},{14,20,12}}},{{{29,23,30},{22,35,21},{31,36,38}}}};
M mul(const M& a,const M& b){M c{};for(int i=0;i<q;i++)for(int j=0;j<q;j++){for(int k=0;k<q;k++)c[i][j]+=a[i][k]*b[k][j];c[i][j]%=p;}return c;}
void init(){
 ph[0]=1;for(int i=1;i<ell;i++)ph[i]=ph[i-1]*3%p;
 assert(ph[ell-1]*3%p==1 && ph[ell/2]==p-1);
 for(int i=1;i<p;i++)for(int v=1;v<p;v++)if(i*v%p==1)inv[i]=v;
 for(int i=0;i<N;i++){
  int w=i,s=0;for(int k=0;k<ell;k++){int u=w%q;w/=q;digits[i][k]=u;s+=u;}
  rot[i]=i/q+tail*(i%q);charge[i]=0;
 }
 for(int j=0;j<N;j++){
  M c{};for(int i=0;i<q;i++)c[i][i]=1;
  for(int k=0;k<ell;k++)c=mul(weight[digits[j][k]],c);
  tr[j]=c;
 }
}
int entry(int a,int b){
 int t1=0,t2=0;for(int k=3;k>=0;k--){
   t1=t1*9+digits[a][k]+q*digits[b][k];
   t2=t2*9+digits[a][k+4]+q*digits[b][k+4];
 }
 int sum=0; for(int i=0;i<q;i++)for(int j=0;j<q;j++)sum+=tr[t1][i][j]*tr[t2][j][i];
 return sum%p;
}
struct V {int r; vector<array<int,2>> orb;};
using B=vector<V>;
B basis(int h,int j){
 vector<bool> seen(N);B b;
 for(int i=0;i<N;i++)if(!seen[i]&&charge[i]==h){
  V v{i,{}};int w=i,k=0;
  do {seen[w]=true;v.orb.push_back({w,ph[(ell-(j*k)%ell)%ell]});w=rot[w];k++;}while(w!=i);
  if(j*k%ell==0)b.push_back(v);
 }
 return b;
}
int calc(int h,int j){
 auto R=basis(h,j),C=basis((q-h)%q,j);int n=R.size();assert(C.size()==R.size());
 vector<vector<uint8_t>> m(n,vector<uint8_t>(n));
 for(int i=0;i<n;i++)for(int k=0;k<n;k++){
  int s=0;for(auto u:C[k].orb)s+=u[1]*entry(R[i].r,u[0]);m[i][k]=s%p;
 }
 int r=0;
 for(int k=0;k<n;k++){
  int z=r;while(z<n&&!m[z][k])z++;
  if(z==n)continue;
  swap(m[z],m[r]);auto &v=m[r];
  for(int t=r+1;t<n;t++){
   auto &a=m[t];if(!a[k])continue;
   int c=p-a[k]*inv[v[k]]%p;
   for(int s=k+1;s<n;s++)a[s]=(a[s]+c*v[s])%p;
  }
  r++;
 }
 cout<<h<<" "<<j<<" "<<n<<" "<<r<<"\n";
 return r;
}
int main(){
 init();int rank=0;
 for(int j=0;j<=4;j++)rank+=(j==0||j==4?1:2)*calc(0,j);

 cout<<"rank "<<rank<<" of "<<N<<"\n";
 return rank==N-1?0:1;
}
