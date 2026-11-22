// Exact rational upper of the rank-7 and rank-9 quadratic debit.
// Independent inner ceiling for the allowed fraction and reciprocal denominator.
#include <array>
#include <iostream>
#include <stdexcept>
#include <string>
using i128 = __int128_t;
using i64 = long long;
constexpr i64 K = 1LL << 38;
void need(bool x) { if (!x) throw std::runtime_error("certificate failed"); }
i128 ceildiv(i128 x, i128 y) { need(x >= 0 && y > 0); return (x+y-1)/y; }
std::string dec(i128 x) {
  if (!x) return "0";
  std::string s;
  while(x>0){s=char('0'+x%10)+s;x/=10;}
  return s;
}
struct Test {
 int d,n,m; i64 P=1,Q,ix[10]; i128 wden, num=0;
 Test(int d0,int n0,int m0):d(d0),n(n0),m(m0){
  for(int j=0;j<d;j++) P*=n;
  Q=P*m;
  wden=2*n;
  for(int j=1;j<d;j++) wden*=3*n*n;
 }
 i64 area(i64 a,i64 b,i64 c){ // ceil(K*vol{a X+b Y <= c})
  if(c<=0)return 0;
  if(c>=a+b)return K;
  if(a==0)return ceildiv(i128(K)*c,b);
  if(b==0)return ceildiv(i128(K)*c,a);
  if(a>b)std::swap(a,b);
  if(c<a)return ceildiv(i128(K)*c*c,2*i128(a)*b);
  if(c<b)return ceildiv(i128(K)*(2*c-a),2*b);
  i64 u=a+b-c;
  return ceildiv(i128(K)*(2*i128(a)*b-i128(u)*u),2*i128(a)*b);
 }
 void box(){
  i64 l[10],u[10]; i128 weight=1;
  l[0]=u[0]=P;
  for(int j=0;j<d;j++){
   l[j+1]=l[j]*ix[j]/n;u[j+1]=u[j]*(ix[j]+1)/n;
   weight*=j==d-1?2*ix[j]+1:3*ix[j]*ix[j]+3*ix[j]+1;
  }
  auto bl=l[d],bh=u[d],cl=l[d-1],ch=u[d-1];
  int R=d-1;
  i64 twice_support_D2=2*P+cl;
  for(int j=1;j<R;j++)twice_support_D2+=l[j];
  twice_support_D2*=m;
  const i128 recip_num=i128(2*Q)*(2*Q)*(2*Q)*K;
  i128 inner=0;
  for(unsigned S=0;S<(1u<<R);S++){
   if(__builtin_popcount(S)%2)continue;
   i64 sl=0,sh=0,pl=0;
   // Exact min/max of signed nested ratio polynomial.
   for(int j=R-1;j>=0;j--){
    i64 c=(S>>j&1)?-1:1;
    if(c>0)pl+=l[j];
    if(j==R-1)sl=sh=c*P;
    else{
     sl=c*P+sl*(sl<0?ix[j]+1:ix[j])/n;
     sh=c*P+sh*(sh>0?ix[j]+1:ix[j])/n;
    }
   }
   if(2*bh+ch+sh<=P)continue;
   for(int j=0;j<m;j++)for(int k=0;k<m;k++){
    const i64 cu=k<m/2?ch:cl;
    const i64 C=2*(m-j)*bh+(m-2*k)*cu+m*(sh-P);
    if(C<=0)continue;
    const i64 f=area(2*bh,2*cu,C);
    const i64 D1=2*std::max(Q,-2*bh*(j+1)+(m-2*(k+1))*(k+1<=m/2?cl:ch)+m*sl);
    const i64 D2=std::max(twice_support_D2,2*(bl*(m-j-1)+cl*(m-k-1)+m*pl));
    const i64 inv=ceildiv(recip_num,i128(D1)*D2*D2);
    inner+=ceildiv(i128(f)*inv,K);
   }
  }
  num+=weight*inner;
 }
 void rec(int j=0){
  if(j==d){box();return;}
  for(ix[j]=0;ix[j]<n;ix[j]++)rec(j+1);
 }
 void verify(i64 cap){
  rec();
  i128 a=8*num, b=i128(K)*wden*P*m*m;
  need(a<cap*(b/100000)+(cap*(b%100000))/100000);
  std::cout<<"k="<<d+3<<": exact upper "<<dec(a)<<"/"<<dec(b)<<" < "<<cap<<"/100000\n";
 }
};
int main(){
 Test(4,24,12).verify(1661);
 Test(6,14,8).verify(1824);
}
