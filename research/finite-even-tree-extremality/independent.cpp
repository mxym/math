#include <gmpxx.h>
#include <algorithm>
#include <iostream>
#include <stdexcept>
#include <vector>
using cpp_int=mpz_class;
static_assert(sizeof(unsigned long)>=8,"Requires a 64-bit unsigned long for the gap multiplier");
using std::vector;
int main() {
 const int K=128;
 vector<int> hi(K+1,0);
 for (int j=2; j<K; ++j) {
  int m=2*j*j-1;
  hi[j]=std::max(hi[j],m); hi[j+1]=std::max(hi[j+1],m);
 }
 for (int k=K; k>=4; --k) {
  int p=k/2,q=k-p,h=(hi[k]+1)/2;
  hi[p]=std::max(hi[p],h); hi[q]=std::max(hi[q],h);
 }
 vector<vector<cpp_int>> T(K+1);
 for(int k=1;k<=K;++k) {
  int nmax=hi[k]; T[k].resize(nmax+1);
  if(k<=3){
   for(int n=k;n<=nmax;++n)
    if(k==1)T[k][n]=n;else if(k==2)T[k][n]=cpp_int(n)*(n-1)/2;else T[k][n]=cpp_int(n)*(n-1)*(n-2)/6;
   continue;
  }
  int p=k/2,q=k-p; vector<cpp_int> root(nmax+1);
  for(int v=k;v<=nmax;++v){
   int l=v/2,h=v-l;
   root[v]=T[p][l]*T[q][h];
   if(p!=q)root[v]+=T[q][l]*T[p][h];
  }
  // At every fixed depth the nonempty balanced tree node sizes
  // are floor(n/m) or ceil(n/m), and sum to n (virtual zero padding).
  for(int n=k;n<=nmax;++n)
   for(int m=1;m<=n;m*=2) {
    int q0=n/m,r=n%m;
    if(q0+1<k)break;
    if(m-r)T[k][n]+=(m-r)*root[q0];
    if(r)T[k][n]+=r*root[q0+1];
   }
 }
 unsigned ct=0,qt=0; int mx=0;
 for(int j=1;j<K;++j)for(int n=j+1;n<2*j*j;++n){
  const cpp_int &a=T[j][n],&b=T[j+1][n];
  if(a<=0||b<=0)throw std::runtime_error("empty required slice");
  cpp_int det=T[j][n-1]*b-T[j+1][n-1]*a;
  if(det<0)throw std::runtime_error("negative minor");
  ++ct;
  if(n>=2*j-1){if(det*(16UL*n*j*j)<a*b)throw std::runtime_error("small gap");++qt;}
  mx=std::max(mx,n);
 }
 std::cout<<ct<<" exact minors; "<<qt<<" exact quantitative gaps; largest host "<<mx<<"\n";
}
