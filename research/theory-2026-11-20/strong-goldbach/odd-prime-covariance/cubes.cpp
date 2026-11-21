#include <algorithm>
#include <gmpxx.h>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <vector>
using cpp_int=mpz_class;
using big=mpz_class;
using std::vector;
int pos=0,j,K,c=333,d=4000,a,H,l;
uint64_t fac[14], count_cells=0; vector<int>b;
vector<cpp_int>E;
cpp_int mass=0, bound=0;
big hpower;
cpp_int power(cpp_int n,int m){cpp_int v=1; while(m--)v*=n;return v;}
void keep(){
 ++count_cells;
 int r[12];for(int i=0;i<j;i++)r[i]=c*K+a*b[i];
 unsigned long mult=fac[j];
 for(int i=0;i<j;){int t=i+1;while(t<j&&b[t]==b[i])t++;mult/=fac[t-i];i=t;}
 cpp_int v=E[l]*mult;mass+=v;
 if(2*r[0]>=H)return; // all dominant, J identically zero
 int pc=0,tp=0,pp=0,tc=0;
 for(int i=0;i<j;i++)for(int m=i+1;m<j;m++){
   if(2*(r[i]+r[m]+a*std::max(0,l-(j-2)))>H)pc++;
   if(2*(r[i]+r[m]+a*std::min(2,l))>=H)pp++;
   if(j==7)for(int k=m+1;k<j;k++){int t=r[i]+r[m]+r[k];if(2*(t+a*std::min(3,l))>=H)tp++;if(2*(t+a*std::max(0,l-(j-3)))>H)tc++;}
 }
 int f=j==5?std::max(0,3-pc):std::max(0,std::min(10,tp-10-pc));
 if(pos && j==7)f=std::max(0,std::min(10,10+pp-tc));
 if(!f)return;
 big den=r[0]+a*l;
 for(int i=1;i<j;i++)den*=r[i];
 big q=(hpower*f+den-1)/den;
 bound+=v*cpp_int(q);
}
void visit(int rem,int n,int cap){
 if(n==1){if(rem<=cap){b.push_back(rem);keep();b.pop_back();}return;}
 for(int v=(rem+n-1)/n;v<=std::min(rem,cap);v++){b.push_back(v);visit(rem-v,n-1,v);b.pop_back();}
}
int main(int argc,char**argv){
 if(argc!=4) return 2;
 pos=std::atoi(argv[3]);
 j=std::atoi(argv[1]);K=std::atoi(argv[2]);if((j!=5&&j!=7)||K<j||K>512||pos<0||pos>1||(pos && j!=7))return 2;
 a=d-j*c;H=d*K;fac[0]=1;for(int i=1;i<=12;i++)fac[i]=fac[i-1]*i;E.resize(j);
 hpower=1;for(int i=0;i<j;i++)hpower*=H;
 for(l=1;l<j;l++){
  for(int i=0;i<=l;i++)E[l]+=(i%2?-1:1)*power(l-i,j-1)*(fac[j]/(fac[i]*fac[j-i]));
  if(E[l]<=0)return 3;
  visit(K-l,j,K-l);
 }
 if(mass!=power(K,j-1))return 4;
 cpp_int num=4*power(a,j-1)*bound;
 cpp_int den=power(H,j-1)*fac[j]*fac[j-1];
 std::cout<<pos<<" "<<j<<" "<<K<<" "<<count_cells<<" "<<mass<<" "<<num<<" "<<den<<"\n";
}
