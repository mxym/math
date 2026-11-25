#include <array>
#include <cassert>
#include <iostream>
#include <vector>

constexpr int p=1009;
int power(int x,int n) {int a=1; for (;n;n>>=1,x=x*x%p) if(n&1) a=a*x%p; return a;}
int rank_for(int q) {
  int N=q*q*q*q;
  std::vector<std::vector<int>> K(q,std::vector<int>(q));
  for(int i=0;i<q;++i) for(int j=0;j<q;++j) K[i][j]=power(i+1,j);
  std::vector<std::array<int,4>> W(N);
  for(int i=0;i<N;++i) {int a=i; for(int j=3;j>=0;--j) {W[i][j]=a%q;a/=q;}}
  std::vector<std::vector<int>> M(N,std::vector<int>(N));
  for(int i=0;i<N;++i) for(int j=0;j<N;++j) {
    int a=1;
    for(int k=0;k<4;++k) a=a*K[W[i][k]][W[j][k]]%p*K[W[j][k]][W[i][(k+1)%4]]%p;
    M[i][j]=a;
  }
  int r=0;
  for(int j=0;j<N;++j) {
    int i=r; while(i<N&&!M[i][j])++i;
    if(i==N) continue;
    M[r].swap(M[i]);
    const int inv=power(M[r][j],p-2);
    for(int i=r+1;i<N;++i) if(M[i][j]){
      const int z=p-M[i][j]*inv%p;
      for(int k=j;k<N;++k) M[i][k]=(M[i][k]+z*M[r][k])%p;
    }
    if(++r==N) break;
  }
  return r;
}
int main(){
  for(auto c : {std::array<int,2>{5,625}, {6,1296}, {7,2400}, {8,4096}}) {
    int r=rank_for(c[0]);
    std::cout<<c[0]<<" "<<r<<std::endl;
    if(r!=c[1]) return 1;
  }
}
