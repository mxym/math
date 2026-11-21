// Independent homogeneous normal-vector enumeration: one reference row and four
// differences; wedge products of the differences give all five cofactors at once.
#include <array>
#include <vector>
#include <set>
#include <algorithm>
#include <numeric>
#include <iostream>
using namespace std;
using R=array<int,5>; using Profile=array<int,6>;
vector<R> rows;set<Profile> found;
int bitcnt(int x){return __builtin_popcount((unsigned)x);}
void extend(int a,int last,int n,const array<long long,32>& wedges){
 if(n<4){for(int j=last-1;j>=4-n-1;j--){
  array<long long,32> nw{};bool any=false;
  for(int m=1;m<32;m++)if(bitcnt(m)==n+1){int sign=(n%2?-1:1);
   for(int k=0;k<5;k++)if(m&(1<<k)){nw[m]+=sign*(rows[j][k]-rows[a][k])*wedges[m^(1<<k)];sign=-sign;} any=any||nw[m]!=0;}
  if(any)extend(a,j,n+1,nw);
 }return;}
 Profile p{};for(int j=0;j<5;j++)p[j]=(j%2?-1:1)*wedges[31^(1<<j)];
 long long den=inner_product(rows[a].begin(),rows[a].end(),p.begin(),0ll);
 if(den<0){for(auto&x:p)x=-x;den=-den;}
 if(!den||p[0]*8<=den||p[4]>=den||!is_sorted(p.begin(),p.begin()+5)||2*(p[0]+p[1])<=den||p[2]*2>den)return;
 int g=den;for(int j=0;j<5;j++)g=gcd(g,p[j]);for(int j=0;j<5;j++)p[j]/=g;p[5]=den/g;
 if(found.count(p))return;int count=0;for(auto&r:rows)count+=inner_product(r.begin(),r.end(),p.begin(),0)==p[5];if(count>=6)found.insert(p);
}
void children(int last,int depth,R&a){
 if(depth>=2){
  int t=depth-a[0];bool ok= (t==0&&a[0]<=7)||(t==1&&a[0]<=4)||(t==2&&a[0]<=1)||(t==3&&a[0]==0);
  if(ok)rows.push_back(a);
 }
 if(depth==7)return;
 for(int i=last;i<5;i++){a[i]++;children(i,depth+1,a);a[i]--;}
}
int main(){
 R a{};children(0,0,a);sort(rows.rbegin(),rows.rend());if(rows.size()!=62)return 3;
 array<long long,32> wedge{};wedge[0]=1;for(int j=4;j<(int)rows.size();j++)extend(j,j,0,wedge);
 for(auto&p:found){for(int x:p)cout<<x<<" ";cout<<"\n";}
}
