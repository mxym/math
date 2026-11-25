#include <algorithm>
#include <array>
#include <vector>
#include <set>
#include <iostream>
#include <cassert>
#include <stdexcept>
using namespace std;
constexpr int p=1009;
int mod(int x){x%=p;return x<0?x+p:x;}
int pw(int x,int i){int r=1;for(;i;i/=2,x=x*x%p)if(i&1)r=r*x%p;return r;}
using W=array<int,6>;using T=array<int,3>;
void rot(W&w){rotate(w.begin(),w.begin()+1,w.end());}
struct Orbit {W rep; vector<W> orbit;};
vector<Orbit> bas(W a){
 sort(a.begin(),a.end());vector<Orbit> v;
 do{
  W t=a; bool ok=true;vector<W> O;
  do{if(t<a){ok=false;break;}O.push_back(t);rot(t);}while(t!=a);
  if(ok&&O.size()%2==0)v.push_back({a,O});
 }while(next_permutation(a.begin(),a.end()));
 return v;
}
int sgn(int x){return x==0?0:(x%2?x+1:x-1);}
int rnd(const int x){return mod(435*x*x*x+251*x*x+471*x+1);}
struct Edge{int from,to,v,t;};
vector<Edge> e[7];int nq;
void init(int q,int seed){
 nq=q;for(auto&v:e)v.clear();
 auto add=[](int a,int i,int j,int c,int t){e[a].push_back({i,j,c,t});};
 add(0,0,0,1,0);
 for(int a=1;a<q;a++){
  add(a,0,a,1,0);
  add(a,sgn(a),0,rnd(a+seed),0);
  add(a,a,a,rnd(a+q+seed),1);
  add(a,sgn(a),sgn(a),rnd(a+2*q+seed),1);
  add(0,a,0,rnd(a+3*q+seed),1);
 }
}
T tr(const W&a,const W&b,int limit){
 T res{};
 for(int s=0;s<nq;s++){
  T x[7]={};x[s][0]=1;
  for(int j=0;j<12;j++){
   T y[7]={};
   for(auto z:e[j%2?sgn(b[j/2]):a[j/2]])
    for(int h=0;h+z.t<=limit;h++)
     y[z.to][h+z.t]+=z.v*x[z.from][h];
   for(int i=0;i<nq;i++)for(int h=0;h<=limit;h++)x[i][h]=y[i][h]%p;
  }
  for(int h=0;h<=limit;h++)res[h]=(res[h]+x[s][h])%p;
 }
 return res;
}
int coef(const Orbit&a,const Orbit&b,int h){
 int x=0;for(int j=0;j<(int)b.orbit.size();j++){
  int v=tr(a.rep,b.orbit[j],h)[h];x+=(j%2?-v:v);
 }
 return mod(x);
}
using Mat=vector<vector<int>>;
Mat Z(int n,int m){return Mat(n,vector<int>(m));}
Mat mats(const vector<Orbit>&a,const vector<Orbit>&b,int h){
 Mat A=Z(a.size(),b.size());
 for(int i=0;i<(int)a.size();i++)for(int j=0;j<(int)b.size();j++)A[i][j]=coef(a[i],b[j],h);
 return A;
}
void apply(Mat A,Mat&B){
 int n=A.size(),m=B[0].size();
 for(int j=0;j<n;j++){
  int k=j;while(k<n&&!A[k][j])k++;
  if(k==n)throw 1;
  swap(A[k],A[j]);swap(B[k],B[j]);int z=pw(A[j][j],p-2);
  for(int l=j;l<n;l++)A[j][l]=z*A[j][l]%p;
  for(int l=0;l<m;l++)B[j][l]=z*B[j][l]%p;
  for(int i=0;i<n;i++)if(i!=j&&A[i][j]){
   int a=p-A[i][j];
   for(int l=j;l<n;l++)A[i][l]=(A[i][l]+a*A[j][l])%p;
   for(int l=0;l<m;l++)B[i][l]=(B[i][l]+a*B[j][l])%p;
  }
 }
}
int det(Mat A){
 int d=1,n=A.size();
 for(int j=0;j<n;j++){
  int k=j;while(k<n&&!A[k][j])k++;
  if(k==n)return 0;
  if(k!=j)swap(A[k],A[j]),d=p-d;
  d=d*A[j][j]%p;int z=pw(A[j][j],p-2);
  for(int i=j+1;i<n;i++){
   int a=mod(-z*A[i][j]);for(int l=j+1;l<n;l++)A[i][l]=(A[i][l]+a*A[j][l])%p;
  }
 }return d;
}
int main(){
 vector<W> words{{1,1,1,2,2,2},{1,1,2,2,3,4},{1,2,3,4,5,6}};
 for(int i_profile=0;i_profile<3;i_profile++){
  W w=words[i_profile];
  init(w.back()+1,2);
  auto K=bas(w);
  Mat H=mats(K,K,2),base=mats(K,K,0),first=mats(K,K,1);
  for(auto A:{base,first})for(auto row:A)for(int x:row)assert(!x);
  set<W>L;
  for(int j=0;j<6;j++){
   W y=w;y[j]=0;sort(y.begin(),y.end());L.insert(y);
  }
  for(W y:L){
   auto J=bas(y);Mat A=mats(J,J,0),X=mats(J,K,1),B=mats(K,J,1);
   cout<<"J "<<J.size()<<" base det "<<det(A)<<endl;
   apply(A,X);
   for(int i=0;i<(int)K.size();i++)for(int j=0;j<(int)K.size();j++){
    int v=0;for(int k=0;k<(int)J.size();k++)v+=B[i][k]*X[k][j];
    H[i][j]=mod(H[i][j]-v);
   }
  }
  int d=det(H);int expected[3]={0,111,793};
  cout<<"K "<<K.size()<<" jet determinant "<<d<<endl;
  if(d!=expected[i_profile])throw runtime_error("second-jet determinant mismatch");
 }
}
