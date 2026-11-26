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
int root=1; vector<Orbit> bas(W a){
 sort(a.begin(),a.end());vector<Orbit> v;
 do{
  W t=a; bool ok=true;vector<W> O;
  do{if(t<a){ok=false;break;}O.push_back(t);rot(t);}while(t!=a);
  if(ok&&pw(root,O.size())==1)v.push_back({a,O});
 }while(next_permutation(a.begin(),a.end()));
 return v;
}
int nq; int sgn(int x){return (x==0||(nq%2==0&&x==nq-1))?x:(x%2?x+1:x-1);}
int rnd(const int x){return mod(435*x*x*x+251*x*x+471*x+1);}
struct Edge{int from,to,v,t;};
vector<Edge> e[7];
void init(int q,int seed){
 nq=q;for(auto&v:e)v.clear();
 auto add=[](int a,int i,int j,int c,int t){e[a].push_back({i,j,c,t});};
 add(0,0,0,1,0);
 for(int a=1;a<q;a++){
  add(a,0,a,1,0);
  add(a,sgn(a),0,rnd(a+seed),0);
  if(a==nq-1)continue;
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
  int v=tr(a.rep,b.orbit[j],h)[h];x+=pw(root,j)*v;
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
struct Red{vector<int>r,c;Mat L,R;};
Mat sub(Mat const&A,vector<int> const&u,vector<int> const&v){
 Mat a=Z(u.size(),v.size());
 for(int i=0;i<(int)u.size();i++)for(int j=0;j<(int)v.size();j++)a[i][j]=A[u[i]][v[j]];
 return a;
}
pair<vector<int>,vector<int>> piv(Mat A){
 if(A.empty())return {};
 int n=A.size(),m=A[0].size(),r=0;
 vector<int> order(n),cs;for(int i=0;i<n;i++)order[i]=i;
 for(int j=0;j<m;j++){
  int i=r;while(i<n&&!A[i][j])i++;if(i==n)continue;
  swap(A[i],A[r]);swap(order[i],order[r]);cs.push_back(j);
  int t=pw(A[r][j],p-2);
  for(int a=r+1;a<n;a++)if(A[a][j]){
   int b=mod(-A[a][j]*t);for(int l=j;l<m;l++)A[a][l]=(A[a][l]+b*A[r][l])%p;
  }
  r++;
 }
 order.resize(r);return {order,cs};
}
Mat transpose(Mat const&A){Mat B=Z(A[0].size(),A.size());for(int i=0;i<(int)A.size();i++)for(int j=0;j<(int)A[0].size();j++)B[j][i]=A[i][j];return B;}
Mat mul(Mat const&A,Mat const&B){
 Mat C=Z(A.size(),B[0].size());for(int i=0;i<(int)A.size();i++)for(int j=0;j<(int)B[0].size();j++){int64_t v=0;for(int k=0;k<(int)B.size();k++)v+=A[i][k]*B[k][j];C[i][j]=v%p;}return C;
}
void subtract(Mat &A,Mat const&B){for(int i=0;i<(int)A.size();i++)for(int j=0;j<(int)A[i].size();j++)A[i][j]=mod(A[i][j]-B[i][j]);}
Red red(Mat const&A){
 auto [u,v]=piv(A);vector<int>x,y;
 int n=A.size();
 for(int i=0;i<n;i++){if(find(u.begin(),u.end(),i)==u.end())x.push_back(i);if(find(v.begin(),v.end(),i)==v.end())y.push_back(i);}
 Mat L=Z(x.size(),n),R=Z(n,y.size());
 for(int i=0;i<(int)x.size();i++)L[i][x[i]]=1;
 for(int i=0;i<(int)y.size();i++)R[y[i]][i]=1;
 if(!u.empty()&&!x.empty()){
  Mat B=sub(A,u,y),C=transpose(sub(A,x,v)),D=sub(A,u,v);
  apply(D,B);apply(transpose(D),C);
  for(int i=0;i<(int)u.size();i++)for(int j=0;j<(int)x.size();j++){L[j][u[i]]=mod(-C[i][j]);R[v[i]][j]=mod(-B[i][j]);}
 }
 return {u,v,L,R};
}
set<W> nextprofiles(W const&w){
 set<W>L;
 for(int j=0;j<6;j++){
  if(w[j]){if(w[j]!=nq-1){W y=w;y[j]=0;sort(y.begin(),y.end());L.insert(y);}}
  else for(int a=1;a<nq-1;a++){W y=w;y[j]=a;sort(y.begin(),y.end());L.insert(y);}
 }
 return L;
}
int main(int argc,char**argv){
 int q=argc>1?atoi(argv[1]):6, seed=argc>2?atoi(argv[2]):2;init(q,seed);
 vector<W>K{{0,1,2,3,4,5},{1,2,3,4,5,5}};
 for(int h=0;h<6;h++){
  root=pw(11,(p-1)/6*h);
  for(W const&w:K){
   auto A=bas(w);
   Red f=red(mats(A,A,0));
   if(f.L.empty())continue;
   Mat H=mul(mul(f.L,mats(A,A,2)),f.R);
   for(auto y:nextprofiles(w)){
    auto J=bas(y);if(J.empty())continue;
    Mat X=mul(mats(J,A,1),f.R),B=mul(f.L,mats(A,J,1));
    auto nonzero=[](Mat const&M){for(auto &r:M)for(int a:r)if(a)return true;return false;};
    if(nonzero(X)&&nonzero(B)){apply(mats(J,J,0),X);subtract(H,mul(B,X));}
   }
   std::cout<<"corezeros "<<std::count(w.begin(),w.end(),0)<<" root "<<h<<" residual "<<H.size()<<" rank "<<piv(H).first.size()<<" det "<<det(H)<<endl;
  }
 }
}
