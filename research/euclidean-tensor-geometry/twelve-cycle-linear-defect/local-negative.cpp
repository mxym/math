#include <algorithm>
#include <array>
#include <vector>
#include <set>
#include <iostream>
#include <cassert>
#include <stdexcept>
using namespace std;
constexpr int p=13;
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
int sgn(int x){return x==0?0:(x%2?x+1:x-1);}
int rnd(const int x){return mod(435*x*x*x+251*x*x+471*x+1);}
struct Edge{int from,to,v,t;};
vector<Edge> e[11];int nq;
void init(int q,int seed){
 nq=q;for(auto&v:e)v.clear();
 auto add=[](int a,int i,int j,int c,int t){e[a].push_back({i,j,c,t});};
 add(0,0,0,1,0);
 for(int a=1;a<q;a++){
  add(a,0,a,1,0);
  add(a,sgn(a),0,(a%2?2:1),0);
  add(a,a,a,rnd(a%2+seed),1);
  add(a,sgn(a),sgn(a),rnd(a%2+2+seed),1);
  add(0,a,0,rnd(a%2+4+seed),1);
 }
}
T tr(const W&a,const W&b,int limit){
 T res{};
 int W[12];int z0=-1;for(int j=0;j<12;j++){W[j]=j%2?sgn(b[j/2]):a[j/2];if(W[j]==0)z0=j;}
 for(int s=0;s<(z0>=0?1:nq);s++){
  T x[11]={};x[s][0]=1;
  for(int d=0;d<12;d++){int j=(d+z0+1)%12;
   T y[11]={};
   for(auto z:e[W[j]])
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
  if(w[j]){W y=w;y[j]=0;sort(y.begin(),y.end());L.insert(y);}
  else for(int a=1;a<nq;a++){W y=w;y[j]=a;sort(y.begin(),y.end());L.insert(y);}
 }
 return L;
}

Mat effective(vector<Orbit> const&A, vector<Orbit> const&B, W const&w, W const&v){
 Mat H=mats(A,B,2);
 auto n1=nextprofiles(w), n2=nextprofiles(v);
 for(W const& y:n1)if(n2.count(y)){
  auto J=bas(y);if(J.empty())continue;
  Mat X=mats(J,B,1),Y=mats(A,J,1);
  auto nz=[](Mat const&M){for(auto &r:M)for(int a:r)if(a)return true;return false;};
  if(nz(X)&&nz(Y)){apply(mats(J,J,0),X);subtract(H,mul(Y,X));}
 }return H;
}
void add(Mat &A,Mat const&B){for(int i=0;i<(int)A.size();i++)for(int j=0;j<(int)A[i].size();j++)A[i][j]=mod(A[i][j]+B[i][j]);}
struct PM{W w;vector<Orbit>a;Red f;Mat WW;};
int main(int argc,char**argv){
 int q=argc>1?atoi(argv[1]):5, seed=argc>2?atoi(argv[2]):2;init(q,seed);root=p-1;
 vector<PM>N;
 for(int i=1;i<q;i+=2)for(int j=i+2;j<q;j+=2){
  W w{0,0,i,i+1,j,j+1};auto a=bas(w);
  auto f=red(mats(a,a,0));if(f.L.size()!=12)throw runtime_error("bad kernel");
  auto H=mul(mul(f.L,effective(a,a,w,w)),f.R);
  N.push_back({w,a,f,H});
 }
 vector<W> keys;
 for(int i=1;i<q;i+=2)for(int j=1;j<q;j+=2)if(i!=j){W w{i,i,i+1,i+1,j,j+1};sort(w.begin(),w.end());keys.push_back(w);}
 for(int i=1;i<q;i+=2)for(int j=i+2;j<q;j+=2)for(int k=j+2;k<q;k+=2)keys.push_back({i,i+1,j,j+1,k,k+1});
 Mat W0=Z(N.size()*12,N.size()*12);
 for(int i=0;i<(int)N.size();i++)for(int x=0;x<12;x++)for(int y=0;y<12;y++)W0[12*i+x][12*i+y]=N[i].WW[x][y];
 vector<Mat> cache(3);for(auto const&w:keys){
  auto K=bas(w);
  const int kt=(K.size()==120)?2:(w[0]==w[1]?0:1);
  if(cache[kt].empty()){cache[kt]=effective(K,K,w,w);cout<<"K "<<K.size()<<" det "<<det(cache[kt])<<endl;}
  Mat H=cache[kt];if(det(H)==0){cout<<"FAIL "<<seed<<endl;return 0;}
  vector<int>I;vector<Mat>L,R;
  for(int i=0;i<(int)N.size();i++)if(includes(w.begin(),w.end(),N[i].w.begin()+2,N[i].w.end())){
   auto &z=N[i];
   auto B=mul(z.f.L,effective(z.a,K,z.w,w)),X=mul(effective(K,z.a,w,z.w),z.f.R);
   apply(H,X);I.push_back(i);L.push_back(B);R.push_back(X);
  }
  for(int i=0;i<(int)I.size();i++)for(int j=0;j<(int)I.size();j++){
   auto C=mul(L[i],R[j]);
   for(int x=0;x<12;x++)for(int y=0;y<12;y++)W0[12*I[i]+x][12*I[j]+y]=mod(W0[12*I[i]+x][12*I[j]+y]-C[x][y]);
  }
 }
 cout<<"result q "<<q<<" seed "<<seed<<" N "<<W0.size()<<" rank "<<piv(W0).first.size()<<" det "<<det(W0)<<endl;
 for(auto const &row:W0){for(int x:row)cout<<x<<" ";cout<<"\n";}
}
