#include<bits/stdc++.h>
using namespace std;
int main(){
const int s=8,N=6561,H=N/3;
vector<vector<int>>w(N,vector<int>(s));vector<int>rep(N,-1),sg(N),O;
auto rot=[&](int x){return x/3+(x%3)*H;};
for(int x=0;x<N;x++){int z=x,q=0;for(int j=0;j<s;j++){int a=z%3;z/=3;w[x][j]=a;q+=a==1?1:a==2?-1:0;}
if(q||rep[x]!=-1)continue;
int y=x,l=0;do{rep[y]=x;sg[y]=l%2?-1:1;l++;y=rot(y);}while(y!=x);
if(l%2==0)O.push_back(x);
}
set<int>S(O.begin(),O.end());
auto refl=[&](int x){int z=0,p=1;for(int j=0;j<s;j++){int a=w[x][(s-j)%s];if(a)a=3-a;z+=p*a;p*=3;}return z;};
vector<vector<pair<int,int>>> Bminus,Bplus;
for(auto u:O){int x=refl(u),v=rep[x],e=sg[x];if(!S.count(v))abort();if(v<u)continue;
if(v==u){(e==1?Bplus:Bminus).push_back({{u,1}});}
else {Bplus.push_back({{u,1},{v,e}});Bminus.push_back({{u,1},{v,-e}});}}
cerr<<"dims "<<Bplus.size()<<" "<<Bminus.size()<<endl;
if(Bplus.size()>Bminus.size())swap(Bplus,Bminus);
int m=Bplus.size(), n=Bminus.size(),D=2*s;
vector<vector<vector<int>>> P(m,vector<vector<int>>(n,vector<int>(D+1)));
for(int i=0;i<m;i++)for(int j=0;j<n;j++){
int u=Bplus[i][0].first;
for(auto [v,e]:Bminus[j]){int x=v;do{for(int b0=0;b0<2;b0++){
int b=b0,k=0;bool ok=true;for(int a=0;a<s&&ok;a++)for(int y:{w[u][a],w[x][a]}){if(y==0)k+=b;else if(b==y-1)b^=1;else{ok=false;break;}}if(ok&&b==b0)P[i][j][k]+=e*sg[x];
}x=rot(x);}while(x!=v);}}
int C=0,deg=0;for(auto &row:P)for(auto &a:row){int c=0;for(int k=0;k<=D;k++)if(a[k]){c+=abs(a[k]);deg=max(deg,k);}C=max(C,c);}
cout<<"entry norm "<<C<<" degree "<<deg<<endl;
vector<vector<pair<int,int>>>  terms(m*n);
for(int i=0;i<m;i++)for(int j=0;j<n;j++)for(int k=0;k<=D;k++)if(P[i][j][k])terms[i*n+j].push_back({k,P[i][j][k]});
int p;
while(cin>>p){
vector<int>I(p,1);for(int x=2;x<p;x++)I[x]=p-(long long)(p/x)*I[p%x]%p;
vector<int> A(m*n),T(D+1,1);int maxr=0;
for(int t=0;t<=50*deg;t++){
for(int k=1;k<=D;k++)T[k]=T[k-1]*t%p;
for(int j=0;j<m*n;j++){int x=0;for(auto [k,z]:terms[j])x+=T[k]*z;A[j]=(x%p+p)%p;}
int r=0;for(int j=0;j<n&&r<m;j++){
int i=r;while(i<m&&!A[i*n+j])i++;if(i==m)continue;for(int l=j;l<n;l++)swap(A[i*n+l],A[r*n+l]);int *a=&A[r*n];int z=I[a[j]];
for(int l=r+1;l<m;l++){int *b=&A[l*n];if(b[j]){int f=b[j]*z%p;for(int k=j;k<n;k++)b[k]=(b[k]+p*p-f*a[k])%p;}}r++;}
maxr=max(maxr,r);if(r>49){cout<<"failed "<<p<<" "<<t<<" rank "<<r<<endl;return 1;}}
cout<<p<<" "<<maxr<<endl;
}}
