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

const vector<vector<array<int,3>>> V={
  {{35,0,-1},{50,0,1},{56,1,1}},
  {{22,1,1},{34,3,-1},{49,3,1},{56,0,1}},
  {{30,2,-1},{35,4,1},{39,0,-1},{50,4,-1},{53,0,1}},
  {{9,1,1},{25,4,-1},{26,0,1},{51,4,1},{54,0,1}},
  {{16,1,-1},{30,0,-1},{34,6,1},{38,2,-1},{49,6,-1},{52,2,1}},
  {{18,1,-1},{29,5,-1},{31,3,-1},{32,8,-1},{33,4,1},{41,4,1},{42,0,-1},{44,6,-1},{45,2,1}},
  {{10,3,1},{15,1,-1},{24,3,-1},{26,4,1},{27,0,-1},{33,6,1},{37,2,-1},{48,6,-1},{49,2,1}},
  {{6,1,-1},{17,3,1},{20,1,-1},{23,6,-1},{25,2,1},{40,4,1},{41,0,-1},{53,4,-1},{55,0,1}},
};
if(m!=57||n!=84) throw runtime_error("unexpected block dimensions");
for(auto v:V)for(int c=0;c<n;c++){
 vector<int> out(D+9);
 for(auto [i,a,z]:v)for(auto [b,x]:terms[i*n+c])out[a+b]+=z*x;
 if(any_of(out.begin(),out.end(),[](int z){return z!=0;}))throw runtime_error("nonzero polynomial");
}
vector<vector<int>> B;vector<int>I(101,1),tp(9,1);
for(int x=2;x<101;x++)I[x]=101-(101/x)*I[101%x]%101;
for(int x=1;x<9;x++)tp[x]=tp[x-1]*7%101;
for(auto v:V){vector<int> b(m);for(auto [i,e,c]:v)b[i]=(b[i]+101+c*tp[e])%101;B.push_back(b);}
int r=0;
for(int j=0;j<m&&r<(int)B.size();j++){
 int i=r;while(i<(int)B.size()&&!B[i][j])i++;
 if(i==(int)B.size())continue;
 swap(B[r],B[i]);int z=I[B[r][j]];
 for(int l=r+1;l<(int)B.size();l++)if(B[l][j]){
  int f=B[l][j]*z%101;for(int k=j;k<m;k++)B[l][k]=(B[l][k]+10201-f*B[r][k])%101;
 }
 r++;
}
if(r!=8)throw runtime_error("not independent");
cout<<"8 independent exact polynomial null vectors"<<endl;
}
