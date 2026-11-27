// Exact C++17 verification: mass34 cap6, target b12, top degree9.
// Invoke with optional leading projective index 0..17. Output only completed counts.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <vector>
using namespace std;
inline int m(int x){x%=17; return x<0?x+17:x;}
int inv[17], powr[17][11];
const int D=10,sz=12,lim=255, allbits=(1<<17)-1;
const int S[sz]={0,1,2,3,4,5,6,7,8,9,11,15};
struct Profile{int q; array<int,11> f;};
vector<Profile> bank;
struct Node { array<int,17> c{}; int mask=0,w=10000,id=-1;};
vector<Node> tree(17*17);
int root[17][17]; 
int rot(int a,int b){return ((uint32_t(a)<<b)|(uint32_t(a)>>(17-b)))&allbits;} // b is 0..16
static int perm[17][1<<17];
int wt[sz],iw[sz],scale;
uint64_t stats[9]={}, congr=0, phys=0;
uint64_t idx7=0;
struct Interp{
 int r,t, B[sz],T[sz],coef[sz][sz], tab[sz][sz][17];
};
map<vector<int>,Interp> cached;
const Interp& interp(const vector<int>& B){
 auto hit=cached.find(B);if(hit!=cached.end())return hit->second;
 Interp I{};I.r=B.size();for(int i=0;i<I.r;i++)I.B[i]=B[i];
 for(int k=0;k<sz;k++)if(find(B.begin(),B.end(),k)==B.end())I.T[I.t++]=k;
 for(int i=0;i<I.t;i++)for(int j=0;j<I.r;j++){
  int q=1,d=1,u=S[I.T[i]],v=S[B[j]];
  for(int a:B)if(a!=B[j]){q=m(q*(u-S[a]));d=m(d*(v-S[a]));}
  int c=m(m(q*inv[d])*m(wt[I.T[i]]*iw[B[j]]));I.coef[i][j]=c;
  for(int x=0;x<17;x++)I.tab[i][j][x]=m(c*x);
 }
 return cached.emplace(B,I).first->second;
}
void profileGen(int D){
 auto start=bank.size();int B[11][11]={};
 for(int i=0;i<=D;i++){
  int g[11]={1},den=1,dd=0;
  for(int j=0;j<=D;j++)if(j!=i){
   for(int k=dd+1;k>0;k--)g[k]=m(g[k-1]-j*g[k]);
   g[0]=m(-j*g[0]);++dd;den=m(den*(i-j));
  }
  for(int k=0;k<=D;k++)B[i][k]=m(g[k]*inv[den]);
 }
 int T[17][11]={};
 for(int x=0;x<17;x++)for(int i=0;i<=D;i++)for(int k=0;k<=D;k++)T[x][i]=m(T[x][i]+B[i][k]*powr[x][k]);
 int ia=D-1,ib=D,dt=inv[m(B[ia][D-1]*B[ib][D]-B[ib][D-1]*B[ia][D])];
 int V[11]={},seen[17]={};
 for(int a=1;a<17;a++)if(!seen[a]){
  vector<int> orbit;for(int u=1;u<17;u++){int lead=m(a*powr[u][D]);if(!seen[lead]){orbit.push_back(u);seen[lead]=1;}}
  auto dfs=[&](auto&& self,int at,int sm,int sq,int x,int y)->void{
   if(at<ia){for(int v=0;v<=6&&sm+v<=34;v++){V[at]=v;self(self,at+1,sm+v,sq+v*v,x+v*B[at][D-1],y+v*B[at][D]);}return;}
   int cx=m(-x),cy=m(a-y),u=m((cx*B[ib][D]-cy*B[ib][D-1])*dt),v=m((cy*B[ia][D-1]-cx*B[ia][D])*dt);
   if(u>6||v>6)return;
   V[ia]=u;V[ib]=v;sm+=u+v;sq+=u*u+v*v;
   if(sm>34||sm+(16-D)*6<34)return;
   for(int t=D+1;t<17;t++){int q=0;for(int i=0;i<=D;i++)q+=T[t][i]*V[i];q%=17;
    if(q>6||sm+q>34||sm+q+(16-t)*6<34)return;
    sm+=q;sq+=q*q;
   }
   if(sm!=34)return;
   array<int,11> f{};for(int j=0;j<=D;j++){for(int i=0;i<=D;i++)f[j]+=B[i][j]*V[i];f[j]%=17;}
   assert(f[D]==a&&f[D-1]==0);for(int t:orbit){Profile P{(sq-68)/2,{}};for(int j=0;j<=D;j++)P.f[j]=m(f[j]*powr[t][j]);bank.push_back(P);}
  };
  dfs(dfs,0,0,0,0,0);
 }
 assert(bank.size()-start==(D==6?16:D==7?48:D==8?272:3008));
}

void insertBank(){
 for(int a=0;a<17;a++)for(int b=0;b<17;b++)root[a][b]=17*a+b;
 const auto centered=bank;bank.clear();
 for(auto P:centered)for(int h=0;h<17;h++){
  Profile Q{P.q,{}};auto& f=Q.f;
  for(int i=9;i>=0;i--){
   for(int j=9;j>0;j--)f[j]=m(f[j-1]-h*f[j]);
   f[0]=m(P.f[i]-h*f[0]);
  }
  const int id=bank.size();bank.push_back(Q);int n=root[f[9]][f[8]];
  for(int j=7;j>=0;j--){
   tree[n].w=min(tree[n].w,Q.q);
   int z=f[j];if(!tree[n].c[z]){tree[n].c[z]=tree.size();tree[n].mask|=1<<z;tree.emplace_back();}
   n=tree[n].c[z];
  }
  tree[n].w=Q.q;tree[n].id=id;
 }
}
void leaf(const int N[sz]){
 ++congr;
 int vals[sz][17];for(int i=0;i<sz;i++)for(int t=0;t<17;t++){
  int a=0;for(int k=10;k>=0;k--)a=(a*t+bank[tree[N[i]].id].f[k])%17;
  vals[i][t]=a;
 }
 for(int x=0;x<17;x++)for(int y=0;y<17;y++){
  int v=-22;for(int i=0;i<sz;i++)v+=vals[i][m(x+S[i]*y)];if(v!=0&&v!=17)return;
 }
 ++phys;cerr<<"Physical tuple "<<scale<<" hit "<<phys<<"\n";
}
void rec(int d,const int N[sz],int budget){
 if(budget>lim)return; 
 vector<int> ord(sz);for(int i=0;i<sz;i++)ord[i]=i;
 sort(ord.begin(),ord.end(),[&](int i,int j){int a=__builtin_popcount((unsigned)tree[N[i]].mask),b=__builtin_popcount((unsigned)tree[N[j]].mask);return a==b?i<j:a<b;});
 int next[sz];
 if(d==0){
  int tail[sz+1]={};for(int i=sz-1;i>=0;i--)tail[i]=tail[i+1]+tree[N[ord[i]]].w;
  auto G=[&](auto&& go,int at,int v,int w)->void{
   if(at==sz){if((v==22||v==39)&&w==lim){++stats[0];leaf(next);}return;}
   int i=ord[at];unsigned M=tree[N[i]].mask;
   while(M){int a=__builtin_ctz(M);M&=M-1;int n=tree[N[i]].c[a],t=tree[n].w;if(w+t+tail[at+1]<=lim&&v+a<=39){next[i]=n;go(go,at+1,v+a,w+t);}}
  };
  G(G,0,0,0);return;
 }
 int a=11-d;vector<int> B(ord.begin(),ord.begin()+a);sort(B.begin(),B.end());
 const auto& I=interp(B);int part[sz]={};int last=I.B[I.r-1],lastMask[sz],ic[sz];
 for(int t=0;t<I.t;t++){ic[t]=inv[I.coef[t][I.r-1]];lastMask[t]=perm[ic[t]][tree[N[I.T[t]]].mask];}
 auto G=[&](auto&& go,int at,int w)->void{
  if(at==I.r-1){
   unsigned M=tree[N[last]].mask;for(int t=0;t<I.t&&M;t++)M&=rot(lastMask[t],m(-ic[t]*part[t]));
   while(M){
    int a=__builtin_ctz(M);M&=M-1;int n=tree[N[last]].c[a],b=w+tree[n].w-tree[N[last]].w;
    if(b>lim)continue;next[last]=n;bool ok=true;
    for(int t=0;t<I.t;t++){int i=I.T[t],v=m(part[t]+I.tab[t][at][a]);int n=next[i]=tree[N[i]].c[v];b+=tree[n].w-tree[N[i]].w;if(b>lim){ok=false;break;}}
    if(ok){++stats[d];rec(d-1,next,b);}
   }return;
  }
  int i=I.B[at];unsigned M=tree[N[i]].mask;
  while(M){int x=__builtin_ctz(M);M&=M-1;int n=tree[N[i]].c[x],b=w+tree[n].w-tree[N[i]].w;
   if(b>lim)continue;
   next[i]=n;for(int t=0;t<I.t;t++)part[t]+=I.tab[t][at][x];go(go,at+1,b);for(int t=0;t<I.t;t++)part[t]-=I.tab[t][at][x];
  }
 };
 G(G,0,budget);
}
int main(int argc,char**argv){
 for(int a=0;a<17;a++){powr[a][0]=1;for(int j=1;j<=10;j++)powr[a][j]=m(powr[a][j-1]*a);for(int b=0;b<17;b++)if(m(a*b)==1)inv[a]=b;}
 for(int c=1;c<17;c++)for(unsigned b=1;b<=allbits;b++){int t=__builtin_ctz(b);perm[c][b]=perm[c][b&(b-1)]|(1<<m(c*t));}

 for(int d=6;d<=9;d++)profileGen(d);insertBank();
 cerr<<bank.size()<<" shifted profiles generated.\n";
 for(int i=0;i<sz;i++){int f=1;for(int j=0;j<sz;j++)if(j!=i)f=m(f*(S[i]-S[j]));wt[i]=inv[f];iw[i]=f;}
 for(int h=0;h<18;h++){
  if(argc>1&&h!=atoi(argv[1]))continue;
  scale=h;fill(begin(stats),end(stats),0);congr=phys=0;
  int a[sz],v[sz],l=-1,r=-1;
  for(int i=0;i<sz;i++){
   a[i]=m(wt[i]*(h==17?1:S[i]-h));
   if(a[i]){if(l<0)l=i;else if(r<0)r=i;}
  }
  for(int i=0;i<sz;i++)v[i]=m(wt[i]*(S[i]-S[l])*(S[i]-S[r]));
  for(int b=0;b<17;b++){
   int N[sz],total=0;
   for(int i=0;i<sz;i++){N[i]=root[a[i]][m(b*v[i])];total+=tree[N[i]].w;}
   rec(7,N,total);
  }
  if(h==0&&(congr||phys||stats[7]!=828259||stats[6]!=1339025||stats[5]))abort();
  if(h==10&&(congr||phys||stats[7]!=1059551||stats[6]!=1047614||stats[5]!=2||stats[4]))abort();
  cout<<"leading "<<h<<" congr "<<congr<<" physical "<<phys<<" stats";for(int j=7;j>=0;j--)cout<<" "<<stats[j];cout<<endl;
 }
}
