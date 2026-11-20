#include <bits/stdc++.h>
using namespace std;
const int N=1024,d=5;
int M[4][N],bar[N],pj[N],V[N],num;bool orth[N][N];vector<array<int,N>> G;long long ops;
int mu(int a,int b){static int m[4][4]={{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};return m[a][b];}
int dot(int x,int y){int v=0;while(x&&y){v^=mu(x&3,y&3);x>>=2;y>>=2;}return v;}
array<int,N> trans(array<int,5> b){array<int,N>T;T.fill(-1);for(int z=0;z<N;z++){int x=0;for(int j=0;j<5;j++)x^=M[(z>>(2*j))&3][b[j]];assert(T[x]<0);T[x]=z;}return T;}
array<int,N> frame(array<int,5> c,int y){
 array<int,5> b;copy(c.begin(),c.begin()+4,b.begin());b[4]=y;auto t=trans(b);int f=t[c[4]];assert(f<256);
 for(int j=0;j<4;j++){int s=(f>>(2*j))&3;assert(s);b[j]=M[s][b[j]];}return trans(b);
}
vector<int> anchor{1,4,16,64,85,256};
void init(){
 for(int i=0;i<N;i++)for(int a=0;a<4;a++){int v=0,z=0;for(int j=0;j<5;j++){int t=i>>(2*j)&3;v|=mu(a,t)<<(2*j);z|=mu(t,t)<<(2*j);}M[a][i]=v;bar[i]=z;}
 for(int i=1;i<N;i++){int j=i;while(!(j&3))j>>=2;pj[i]=M[mu(j&3,j&3)][i];if(pj[i]==i)V[num++]=i;}assert(num==341);
 for(int i=0;i<num;i++)for(int j=0;j<num;j++)orth[V[i]][V[j]]=dot(V[i],V[j])==0;
 array<int,5> c{1,4,16,64,85};do{auto t=frame(c,256);for(int a=1;a<4;a++)for(int q=0;q<2;q++){array<int,N>h{};for(int x=0;x<N;x++){int v=t[x];v=(v&255)^M[a][v&768];h[x]=pj[q?bar[v]:v];}G.push_back(h);}}while(next_permutation(c.begin(),c.end()));assert(G.size()==720);
}
using vec=vector<int>;
vec canon(const vec&A){
 int n=A.size();vector<array<int,7>> sig;vector<array<int,5>> cs;vector<uint64_t> colors(n);
 for(int k=0;k<num;k++){int h=V[k],s=0;unsigned m=0;for(int j=0;j<n;j++)if(orth[h][A[j]]){s++;m|=1u<<j;}
 assert(s<=5);if(s>=2)for(int j=0;j<n;j++)if(m>>j&1)colors[j]+=1ull<<(10*s);
 if(s==5){array<int,5>c;int l=0;for(int j=0;j<n;j++)if(m>>j&1)c[l++]=j;cs.push_back(c);}}
 assert(!cs.empty());array<uint64_t,6> ls;ls.fill(~0ull);vec best;array<int,5> c;
 for(auto idx:cs)for(int y=0;y<n;y++){
  if(find(idx.begin(),idx.end(),y)!=idx.end())continue;
  array<uint64_t,6> sig;for(int i=0;i<5;i++)sig[i]=colors[idx[i]];sort(sig.begin(),sig.begin()+5);sig[5]=colors[y];
  if(sig>ls)continue;if(sig<ls){ls=sig;best.clear();}
  for(int i=0;i<5;i++)c[i]=A[idx[i]];auto t=frame(c,A[y]);vec z;for(int j=0;j<n;j++)if(j!=y&&find(idx.begin(),idx.end(),j)==idx.end())z.push_back(pj[t[A[j]]]);
  for(auto&g:G){vec b;for(int v:z)b.push_back(g[v]);sort(b.begin(),b.end());if(best.empty()||b<best)best=b;}ops++;
 }
 vec r=anchor;r.insert(r.end(),best.begin(),best.end());sort(r.begin(),r.end());return r;
}

using bits=bitset<1024>;
using Ar = array<int,N>;
vector<Ar> GG,Aut;int nu,hn,tot,goal,nodesmax;vec A;bits allow,neigh[1024],pencils[341][4];int cap[341],wh[341],fval[1024][341],rem[341][4];int edgeO[1024];vector<vec> orbs;
void initG(){
 array<int,5> ci{1,4,16,64,85};do{auto t=frame(ci,256);
 for(int a=1;a<=3;a++)for(int q=0;q<2;q++){Ar g;for(int x=0;x<N;x++){int u=t[x];u=(u&255)^M[a][u&768];g[x]=q?bar[u]:u;}GG.emplace_back(g);}
 }while(next_permutation(ci.begin(),ci.end()));
}
void setup(){
 int sz=A.size();bits mask,s;for(int x:A)mask.set(x);Aut.clear();unordered_set<string> seen;
 for(int ki=0;ki<num;ki++){
  int h=V[ki],m=0;array<int,5> c;
  for(int x:A)if(orth[h][x]){assert(m<=4);c[m++]=x;}
  if(m!=5)continue;
  for(int y:A)if(!orth[h][y]){
   auto t=frame(c,y);
   for(auto&g:GG){bool ok=true;for(int u:A)if(!mask[pj[g[t[u]]]]){ok=0;break;}if(!ok)continue;
    for(int a=1;a<=3;a++){
     string key;for(int b:{1,4,16,64,256,2}){int j=M[a][g[t[b]]];key+=to_string(j)+".";}
     if(!seen.insert(key).second)continue;
     Ar B;for(int i=0;i<N;i++)B[i]=M[a][g[t[i]]];Aut.push_back(move(B));
    }
   }
  }
 }
 allow.set();allow.reset(0);for(int u:A)for(int v:A)for(int s=0;s<4;s++)for(int t=0;t<4;t++)allow.reset(M[s][u]^M[t][v]);
 fill(edgeO,edgeO+1024,-1);orbs.clear();for(int x=1;x<N;x++)if(allow[x]&&edgeO[x]<0){int i=orbs.size();set<int>o;for(auto&B:Aut)o.insert(B[x]);vec V(o.begin(),o.end());for(int y:V){assert(allow[y]&&edgeO[y]<0);edgeO[y]=i;}orbs.push_back(V);}
 sort(orbs.begin(),orbs.end(),[](auto&x,auto&y){return x.size()!=y.size()?x.size()>y.size():x[0]<y[0];});for(int i=0;i<orbs.size();i++)for(int x:orbs[i])edgeO[x]=i;
 for(int k=0;k<num;k++){wh[k]=V[k];int c=0;for(int x:A)c+=orth[V[k]][x];cap[k]=hn-c;for(int b=0;b<4;b++)pencils[k][b].reset();
  for(int i=0;i<N;i++){int v=dot(wh[k],i);fval[i][k]=v;pencils[k][v].set(i);}}
}
