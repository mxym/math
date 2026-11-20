#include<bits/stdc++.h>
using namespace std;using U=bitset<160>;const int N=216+4*216,G=18;int cap[N],pairix[4][4];vector<int> feat[1296];struct O{vector<pair<int,int>> co;int w[4];int tag[3]={-1,-1,-1};};vector<O> ops[G];int lev[G];int typ[G],compg[G];bool need[N];vector<pair<int,int>> links;U tagm[G][3][16];U masks[G][216][5];long long nodes,cut=0;int scase;
bool go(int done,array<U,G> dom){++nodes;
 for(int j=0;j<G;j++)if(!(done>>j&1)){for(int p=dom[j]._Find_first();p<160;p=dom[j]._Find_next(p))for(auto [t,c]:ops[j][p].co)if(cap[t]<c){dom[j].reset(p);break;}if(dom[j].none())return false;}
 while(true){bool change=false;auto check=[&](int j,const U&v){auto z=dom[j]&v;if(z!=dom[j]){change=true;dom[j]=z;}return z.any();};
 for(auto [u,v]:links){int x=u/6,y=v/6;U r,s;for(int l=0;l<16;l++)if((tagm[u][y][l]&dom[u]).any()&&(tagm[v][x][l]&dom[v]).any())r|=tagm[u][y][l],s|=tagm[v][x][l];if(!check(u,r)||!check(v,s))return false;}
 for(int t=0;t<216;t++){int sumlo=0,sumhi=0;int lo[G],hi[G];for(int j=0;j<G;j++)if(!(done>>j&1)){int a=0,b=4;while((dom[j]&masks[j][t][a]).none())a++;while((dom[j]&masks[j][t][b]).none())b--;sumlo+=(lo[j]=a);sumhi+=(hi[j]=b);}
 if(sumlo>cap[t]||sumhi<cap[t])return false;if(sumlo==sumhi)continue;
 for(int j=0;j<G;j++)if(!(done>>j&1)){int a=max(lo[j],cap[t]-sumhi+hi[j]),b=min(hi[j],cap[t]-sumlo+lo[j]);U s;if(a==lo[j]&&b==hi[j])continue;for(int u=a;u<=b;u++)s|=masks[j][t][u];if(!check(j,s))return false;}}if(!change)break;}
 if(done==(1<<G)-1)return true;int j=-1;for(int i=0;i<G;i++)if(!(done>>i&1)&&(j<0||dom[i].count()<dom[j].count()))j=i;
 for(int p=dom[j]._Find_first();p<160;p=dom[j]._Find_next(p)){auto dd=dom;dd[j].reset();dd[j].set(p);lev[j]=p;for(auto [t,c]:ops[j][p].co)cap[t]-=c;if(go(done|1<<j,dd))return true;for(auto [t,c]:ops[j][p].co)cap[t]+=c;}return false;}
int main(int argc,char**av){int num=0;vector<pair<int,int>>E;for(int i=0;i<4;i++)for(int j=i+1;j<4;j++)pairix[i][j]=num++,E.emplace_back(i,j);for(int w=0;w<1296;w++){int a=w,v[4];for(auto&s:v)s=a%6,a/=6;for(auto [i,j]:E)feat[w].push_back(pairix[i][j]*36+6*v[i]+v[j]);for(int i=0;i<4;i++){int q=0;for(int j=0;j<4;j++)if(j!=i)q=6*q+v[j];feat[w].push_back(216+216*i+q);}}
 vector<array<int,4>>P;array<int,4>pp={0,1,2,3};do{if((pp[0]^pp[3])!=3)P.push_back(pp);}while(next_permutation(pp.begin(),pp.end()));array<U,G>dom;
 for(int i=0;i<3;i++)for(int ei=0;ei<6;ei++){int g=i*6+ei;auto [s,t]=E[ei];auto [u,v]=E[5-ei];int T=typ[g]=(ei!=0&&ei!=5);int R[4],k=0;for(int x=0;x<6;x++)if(x/2!=i)R[k++]=x;
 for(auto p:P)for(auto q:P){int n=0;for(int a=0;a<4;a++)n+=(p[a]/2==0&&q[a]/2==0);if(n!=T)continue;O o;map<int,int>marks;
 for(int b=0;b<4;b++){int V[4];V[s]=2*i+b/2;V[t]=2*i+b%2;V[u]=R[p[b]];V[v]=R[q[b]];int w=V[0]+6*(V[1]+6*(V[2]+6*V[3]));o.w[b]=w;int other=V[u]/2;if(V[v]/2==other){int tag=0;for(int a=0;a<4;a++)tag=2*tag+V[a]%2;o.tag[other]=tag;if(ei>=3)continue;}for(int j:feat[w])marks[j]++;}
 o.co.assign(marks.begin(),marks.end());int a=ops[g].size();ops[g].push_back(o);for(int r=0;r<216;r++)masks[g][r][marks[r]].set(a);for(int j=0;j<3;j++)if(o.tag[j]>=0)tagm[g][j][o.tag[j]].set(a);dom[g].set(a);}
 if(ei<=2&&T)for(int j=0;j<3;j++)if(j!=i)links.emplace_back(g,j*6+5-ei);}
 for(int t=0;t<N;t++)cap[t]=t>=216?1:2-(t%36/12==t%6/2);
 // represent the t=0 chart at wing 0 on pair 01 by a fixed table; enumerate every value (optional argv).
 for(int o=0;o<(int)ops[0].size();o++){if(argc>1&&o!=atoi(av[1]))continue;auto d=dom;d[0].reset();d[0].set(o);nodes=0;bool sat=go(0,d);cout<<o<<" "<<sat<<" "<<nodes<<endl;if(sat)return 0;}}
