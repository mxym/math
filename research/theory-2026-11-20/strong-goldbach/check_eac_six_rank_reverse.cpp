// Independent reverse-row search. Exponent vectors directly, prefix-order masks,
// rank over F_101, signed Leibniz determinants over Z. No floating point.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <set>
#include <vector>
using namespace std;
using Row=array<int,6>; using Mask=uint64_t;
struct Opt{Row a{},cdf{}; int size{},support{},code{};};
vector<Opt> opts[6]; Mask allowed[6][50][6]; Row mat[6],piv[6]; int invs[101],chosen[6],hist[7]; set<array<int,7>> result; long long modkept=0,falsepos=0; bool ok=true;
int permDet(const vector<Row>& a,const vector<int>& c){
 vector<int> ord=c;int total=0;
 do{int v=1;for(size_t j=0;j<c.size();j++){v*=a[j][ord[j]];for(size_t k=0;k<j;k++)if(ord[k]>ord[j])v=-v;}total+=v;}while(next_permutation(ord.begin(),ord.end()));return total;
}
bool scc(){ // two independent graph traversals from 0
 for(int rev=0;rev<2;rev++){int reached=1;
  for(int s=0;s<5;s++){int nxt=reached;for(int i=0;i<6;i++)if(reached&(1<<i))for(int j=0;j<6;j++)if(rev?mat[j][i]:mat[i][j])nxt|=1<<j; reached=nxt;}
  if(reached!=63)return false;
 }return true;
}
void terminal(){
 if(!scc())return;
 int t=0,r=0;for(int i=0;i<6;i++){t+=opts[i][chosen[i]].size==3;for(int j=0;j<i;j++)r+=mat[i][j]*mat[j][i];}
 if(2*r<(t?15:14))return;
 modkept++;
 vector<Row> B(6);for(int i=0;i<6;i++)for(int j=0;j<6;j++)B[i][j]=(i==j)-mat[i][j];
 for(int i=0;i<6;i++)for(int j=0;j<6;j++){vector<Row>a;vector<int> c; for(int k=0;k<6;k++){if(k!=i)a.push_back(B[k]);if(k!=j)c.push_back(k);}if(permDet(a,c)){falsepos++;return;}}
 const int det=permDet(vector<Row>(mat,mat+6),{0,1,2,3,4,5});
 array<int,7> id{};for(int i=0;i<6;i++)id[i]=opts[i][chosen[i]].code;id[6]=det;result.insert(id);hist[t]++;if(!det)ok=false;
}
void search(int i,int dim,array<Mask,6> candidates){
 if(i<0){terminal();return;}
 for(Mask m=candidates[i];m;m&=m-1){int n=__builtin_ctzll(m);const Opt& opt=opts[i][n];Row b;
  for(int j=0;j<6;j++)b[j]=(101+(i==j)-opt.a[j])%101;
  int h=-1;for(int j=0;j<6;j++){if(!b[j])continue;if(!piv[j][j]){h=j;break;}int f=b[j];for(int k=j;k<6;k++)b[k]=(b[k]+101*101-f*piv[j][k])%101;}
  if(h>=0 && dim==4)continue;
  if(h>=0){int u=invs[b[h]];for(int j=h;j<6;j++)piv[h][j]=b[j]*u%101;}
  mat[i]=opt.a;chosen[i]=n;auto nxt=candidates;for(int j=0;j<i;j++)nxt[j]&=allowed[i][n][j];search(i-1,dim+(h>=0),nxt);
  if(h>=0)piv[h].fill(0);
 }
}
int main(){
 for(int u=1;u<101;u++)for(int v=1;v<101;v++)if(u*v%101==1)invs[u]=v;
 for(int i=0;i<6;i++)for(int code=0;code<4096;code++){Opt o;o.code=code;int t=code;for(int j=5;j>=0;j--){o.a[j]=t%4;t/=4;o.size+=o.a[j];if(o.a[j])o.support|=1<<j;}
  if(o.a[i]||o.size<2||o.size>3)continue;int sum=0;for(int j=0;j<6;j++)o.cdf[j]=(sum+=o.a[j]);opts[i].push_back(o);}
 for(int i=0;i<6;i++){if(opts[i].size()!=50)return 2;for(int n=0;n<50;n++)for(int j=0;j<i;j++)for(int l=0;l<50;l++){
  const auto &later=opts[i][n],&earlier=opts[j][l];
  int repeated=earlier.support & later.support;
  if((repeated>>(i+1))!=0)continue; // target would have smaller input i AND j
  bool fail=earlier.size==later.size;for(int k=0;k<6;k++)if(earlier.cdf[k]<later.cdf[k])fail=false;
  if(!fail)allowed[i][n][j]|=Mask(1)<<l;
 }}
 array<Mask,6> all;all.fill((Mask(1)<<50)-1);search(5,0,all);
 printf("mod-101 terminals %lld false-positive %lld\n",modkept,falsepos);
 for(int i=0;i<7;i++)printf("triple %d exact %d\n",i,hist[i]);
 for(auto const &id:result){printf("chart");for(int a:id)printf(" %d",a);puts("");}return ok?0:1;
}
