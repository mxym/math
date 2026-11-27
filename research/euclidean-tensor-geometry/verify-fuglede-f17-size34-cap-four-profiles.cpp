#include <algorithm>
#include <array>
#include <cstdio>
#include <cstdlib>
#include <numeric>
#include <stdexcept>
#include <vector>
using namespace std;
constexpr int P=17,MASS=34;
int mod(int x){x%=P;return x<0?x+P:x;}
int main(){
 int inv[P]={};for(int a=1;a<P;a++)for(int b=1;b<P;b++)if(a*b%P==1)inv[a]=b;
 for(const int cap: {4})for(int d=6;d<=10;d++){
  int B[P][P]={},eval[P][P]={};for(int i=0;i<=d;i++){
   vector<int> g{1};int den=1;
   for(int j=0;j<=d;j++)if(i!=j){vector<int> h(g.size()+1);for(size_t k=0;k<g.size();k++){h[k]=mod(h[k]-j*g[k]);h[k+1]=mod(h[k+1]+g[k]);}g.swap(h);den=mod(den*(i-j));}
   for(int k=0;k<=d;k++)B[i][k]=mod(g[k]*inv[den]);
   for(int x=0;x<P;x++){int t=0;for(int k=d;k>=0;k--)t=mod(t*x+B[i][k]);eval[x][i]=t;}
  }
  int r=-1,s=-1,det=0;for(int i=0;i<=d&&r<0;i++)for(int j=i+1;j<=d;j++){
   det=mod(B[i][d-1]*B[j][d]-B[j][d-1]*B[i][d]);if(det){r=i;s=j;break;}
  }
  if(r<0)throw logic_error("inverse coefficient rank");const int D=inv[det];
  vector<int> free;for(int j=0;j<=d;j++)if(j!=r&&j!=s)free.push_back(j);
  int vals[P]={},lead=1,g=gcd(d,P-1),mult=(P-1)/g;array<long long,200> hist{};
  auto rec=[&](auto&& self,int i,int mass,int squares,int pen,int top)->void{
   if(i<(int)free.size()){
    int j=free[i],hi=min(cap,MASS-mass),lo=max(0,MASS-mass-(P-1-i)*cap);
    for(int a=lo;a<=hi;a++){vals[j]=a;self(self,i+1,mass+a,squares+a*a,pen+a*B[j][d-1],top+a*B[j][d]);}
    return;
   }
   int e=lead-top,a=mod(D*(-pen*B[s][d]-e*B[s][d-1])),b=mod(D*(B[r][d-1]*e+B[r][d]*pen));
   if(a>cap||b>cap||mass+a+b>MASS)return;
   vals[r]=a;vals[s]=b;mass+=a+b;squares+=a*a+b*b;
   for(int j=d+1;j<P;j++){int u=0;for(int k=0;k<=d;k++)u+=vals[k]*eval[j][k];u%=P;
    if(u>cap||mass+u>MASS||mass+u+(P-1-j)*cap<MASS)return;mass+=u;squares+=u*u;
   }
   if(mass==MASS){if(squares<=68||squares%2)throw logic_error("nonuniform variance");hist[(squares-68)/2]+=mult;}
  };
  for(int i=0;i<g;i++){rec(rec,0,0,0,0,0);lead=mod(lead*3);}
  auto lo=find_if(hist.begin(),hist.end(),[](auto t){return bool(t);});
  auto hi=find_if(hist.rbegin(),hist.rend(),[](auto t){return bool(t);});
  const long long count=accumulate(hist.begin(),hist.end(),0LL);
  const int loValue=lo==hist.end()?-1:int(lo-hist.begin()),hiValue=hi==hist.rend()?-1:int(hist.rend()-hi-1);
  const long long wantCount[]={0,16,20,112,2096};
  const int wantMin[]={-1,17,8,12,8},wantMax[]={-1,17,32,22,27};
  if(count!=wantCount[d-6]||loValue!=wantMin[d-6]||hiValue!=wantMax[d-6])abort();
  printf("degree=%d centered_profiles=%lld 17w_min=%d 17w_max=%d\n",d,count,loValue,hiValue);
 }
}
