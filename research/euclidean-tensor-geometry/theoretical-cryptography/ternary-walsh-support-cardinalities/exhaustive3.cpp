#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <map>
#include <set>
#include <utility>
#include <vector>
using namespace std;
constexpr int N=9,F=19683;
using Row=array<int,N>;
pair<int,int> rot(pair<int,int> q){auto [a,b]=q;return {-b,a-b};}
int add3(int i,int j){return ((i%3+j%3)%3) + 3*((i/3+j/3)%3);}
int neg3(int i){return add3(i,i);}
int scale3(int a,int i){return a? a==1?i:neg3(i):0;}
int norm(Row f){int c=f[0],a=(3+f[1]-c)%3,b=(3+f[3]-c)%3;int z=0,w=1;
 for(int u=0;u<N;++u,w*=3){z+=w*((15+f[u]-c-a*(u%3)-b*(u/3))%3);}return z;}
int main(){
 vector<Row> words(F),spec(F);
 vector<pair<int,int>> coeff;
 vector<array<int,3>> histograms;
 map<pair<int,int>,int> ident;
 vector<int> masks(F);
 for(int z=0;z<F;z++){
  int t=z;for(int i=0;i<N;i++){words[z][i]=t%3;t/=3;}
  for(int u=0;u<N;u++){
   int h[3]={};for(int x=0;x<N;x++)h[(15+words[z][x]-(x%3)*(u%3)-(x/3)*(u/3))%3]++;
   pair<int,int> p={h[0]-h[2],h[1]-h[2]};
   if(!ident.count(p)){ident[p]=coeff.size();coeff.push_back(p);histograms.push_back({h[0],h[1],h[2]});}spec[z][u]=ident[p];
   if(p!=pair(0,0))masks[z]|=1<<u;
  }
 }
 const int M=coeff.size();assert(M==55);vector<uint8_t> w(M*M*M), bucket(M*M*M);
 for(int i=0;i<M;i++)for(int j=0;j<M;j++)for(int k=0;k<M;k++){
  auto [a,b]=coeff[i];const auto u=coeff[j],v=coeff[k];auto q=u,r=v;int s=0;
  for(int t=0;t<3;t++){s+=int(a+q.first+r.first!=0||b+q.second+r.second!=0);q=rot(q);r=rot(rot(r));}
  auto p=histograms[i],q0=histograms[j],r0=histograms[k];
  int h=0;
  for(int t=0;t<3;++t){
   int z[3];for(int a=0;a<3;++a)z[a]=p[a]+q0[(a+t)%3]+r0[(a+2*t)%3];
   h+=z[0]!=z[1]||z[0]!=z[2];
  }
  assert(h==s);
  w[(i*M+j)*M+k]=s;
  bucket[(i*M+k)*M+j]=h;
 }
 set<int> marked;vector<int> seeds;
 for(int p=0;p<F;p++)if(norm(words[p])==p&&!marked.count(p)){
  seeds.push_back(p);
  for(int u=1;u<N;u++)for(int v=1;v<N;v++)if(u!=v&&u!=neg3(v))for(int t=0;t<N;t++)for(int z=1;z<=2;z++){
   Row f;
   for(int x=0;x<N;x++)f[x]=z*words[p][add3(t,add3(scale3(x%3,u),scale3(x/3,v)))]%3;
   marked.insert(norm(f));
  }
 }
 assert(seeds.size()==11&&marked.size()==729);
 printf("n=3 slice representatives=%zu normalized 2D truth tables=%zu histogram types=%d\n",seeds.size(),marked.size(),M);fflush(stdout);
 array<uint64_t,14> hist{}, hist2{};
 for(int f:seeds){
  const int mf=masks[f];array<uint64_t,14> local{},second{};
  for(int g=0;g<F;g+=3){
   int mg=masks[g], u=mf|mg, I=mf&mg, X=mf^mg;
   const uint8_t* p[9];for(int a=0;a<9;a++)p[a]=&w[(spec[f][a]*M+spec[g][a])*M];
   for(int h=0;h<F;h++){
    int mh=masks[h];int once=(X&~mh)|(mh&~u),twice=(I&~mh)|(X&mh),third=I&mh;
    if(3*popcount(unsigned(once))+2*popcount(unsigned(twice))+popcount(unsigned(third))>13)continue;
    const auto& spec_h=spec[h];
    int s=0;for(int k=0;k<9;k++)s+=p[k][spec_h[k]];if(s>13)continue;
    local[s]++;hist[s]++;
   }
  }
  // Independent summation: use exact phase-residue buckets, order the two
  // inner slices oppositely, and use neither spectral masks nor the bound above.
  for(int h=0;h<F;h++){
   const uint8_t* p[9];for(int a=0;a<9;a++)p[a]=&bucket[(spec[f][a]*M+spec[h][a])*M];
   for(int g=0;g<F;g+=3){
    const auto& spec_g=spec[g];int s=0;
    for(int k=8;k>=0&&s<=13;k--)s+=p[k][spec_g[k]];
    if(s<=13){second[s]++;hist2[s]++;}
   }
  }
  assert(local==second);
  printf("seed %d:",f);for(int r=1;r<=13;r++)printf(" %llu",(unsigned long long)local[r]);printf("\n");fflush(stdout);
 }
 assert(hist==hist2&&hist[10]==0&&hist[11]==0&&hist[13]>0);
 assert((hist==array<uint64_t,14>{0,1,0,5,0,0,171,207,0,1803,0,0,3366,4446}));
 printf("n=3 total r=1..13:");for(int r=1;r<=13;r++)printf(" %llu",(unsigned long long)hist[r]);printf("\n");
 puts("PASS both exact 3D truth-table scans.");
}
