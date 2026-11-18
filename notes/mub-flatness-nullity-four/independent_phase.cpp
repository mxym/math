/* Separate full-candidate screen, computing Pauli entries directly by bra/ket
   products over ALL x rather than unique pairs. C++20, no third-party code. */
#include <array>
#include <bit>
#include <cstdlib>
#include <iostream>
#include <vector>
#include <map>
#include <set>
#include <utility>
#include <algorithm>
#include <numeric>
#include <complex>
using namespace std;
void need(bool x,const char* s){if(!x){cerr<<s<<'\n';exit(1);}}
int main(){
 const vector<vector<int>> supports={{0,1,2,4,8},{0,1,2,3,4,8},{0,1,2,4,8,15},{0,1,2,3,4,5,8},{0,1,2,3,4,8,12},{0,1,2,3,4,5,6,8},{0,1,2,3,4,5,8,9},{0,1,2,3,4,5,8,10}};
 using C=complex<int>;constexpr int scale=65*65;
 map<C,int,bool(*)(const C&,const C&)> inverse([](const C&a,const C&b){return make_pair(a.real(),a.imag())<make_pair(b.real(),b.imag());});
 C circ[36];for(int e=-1;e<2;e++)for(int f=-1;f<2;f++)for(int u=0;u<4;u++){
  int id=12*(1+e)+4*(1+f)+u;
  C z=C(e?3:5,e*4)*C(f?5:13,f*12);for(int k=0;k<u;k++) z*=C(0,1);circ[id]=z;
  need(norm(z)==scale && !inverse.count(z),"phase coordinate alias");inverse[z]=id;
 }
 bool compatible[36][36];int quo[36][36][2];
 for(int i=0;i<36;i++)for(int j=0;j<36;j++){
  auto t=circ[i]*conj(circ[j]);compatible[i][j]=t.real()%65==0&&t.imag()%65==0&&inverse.count(C(t.real()/65,t.imag()/65));
  quo[i][j][0]=t.real();quo[i][j][1]=-t.imag();
 }
 for(int row=0;row<8;row++){
  const auto&s=supports[row];int h=int(s.size());
  int ind[16];fill_n(ind,16,-1);for(int j=0;j<h;j++)ind[s[j]]=j;
  int component[8];iota(component,component+h,0);
  auto join=[&](int j,int k){int c=component[k],d=component[j];for(int a=0;a<h;a++)if(component[a]==c)component[a]=d;};
  for(int a=1;a<16;a++){vector<int> each;for(int j=0;j<h;j++)if(ind[s[j]^a]>=0)each.push_back(j);if(each.size()==2)join(each[0],each[1]);}
  vector<int> group;for(int j=0;j<h;j++){auto it=find(group.begin(),group.end(),component[j]);if(it==group.end()){group.push_back(component[j]);component[j]=int(group.size())-1;}else component[j]=int(it-group.begin());}
  need(component[0]==0,"group containing normalized reference");
  vector<array<int,8>> exps;
  // Enumerate ALL maps from components other than the first to {-1,0,1};
  // discard maps with two incompatible signs. This also counts the empty map just once.
  int limit=1;for(unsigned j=1;j<group.size();j++)limit*=3;
  for(int t=0;t<limit;t++){array<int,8> e{};int n=t;for(unsigned j=1;j<group.size();j++){e[j]=n%3-1;n/=3;}
   auto [lo,hi]=minmax_element(e.begin(),e.begin()+group.size());if(*hi-*lo<=1)exps.push_back(e);
  }
  // Fourth-root phase at frame vertices gauge fixed. Test with all ordered pairs x,x+a, no hand factor 2 and no orientation convention.
  vector<int> other;for(int j=0;j<h;j++)if(popcount(unsigned(s[j]))>1)other.push_back(j);
  array<array<int,8>,256> target{},sg{};array<int,256> comp{};vector<int> observables;
  for(int a=1;a<16;a++)for(int b=0;b<16;b++){int key=a+16*b;bool present=false;comp[key]=popcount(unsigned(a&b))&1;
   for(int j=0;j<h;j++){target[key][j]=ind[s[j]^a];if(target[key][j]>=0)present=true;sg[key][j]=(popcount(unsigned(s[j]&b))&1)?-1:1;}
   if(present)observables.push_back(key);
  }
  vector<bool> possible(scale*h+1);
  for(int j=h;j<=16;j++)for(int t=0;t<=j;t++)if((j-t)%2==0&& (scale*h*t)%j==0 && t<j)possible[scale*h*t/j]=true;
  long long all=0,passed=0;
  for(auto e:exps)for(auto f:exps)for(int k=0;k<(1<<(2*other.size()));k++){
   int id[8],bits=k,u[8]={};for(int i:other){u[i]=bits%4;bits/=4;}
   for(int j=0;j<h;j++) id[j]=12*(1+e[component[j]])+4*(1+f[component[j]])+u[j];
   all++;
   bool ok=true;
   for(auto p:observables){int val=0;for(int j=0;j<h;j++){int l=target[p][j];if(l>=0)val+=sg[p][j]*quo[id[j]][id[l]][comp[p]];}
    if(!possible.at(abs(val))){ok=false;break;}
   }
   if(ok){for(int j=0;j<h;j++)for(int l=0;l<h;l++)need(compatible[id[j]][id[l]],"incompatible ratio");passed++;cout<<row;for(int j=0;j<h;j++)cout<<" "<<id[j];cout<<"\n";}
  }
  const int pre[]={1,4,4,16,144,64,4161600,61504},post[]={1,4,4,16,16,64,56,64};need(pre[row]==all&&post[row]==passed,"count discrepancy");
  cerr<<row<<": "<<all<<" -> "<<passed<<"\n";
 }
}
