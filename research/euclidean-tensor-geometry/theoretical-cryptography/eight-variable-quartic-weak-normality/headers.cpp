#include <cstdint>
// C++17. The first route contracts the complementary 4-vector twice in dimension 8.
// The other substitutes one coordinate into the quartic polynomial, retaining the
// grade-4 part in dimension 7, and computes radical dimension via matrix reduction.
#include <array>
#include <algorithm>
#include <string>
#include <vector>
#include <fstream>
#include <sstream>
#include <iostream>
#include <map>
#include <set>
#include <cassert>
using namespace std;
using form=array<unsigned char,256>;
using mat=uint64_t;
int bit(int u){return __builtin_ctz((unsigned)u);}
int parity(int u){return __builtin_parity((unsigned)u);}
int matrank(mat M){unsigned b[8]={};int r=0;for(int j=0;j<8;j++){unsigned x=(M>>(8*j))&255;while(x){int t=bit(x);if(!b[t]){b[t]=x;r++;break;}x^=b[t];}}return r;}
int rank2(mat M){int q=0;for(int j=0;j<8;j++){mat mask=UINT64_C(0x0101010101010101)<<j;mat hit=mask&M;if(!hit)continue;int row=__builtin_ctzll(hit)/8;auto R=(M>>(8*row))&255;for(int k=0;k<8;k++)if((M>>(8*k+j))&1)M^=R<<(8*k);q++;}return q;}
vector<form> read(const string&nm){ifstream in(nm);assert(in);string s;vector<form>out;while(getline(in,s))if(s.rfind("anf=",0)==0){form f{};stringstream w(s.substr(4));while(getline(w,s,'+')){if(s.empty()||s=="0")continue;int u=0;for(char c:s){assert(c>='a'&&c<='h');u|=1<<(c-'a');}assert(__builtin_popcount(u)==4);f[u]^=1;}out.push_back(f);}return out;}
using hist=array<int,4>;
struct ext{array<array<mat,8>,8> t{};ext(form f){
 for(int i=0;i<8;i++)for(int j=0;j<8;j++)if(i!=j)for(int a=0;a<8;a++)for(int b=0;b<8;b++)if(a!=b){int mask=(1<<i)|(1<<j)|(1<<a)|(1<<b);if(__builtin_popcount(mask)==4&&f[255^mask])t[i][j]|=uint64_t(1)<<(8*a+b);}
 }
 hist profile(int h){mat v[8]={}, all[256]={};hist H{};for(int i=0;i<8;i++)if(h>>i&1)for(int j=0;j<8;j++)v[j]^=t[i][j];
 for(int m=0;m<256;m++){if(m)all[m]=all[m&(m-1)]^v[bit(m)];if(m&(h&-h))continue;int r=matrank(all[m]);assert(r%2==0&&r<=6);H[r/2]++;}return H;}
};
form substitute(const form&f,int h){int p=bit(h);form v{};for(int m=0;m<256;m++)if(f[m]){int a=m&~(1<<p);auto del=[p](int z){return (z&((1<<p)-1))|((z>>(p+1))<<p);};if(a==m){v[del(m)]^=1;continue;}for(int j=0;j<8;j++)if(j!=p&&(h>>j&1)&&!(a>>j&1))v[del(a|1<<j)]^=1;}return v;}
hist profile2(const form&g){mat v[7]={},all[128]={};hist H{};for(int i=0;i<7;i++)for(int j=0;j<7;j++)for(int k=0;k<7;k++)if(j!=k&&j!=i&&k!=i){int mask=(1<<i)|(1<<j)|(1<<k);if(g[127^mask])v[i]|=uint64_t(1)<<(8*j+k);}
 for(int j=0;j<128;j++){if(j)all[j]=all[j&(j-1)]^v[bit(j)];int r=rank2(all[j]);assert(r%2==0&&r<=6);H[r/2]++;}return H;}
int main(int argc,char**argv){assert(argc==3);auto p=read(argv[1]),q=read(argv[2]);assert(p.size()==12&&q.size()==998);
 map<hist,int> sig;for(int i=0;i<12;i++){hist s=ext(p[i]).profile(128);assert(s==profile2(p[i])&&!sig.count(s));sig[s]=i;}
 cout<<"index quartic_q full_types_for_255_normals\n";
 for(int i=0;i<(int)q.size();i++){ext t(q[i]);int pf=0;for(int m=0;m<128;m++)pf^=q[i][m]&q[i][255^m];cout<<i<<" "<<pf<<" ";for(int h=1;h<=255;h++){auto s=t.profile(h),s2=profile2(substitute(q[i],h));if(s!=s2||!sig.count(s))throw 1;cout<<"0123456789AB"[sig.at(s)];}cout<<"\n";}}
