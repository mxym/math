// Second implementation of the finite integer sieve. C++17; no LP or third-party libraries.
// Input: working directory containing spectrum.txt, headers.txt, histograms.txt.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <vector>
using namespace std;
using Shape=array<int,21>; using V=array<int,14>; using Allowed=array<array<vector<V>,2>,12>;
set<int> qw={0,64,96,112,120,128,136,144,160,192,256};
struct Case{int p,z;V s;}; map<Shape,Case> cases;
bool test(Shape h,int p,Case &res){
 int level=0, signs=0, q=0;
 for(int k=0;k<=20;k++){
  if(k%4==2)level+=h[k];
  if(p){int a=k%4==1?k:-k;signs+=a*h[k];if((abs(a-1)/4)%2)q+=h[k];}
  else if(k%8==4)q+=h[k];
 }
 int z=0;
 if(p){if(abs(signs)!=64||!qw.count(q))return false;z=255;}
 else{if(level%128)return false;if(!level&&!qw.count(q))return false;z=(level==128?256:0);}
 V c{};for(int i=0;i<=20;i++)for(int j=0;j<=20;j++){
  int n=h[i]*(h[j]-(i==j));if(!n)continue;
  if((i+j)>20)return false;
  c[(i+j)/2]+=n;c[abs(i-j)/2]+=n;
 }
 for(int i=0;i<11;i++){assert(!(c[i]%2));c[i]/=2;}
 // O shapes are precisely B+s*D+t*E; the two marginals can be tested separately.
 if(c[9]||c[7]>z)return false;
 int numer=c[5]-18*z+c[7];if(numer%4||numer<0||numer>4*z)return false;
 int S=numer/4,T=c[7];
 if(c[1]!=52*z+8*S+3*T||c[3]!=58*z-12*S-3*T)return false;
 int gen=c[2]+c[6]+c[10];if(gen%64)return false;gen/=64;
 if(gen>510-z||c[8]+c[10]>510-z||c[10]>gen||c[6]>11*gen)return false;
 c[11]=gen;c[12]=c[0]-c[4];c[13]=c[0]-2*c[4];res=Case{p,z,c};return true;
}
// Fix the maximum exactly, remove one mandatory maximum, and enumerate a multiset
// from the remaining levels. Its maximum is at most min(M,20-M). At the bottom
// the zeroth/second moments uniquely solve the two remaining counts.
void descend(Shape &h,int p,int level,int n,int norm){
 if(n<0||norm<p*p*n||norm>level*level*n)return;
 if(level<=p+2){
  int x=0;if(level==p){if(norm!=p*p*n)return;}else{
   int a=norm-p*p*n,b=level*level-p*p;if(a%b)return;x=a/b;if(x<0||x>n)return;
  }
  h[level]+=x;h[p]+=n-x;
  Case rec;if(test(h,p,rec))assert(cases.emplace(h,rec).second);
  h[level]-=x;h[p]-=n-x;return;
 }
 int step=level*level-p*p;
 for(int i=0;i<=min(n,(norm-p*p*n)/step);i++){
  h[level]+=i;descend(h,p,level-2,n-i,norm-level*level*i);h[level]-=i;
 }
}
vector<string> tokens(string x){istringstream in(x);string t;vector<string>v;while(in>>t)v.push_back(t);return v;}
void checkfiles(string dir){
 ifstream f(dir+"/histograms.txt");assert(f);string l;
 set<Shape> seen;while(getline(f,l)){auto t=tokens(l);assert(t.size()==36);int p=stoi(t[0]),z=stoi(t[1]),ng=stoi(t[2]);Shape h{};for(int i=0;i<21;i++)h[i]=stoi(t[i+3]);auto x=cases.at(h);assert(x.p==p&&x.z==z&&ng==x.s[11]);for(int j=0;j<11;j++)assert(x.s[j]==stoi(t[25+j]));assert(seen.insert(h).second);}assert(seen.size()==28&&seen.size()==cases.size());
}
int main(int argc,char**argv){
 assert(argc==2);string dir=argv[1];
 for(int p=0;p<=1;p++)for(int M=p;M<=20;M+=2){Shape h{};h[M]=1;descend(h,p,min(M,20-M),255,4096-M*M);}
 checkfiles(dir);
 ifstream in(dir+"/spectrum.txt");string l;getline(in,l);Allowed allowed;int cnt=0;while(getline(in,l)){
  auto t=tokens(l);assert(t.size()==28);V w{};for(int i=0;i<11;i++)w[i]=stoi(t[i]);int odd=w[1]!=0;
  int gc=w[2]+w[6]+w[10];assert(gc==0||gc==64);w[11]=gc/64;w[12]=w[0]-w[4];w[13]=w[0]-2*w[4];
  for(int j=0;j<12;j++)if(stoi(t[16+j]))allowed[j][odd].push_back(w);cnt++;
 }assert(cnt==14);
 ifstream hd(dir+"/headers.txt");getline(hd,l);set<int> head1;int singles=0,final=0,survivor=-1,lines=0,nzero=0,nbad=0;Shape sh{};
 while(getline(hd,l)){auto t=tokens(l);int id=stoi(t[0]),p=stoi(t[1]);string types=t[2];assert(types.size()==255&&id==lines++);vector<int> J(256);
  for(int a=1;a<256;a++)J[a]=stoi(types.substr(a-1,1),nullptr,16);
  bool zero=count(J.begin()+1,J.end(),11)>0, bad=count(J.begin()+1,J.end(),9)>0;
  nzero+=zero; nbad+=bad;assert(!zero||!bad);
  if(zero||bad)continue;
  for(int ell=0;ell<(p?1:256);ell++){
   int z=p?255:(ell?256:0), count[12][2]={};
   for(int a=1;a<256;a++){int odd=p?1:(2*__builtin_parity(unsigned(ell&a)));count[J[a]][0]+=2-odd;count[J[a]][1]+=odd;}
   bool ok=true;V lo{},hi{};for(int j=0;j<12;j++)for(int t=0;t<=1;t++)if(count[j][t]){
    auto &A=allowed[j][t];if(A.empty()){ok=false;continue;}
    for(int b=0;b<14;b++){int x=A.front()[b],y=x;for(auto v:A){x=min(x,v[b]);y=max(y,v[b]);}lo[b]+=x*count[j][t];hi[b]+=y*count[j][t];}
   }if(!ok)continue;
   for(auto const& [h,v]:cases){if(v.p!=p||v.z!=z||h[4]==256)continue;int n=0;while(n<14&&v.s[n]>=lo[n]&&v.s[n]<=hi[n])n++;
    if(n>=12){singles++;head1.insert(id);}if(n==14){final++;survivor=id;sh=h;assert(!ell);}
   }
  }
 }
 assert(lines==998&&nzero==11&&nbad==125);assert(head1==set<int>({130,134,168,358,563})&&singles==21);
 assert(final==1&&survivor==130&&sh[0]==48&&sh[4]==192&&sh[8]==16);
 cout<<"Independent integer enumeration: 28 identical absolute global histograms.\n";
 cout<<"Source-order headers: 11 with a zero restriction, 125 with type 9, disjoint; 862 others.\n";
 cout<<"Single-coordinate bounds: 21 triples on five headers. Compound-coordinate bounds: exactly one (head 130, residue slope 0; 48 zeros, 192 at 16, 16 at 32).\n";
}
