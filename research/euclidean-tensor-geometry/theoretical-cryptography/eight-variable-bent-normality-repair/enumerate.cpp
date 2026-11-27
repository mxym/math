// Finite mathematical verification, C++17. Input: the authors' listed abnormal representatives.
// Compile with -O3 and run on source data (pin the input in the wrapper before relying on coverage).
#include <algorithm>
#include <array>
#include <cctype>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <limits>
#include <cstdlib>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
using namespace std;
using U=uint64_t; using TV=array<unsigned char,128>; using Co=array<U,128>;
static void ck(bool ok, const string&m){if(!ok)throw runtime_error(m);}
static int dot(int x,int y){return __builtin_parity((unsigned)(x&y));}
static U mix(U x){x^=x>>30;x*=U(0xbf58476d1ce4e5b9);x^=x>>27;x*=U(0x94d049bb133111eb);return x^(x>>31);}
struct Pal {Co c,key;};
static array<array<unsigned char,64>,254> planes;
static array<array<unsigned char,127>,128> thru;
static void geometry(){array<int,254>a{};array<int,128>b{};for(int x=0;x<128;x++)for(int u=1;u<128;u++){int h=(u-1)*2+dot(x,u);planes[h][a[h]++]=x;thru[x][b[x]++]=h;}}
static Pal paint(const TV&s, int marked=-1){
 Pal p;for(int x=0;x<128;x++)p.c[x]=1+s[x]+(x==marked?100:0);
 for(int r=0;r<3;r++){Co v;for(int x=0;x<128;x++)v[x]=mix(p.c[x]);
  array<U,254> h;for(int i=0;i<254;i++){U z=0;for(int x:planes[i])z+=v[x];h[i]=mix(z);}
  for(int x=0;x<128;x++){U z=v[x];for(int i:thru[x])z+=h[i];p.c[x]=z;}}
 p.key=p.c;sort(p.key.begin(),p.key.end());return p;
}
struct Rec{TV f,s;};
static int records=0;
static vector<Rec> read_data(const string&fn, bool filter){
 ifstream in(fn);ck(bool(in),"source unavailable");vector<Rec> out;string l;int n=0;
 while(getline(in,l))if(l.rfind("anf=",0)==0){n++;TV v{}; stringstream z(l.substr(4));string t;
  while(getline(z,t,'+')){ck(!t.empty(),"empty monomial");int mask=0;
   for(char c:t){ck(c>='a'&&c<='g',"source contains unsupported symbol");mask|=1<<(c-'a');}v[mask]^=1;}
  for(int j=1;j<128;j*=2)for(int x=0;x<128;x++)if(x&j)v[x]^=v[x^j];
  TV s{};bool near=true;for(int u=0;u<128;u++){int w=0;for(int x=0;x<128;x++)w+=1-2*(v[x]^dot(x,u));
    if(w!=0&&abs(w)!=16)near=false;s[u]=w!=0;}
  if(!near){ck(filter,"source ANF not near-bent");continue;}out.push_back({v,s});}
 records=n;cerr<<"ANFs "<<n<<" near-bent "<<out.size()<<"\n";return out;
}
struct FlatDir{array<array<unsigned char,8>,16> cos;}; static vector<FlatDir> flats;
static array<unsigned char,256> slope;
static void all_flats(){
 for(int a=0;a<8;a++)for(int c=0;c<2;c++){int pat=0;for(int k=0;k<8;k++)pat|=(dot(k,a)^c)<<k;slope[pat]=1<<a;}
 for(int i=0;i<7;i++)for(int j=i+1;j<7;j++)for(int k=j+1;k<7;k++){
 int p[3]={i,j,k}, pm=(1<<i)|(1<<j)|(1<<k);vector<pair<int,int>> entries;
 for(int r=0;r<3;r++)for(int h=p[r]+1;h<7;h++)if(!(pm&(1<<h)))entries.emplace_back(r,h);
 for(int pat=0;pat<(1<<entries.size());pat++){int v[3]={1<<i,1<<j,1<<k};for(int e=0;e<(int)entries.size();e++)if((pat>>e)&1)v[entries[e].first]|=1<<entries[e].second;
 FlatDir fd;int row=0;for(int x=0;x<128;x++)if(!(x&pm)){
 for(int s=0;s<8;s++)fd.cos[row][s]=x^(s&1?v[0]:0)^(s&2?v[1]:0)^(s&4?v[2]:0);row++;}
 ck(row==16,"flat error");flats.push_back(fd);}}
 ck(flats.size()==11811,"wrong number of 3-directions");
}
static int slope_mask(const TV&v,const FlatDir&d){int m=0;for(const auto&c:d.cos){
 int t=0;for(int k=0;k<8;k++)t|=v[c[k]]<<k;m|=slope[t];}return m;}
struct Support{TV s;Pal p;bool hard;vector<Pal> marks;int anchor;
 explicit Support(TV z):s(z),p(paint(z)),hard(false),anchor(0){
 int dif=1;for(int i=1;i<128;i++)dif+=p.key[i]!=p.key[i-1];
 hard=dif<=4;
 if(hard){for(int a=0;a<128;a++)marks.push_back(paint(s,a));
 int best=129;for(int a=0;a<128;a++){int n=0;for(const auto&t:marks)n+=t.key==marks[a].key;if(n<best){best=n;anchor=a;}}}
 else{int best=129;for(int a=0;a<128;a++){int n=count(p.c.begin(),p.c.end(),p.c[a]);if(n<best){best=n;anchor=a;}}}
 }};
static vector<Rec> funcs;static vector<Support> src,tar;static vector<array<unsigned char,128>> lowcache;
static ostream *trace=nullptr;
static long long align=0,positive=0,pairs=0,globaltries=0;static int maxflat=0;
struct Search{
 int i,j,a,b;const Support& q;const Support& dest;const Pal &cp,&ct;array<int,128>X{},Y{},mapv{};array<vector<int>,7> opts;long long ctmap=0;
 Search(int i,int j,int b):i(i),j(j),a(src[j].anchor),b(b),q(src[j]),dest(tar[i]),cp(q.hard?q.marks[a]:q.p),ct(q.hard?dest.marks[b]:dest.p){}
 void basis(){
  bool used[128]={}; used[a]=true;X[0]=a;
  for(int k=0;k<7;k++){int t=1<<k,choice=-1,best=129;
   for(int x=0;x<128;x++)if(!used[x]){
    int n=count(cp.c.begin(),cp.c.end(),cp.c[x]);if(n<best){best=n;choice=x;}}
   ck(choice>=0,"basis failed");for(int y=0;y<128;y++)if(ct.c[y]==cp.c[choice]&&dest.s[y]==q.s[choice])opts[k].push_back(y);
   for(int r=0;r<t;r++){X[t+r]=X[r]^choice^a;used[X[t+r]]=true;}
  }
 }
 void check_flat(){
  for(int r=0;r<128;r++)mapv[X[r]]=Y[r];
  int offset=mapv[0];int col[7];for(int k=0;k<7;k++)col[k]=mapv[1<<k]^offset;
  // mapv sends support(q) to the complement of support(p); transpose acts on inputs.
  TV hi;for(int x=0;x<128;x++){int z=0;for(int k=0;k<7;k++)z|=dot(col[k],x)<<k;
   hi[x]=funcs[j].f[z]^dot(offset,x);}
  for(int f=0;f<(int)flats.size();f++){int m=(f<128?lowcache[i][f]:slope_mask(funcs[i].f,flats[f]));
   int common=m&slope_mask(hi,flats[f]);
   if(common){
     if(trace){
       const auto &d=flats[f];
       auto base=[&](const TV& v){for(const auto& c:d.cos){int t=0;
         for(int k=0;k<8;k++)t|=v[c[k]]<<k;
         if(slope[t]&(common&-common))return int(c[0]);
       }throw runtime_error("cannot recover witness");};
       *trace<<i<<' '<<j<<' '<<offset;
       for(int v:col)*trace<<' '<<v;
       for(int t:{1,2,4})*trace<<' '<<int(d.cos[0][t]^d.cos[0][0]);
       *trace<<' '<<base(funcs[i].f)<<' '<<base(hi)<<'\n';
     }
     maxflat=max(maxflat,f);globaltries+=f+1;return;
   }}
  cerr<<"NO COMMON SLOPE: i="<<i<<" j="<<j<<" offset="<<offset<<" cols";for(int c:col)cerr<<" "<<c;cerr<<"\n";throw runtime_error("no transversal affine four-flat");
 }
 void go(int k){if(k==7){ctmap++;check_flat();return;}
  int t=1<<k;
  for(int y:opts[k]){if(find(Y.begin(),Y.begin()+t,y)!=Y.begin()+t)continue;
   bool ok=true;for(int r=0;r<t;r++){int u=Y[r]^y^b;Y[r+t]=u;
    if(cp.c[X[r+t]]!=ct.c[u]||q.s[X[r+t]]!=dest.s[u]){ok=false;break;}}
   if(ok)go(k+1);
  }
 }
 long long run(){if(cp.key!=ct.key||q.s[a]!=dest.s[b]||cp.c[a]!=ct.c[b])return 0;
  basis();Y[0]=b;go(0);return ctmap;}
};
int main(int ac,char**av){try{
 static_assert(numeric_limits<U>::digits==64,"unsigned 64-bit type required");
 ck(ac==3||ac==5,"usage: enumerate SOURCE {count-raw|reduced} [--trace OUTPUT]");
 string mode=av[2];
 if(mode=="count-raw"){ck(ac==3,"count-raw takes no --trace");auto v=read_data(av[1],true);
   ck(records==39952&&v.size()==4085,"unexpected raw count");return 0;}
 ck(mode=="reduced","expected reduced or count-raw");
 ofstream out;if(ac==5){ck(string(av[3])=="--trace","expected --trace");
   out.open(av[4]);ck(bool(out),"cannot write trace");trace=&out;}
 geometry();all_flats();funcs=read_data(av[1],false);int n=funcs.size();int beg=0,end=n;
 ck(records==1309&&n==1309,"unexpected reduced input size");
 map<Co,vector<int>> groups;src.reserve(n);tar.reserve(n);lowcache.resize(n);
 for(int i=0;i<n;i++){TV c=funcs[i].s;for(auto&v:c)v^=1;src.emplace_back(funcs[i].s);tar.emplace_back(c);groups[src[i].p.key].push_back(i);
 for(int k=0;k<128;k++)lowcache[i][k]=slope_mask(funcs[i].f,flats[k]);}
 cerr<<"profiles ready: "<<groups.size()<<" distinct sorted color signatures\n";long long hard=0;
 for(int i=beg;i<end;i++){auto it=groups.find(tar[i].p.key);if(it==groups.end())continue;
 for(int j:it->second){pairs++;const Support& q=src[j];const Support& d=tar[i];long long m=0;
  for(int b=0;b<128;b++)if(q.p.c[q.anchor]==d.p.c[b]&&q.s[q.anchor]==d.s[b]){Search t(i,j,b);m+=t.run();}
  if(m){positive++;align+=m;if(q.hard)hard+=m;}
 }
 if(i%100==0)cerr<<"lower "<<i<<" positive "<<positive<<" maps "<<align<<"\n";}
 cout<<"profile candidate ordered pairs "<<pairs<<"; exact positive pairs "<<positive<<"; verified affine alignments "<<align
 <<"; hard maps "<<hard<<"; maximum flat index "<<maxflat<<"; total directions tried "<<globaltries<<"\n";
 ck(pairs==11662&&positive==11568&&align==37132,"unexpected complete enumeration totals");
 if(trace){out.flush();ck(bool(out),"incomplete trace");}
 return 0;
 }catch(const exception&e){cerr<<e.what()<<"\n";return 1;}}
