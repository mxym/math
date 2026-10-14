// Bounded exact discovery for the complete Ryser design minimum conjecture.
// N=13 is a potential negative witness location, not a partial positive target.
// Every permanent and two-switch difference is integer; randomness discovers only.
#include <array>
#include <vector>
#include <random>
#include <chrono>
#include <algorithm>
#include <iostream>
#include <fstream>
#include <string>
#include <stdexcept>
#include <cstdint>
using M=std::array<uint16_t,13>;
constexpr int n=13,all=(1<<13)-1;
std::array<uint8_t,1<<13> pc;
uint64_t per(const M&a){
 std::array<uint64_t,1<<13> dp{}; dp[0]=1;
 for(int mask=0;mask<=all;mask++){
  int row=pc[mask];if(row==n||!dp[mask])continue;
  int bits=a[row]&~mask;
  while(bits){int b=bits&-bits;bits-=b;dp[mask|b]+=dp[mask];}
 }
 return dp[all];
}
bool legal(const M&a,int k){
 for(int i=0;i<n;i++)if(pc[a[i]]!=k)return false;
 for(int j=0;j<n;j++){int s=0;for(auto r:a)s+=(r>>j)&1;if(s!=k)return false;}
 return true;
}
using Cof=std::array<std::array<uint64_t,13>,13>;
Cof cofactor2(const M&a,int i,int j){
 std::array<int,11> rows{};int p=0;
 for(int r=0;r<n;r++)if(r!=i&&r!=j)rows[p++]=r;
 std::array<uint64_t,1<<13> dp{};dp[0]=1;
 for(int mask=0;mask<=all;mask++){
  int row=pc[mask];if(row>=11||!dp[mask])continue;
  int bits=a[rows[row]]&~mask;
  while(bits){int b=bits&-bits;bits-=b;dp[mask|b]+=dp[mask];}
 }
 Cof c{};
 for(int r=0;r<n;r++)for(int s=r+1;s<n;s++)
  c[r][s]=c[s][r]=dp[all^(1<<r)^(1<<s)];
 return c;
}
struct Move{int i=-1,j=-1,c=-1,d=-1;int64_t delta=0;};
int64_t delta(const M&a,const Cof&m,int i,int j,int c,int d){
 int64_t wd=0,wc=0;
 for(int q=0;q<n;q++){
  int v=int((a[j]>>q)&1)-int((a[i]>>q)&1);
  wd+=int64_t(m[d][q])*v;wc+=int64_t(m[c][q])*v;
 }
 return wd-wc+2*int64_t(m[c][d]);
}
void apply_move(M&a,const Move&mv){
 a[mv.i]^=(1<<mv.c)|(1<<mv.d);
 a[mv.j]^=(1<<mv.c)|(1<<mv.d);
}
Move bestmove(const M&a){
 Move best;
 for(int i=0;i<n;i++)for(int j=i+1;j<n;j++){
  int cs=a[i]&~a[j],ds=a[j]&~a[i];if(!cs||!ds)continue;
  Cof m=cofactor2(a,i,j);
  std::array<int64_t,13>w{};
  for(int p=0;p<n;p++)for(int q=0;q<n;q++)
   w[p]+=int64_t(m[p][q])*(int((a[j]>>q)&1)-int((a[i]>>q)&1));
  for(int c=0;c<n;c++)if(cs&(1<<c))
   for(int d=0;d<n;d++)if(ds&(1<<d)){
    int64_t x=w[d]-w[c]+2*int64_t(m[c][d]);
    if(x<best.delta)best={i,j,c,d,x};
   }
 }
 return best;
}
int bitpick(int b,std::mt19937_64&rng){
 int count=pc[b],idx=rng()%count;
 while(idx--)b&=b-1;
 return __builtin_ctz(unsigned(b));
}
bool randomswitch(M&a,std::mt19937_64&rng){
 int i=rng()%n,j=rng()%n;if(i==j)return false;
 int cs=a[i]&~a[j],ds=a[j]&~a[i];if(!cs||!ds)return false;
 Move m{i,j,bitpick(cs,rng),bitpick(ds,rng),0};apply_move(a,m);return true;
}
bool longtrade(M&a,std::mt19937_64&rng){
 std::array<int,13> idx{};for(int i=0;i<n;i++)idx[i]=i;
 std::shuffle(idx.begin(),idx.end(),rng);
 int len=3+rng()%6;std::array<int,8>cols{};int used=0;
 for(int t=0;t<len;t++){
  int bs=a[idx[t]]&~used;if(!bs)return false;
  int c=bitpick(bs,rng);cols[t]=c;used|=1<<c;
 }
 for(int t=0;t<len;t++)if(a[idx[t]]&(1<<cols[(t+1)%len]))return false;
 for(int t=0;t<len;t++)a[idx[t]]^=(1<<cols[t])|(1<<cols[(t+1)%len]);
 return true;
}
M randomregular(int k,std::mt19937_64&rng){
 std::array<int,13>offset{};for(int i=0;i<n;i++)offset[i]=i;
 std::shuffle(offset.begin(),offset.end(),rng);M a{};
 for(int i=0;i<n;i++)for(int p=0;p<k;p++)a[i]|=1<<((i+offset[p])%n);
 for(int t=0;t<1500;t++)randomswitch(a,rng);
 if(!legal(a,k))throw std::runtime_error("illegal regular start");
 return a;
}
struct Result{int k;uint64_t baseline,best;M matrix{};int trials=0;uint64_t nonconfig_best=UINT64_MAX;M nonconfig_matrix{};};
bool configuration(const M&a,int k){int lam=k*(k-1)/(n-1);for(int i=0;i<n;i++)for(int j=0;j<i;j++)if(pc[a[i]&a[j]]!=lam)return false;return true;}
void save(const std::string&path,const std::array<Result,2>&r,int trials,int steps,int controls,double sec,bool potential){
 std::ofstream f(path);f<<"{\n\"scope\":\"Bounded actual-binary integer discovery only; no universal positive proof. A potential strict witness requires independent verifier.\",\n";
 f<<"\"n\":13,\"seed\":20261014,\"seconds\":"<<sec<<",\"total_trials\":"<<trials<<",\"descent_steps\":"<<steps<<",\"exact_delta_controls\":"<<controls<<",\"potential_counterexample\":"<<(potential?"true":"false")<<",\n\"best_by_row_sum\":[";
 for(int z=0;z<2;z++){if(z)f<<",";f<<"\n{\"k\":"<<r[z].k<<",\"configuration_baseline\":"<<r[z].baseline<<",\"best_exact_permanent\":"<<r[z].best<<",\"trials\":"<<r[z].trials<<",\"rows_as_bitmasks\":[";
  for(int i=0;i<n;i++){if(i)f<<",";f<<r[z].matrix[i];}f<<"],\"minimum_nonconfiguration_seen\":";if(r[z].nonconfig_best==UINT64_MAX)f<<"null";else f<<r[z].nonconfig_best;f<<",\"nonconfiguration_rows\":[";for(int i=0;i<n;i++){if(i)f<<",";f<<r[z].nonconfig_matrix[i];}f<<"]}";}
 f<<"\n]}\n";
}
int main(int argc,char**argv){
 int seconds=argc>1?std::stoi(argv[1]):600;
 std::string out=argc>2?argv[2]:"ryser-nonlocal-discovery.json";
 for(int i=0;i<=all;i++)pc[i]=__builtin_popcount(unsigned(i));
 std::mt19937_64 rng(20261014);
 M plane{1170,113,2584,4372,15,4674,2338,7169,1352,1572,897,2244,4264},comp{};
 for(int i=0;i<n;i++)comp[i]=all^plane[i];
 if(!legal(plane,4)||!legal(comp,9)||per(plane)!=3852||per(comp)!=64803969)
  throw std::runtime_error("independent Python baseline mismatch");
 int controls=0;
 for(auto base:{plane,comp})for(int trial=0;trial<12;trial++){
  M a=base;for(int t=0;t<100;t++)randomswitch(a,rng);
  int i=rng()%n,j=rng()%n;if(i==j){trial--;continue;}
  int cs=a[i]&~a[j],ds=a[j]&~a[i];if(!cs||!ds){trial--;continue;}
  int c=bitpick(cs,rng),d=bitpick(ds,rng);auto cof=cofactor2(a,i,j);
  int64_t dd=delta(a,cof,i,j,c,d);uint64_t old=per(a);
  apply_move(a,{i,j,c,d,dd});if(int64_t(per(a))!=int64_t(old)+dd)
   throw std::runtime_error("exact independent full-DP delta check failed");
  controls++;
 }
 std::array<Result,2>r{Result{4,3852,3852,plane},Result{9,64803969,64803969,comp}};
 int trials=0,steps=0;bool potential=false;auto start=std::chrono::steady_clock::now();
 auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();};
 std::cout<<"BASELINES_OK and "<<controls<<" exact delta controls passed"<<std::endl;
 save(out,r,0,0,controls,elapsed(),false);
 while(elapsed()<seconds&&!potential){
  int z=trials%2,k=r[z].k;M a=randomregular(k,rng);uint64_t value=per(a);trials++;r[z].trials++;
  for(int phase=0;phase<4&&elapsed()<seconds;phase++){
   if(!configuration(a,k)&&value<r[z].nonconfig_best){r[z].nonconfig_best=value;r[z].nonconfig_matrix=a;}
   for(int iter=0;iter<100&&elapsed()<seconds;iter++){
    Move mv=bestmove(a);if(mv.i<0)break;
    apply_move(a,mv);value=uint64_t(int64_t(value)+mv.delta);steps++;
    if(!legal(a,k)||per(a)!=value)throw std::runtime_error("accepted move audit failed");
    if(!configuration(a,k)&&value<r[z].nonconfig_best){r[z].nonconfig_best=value;r[z].nonconfig_matrix=a;}
    if(value<r[z].best){r[z].best=value;r[z].matrix=a;save(out,r,trials,steps,controls,elapsed(),value<r[z].baseline);}
    if(value<r[z].baseline){potential=true;std::cout<<"POTENTIAL_ACTUAL_BINARY_WITNESS k="<<k<<" permanent="<<value<<std::endl;break;}
   }
   if(potential)break;
   for(int t=0;t<100;t++)if(longtrade(a,rng)){if(t>12)break;}
   if(!legal(a,k))throw std::runtime_error("illegal alternating cycle trade");
   value=per(a);
  }
  if(trials%10==0){save(out,r,trials,steps,controls,elapsed(),potential);std::cout<<"trials "<<trials<<" steps "<<steps<<" seconds "<<elapsed()<<" best4 "<<r[0].best<<" best9 "<<r[1].best<<std::endl;}
 }
 save(out,r,trials,steps,controls,elapsed(),potential);
 std::cout<<"FINISHED trials "<<trials<<" steps "<<steps<<" seconds "<<elapsed()<<" potential "<<potential<<std::endl;
 return 0;
}
