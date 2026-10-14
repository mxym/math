// Bounded exact rational discovery for the complete original Lih-Wang conjecture.
// All starts/trades have exact nonnegative integer margins K; A=M/K is DS.
// Finite nonviolations are not a positive theorem. A negative witness needs Python verification.
#include <array>
#include <vector>
#include <random>
#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <string>
#include <stdexcept>
#include <cstdint>
#include <cmath>
#include <boost/multiprecision/cpp_int.hpp>
using U=unsigned __int128;
using I=__int128;
using Big=boost::multiprecision::int256_t;
using Mat=std::array<std::array<int,10>,10>;
using Cof=std::array<std::array<U,10>,10>;
std::array<int,1024> pc;
std::string number(I v){if(v==0)return "0";bool neg=v<0;U x=neg?U(-v):U(v);std::string s;while(x){s.push_back(char('0'+x%10));x/=10;}if(neg)s.push_back('-');std::reverse(s.begin(),s.end());return s;}
U power(U a,int n){U out=1;while(n--)out*=a;return out;}
U fact(int n){U out=1;for(int i=2;i<=n;i++)out*=i;return out;}
U permanent(const Mat&a,int n){
 std::array<U,1024> d{};d[0]=1;int all=(1<<n)-1;
 for(int mask=0;mask<all;mask++){
  int row=pc[mask];U value=d[mask];if(!value)continue;int bits=all^mask;
  while(bits){int bit=bits&-bits;bits-=bit;int j=__builtin_ctz(unsigned(bit));if(a[row][j])d[mask|bit]+=value*U(a[row][j]);}
 }
 return d[all];
}
bool independent_permanent(const Mat&a,int n,U expected){
 Big sum=0;int all=(1<<n)-1;
 for(int mask=0;mask<=all;mask++){
  U product=1;
  for(int i=0;i<n;i++){int r=0;for(int j=0;j<n;j++)if(mask&(1<<j))r+=a[i][j];product*=U(r);}
  if((n-pc[mask])&1)sum-=Big(product);else sum+=Big(product);
 }
 return sum==Big(expected);
}
Cof minor2(const Mat&a,int n,int row1,int row2){
 std::array<int,10> rows{};int k=0;for(int i=0;i<n;i++)if(i!=row1&&i!=row2)rows[k++]=i;
 std::array<U,1024> d{};d[0]=1;int all=(1<<n)-1;
 for(int mask=0;mask<=all;mask++){
  int row=pc[mask];U value=d[mask];if(row>=n-2||!value)continue;int bits=all^mask;
  while(bits){int bit=bits&-bits;bits-=bit;int j=__builtin_ctz(unsigned(bit));if(a[rows[row]][j])d[mask|bit]+=value*U(a[rows[row]][j]);}
 }
 Cof out{};for(int c=0;c<n;c++)for(int dcol=c+1;dcol<n;dcol++)out[c][dcol]=out[dcol][c]=d[all^(1<<c)^(1<<dcol)];return out;
}
struct Case{int n,K,a,b;};
Mat mixed(const Mat&m,const Case&c){Mat out{};for(int i=0;i<c.n;i++)for(int j=0;j<c.n;j++)out[i][j]=c.a*c.n*m[i][j]+(c.b-c.a)*c.K;return out;}
bool legal(const Mat&m,const Case&c){
 for(int i=0;i<c.n;i++){int row=0;for(int j=0;j<c.n;j++){if(m[i][j]<0) return false;row+=m[i][j];}if(row!=c.K)return false;}
 for(int j=0;j<c.n;j++){int col=0;for(int i=0;i<c.n;i++)col+=m[i][j];if(col!=c.K)return false;}return true;
}
int64_t variance(const Mat&m,const Case&c){int64_t sum=0;for(int i=0;i<c.n;i++)for(int j=0;j<c.n;j++){int64_t v=c.n*m[i][j]-c.K;sum+=v*v;}return sum;}
I gap(const Case&c,U pm,U cm){return I(power(c.b,c.n-1)*(U(c.b-c.a)*power(c.K,c.n)*fact(c.n)+U(c.a)*power(c.n,c.n)*pm))-I(cm);}
bool less_score(I g1,int64_t s1,I g2,int64_t s2){return Big(g1)*s2<Big(g2)*s1;}
struct Move{int i=-1,j=-1,c=-1,d=-1,q=0;I dg=0,dp=0,dc=0;int64_t next_s=0;};
void apply_trade(Mat&m,const Move&v){m[v.i][v.c]-=v.q;m[v.j][v.d]-=v.q;m[v.i][v.d]+=v.q;m[v.j][v.c]+=v.q;}
Move best_move(const Mat&m,const Case&cs,I current,int64_t S){
 Mat C=mixed(m,cs);Move best;I bestg=current;int64_t bests=S;
 U coefficient=power(cs.b,cs.n-1)*U(cs.a)*power(cs.n,cs.n);
 I an2=I(cs.a*cs.n)*I(cs.a*cs.n);
 for(int i=0;i<cs.n;i++)for(int j=i+1;j<cs.n;j++){
  Cof mm=minor2(m,cs.n,i,j),mc=minor2(C,cs.n,i,j);
  std::array<I,10> wm{},wc{};
  for(int c=0;c<cs.n;c++)for(int x=0;x<cs.n;x++){int difference=m[j][x]-m[i][x];wm[c]+=I(mm[c][x])*difference;wc[c]+=I(mc[c][x])*difference;}
  for(int c=0;c<cs.n;c++)for(int d=c+1;d<cs.n;d++){
   int low=-std::min(m[i][d],m[j][c]),high=std::min(m[i][c],m[j][d]);
   int entrydiff=m[i][d]+m[j][c]-m[i][c]-m[j][d];
   for(int q=low;q<=high;q++){
    if(q==0)continue;
    int64_t ns=S+int64_t(cs.n)*cs.n*(int64_t(2)*q*entrydiff+int64_t(4)*q*q);
    if(ns<0)throw std::runtime_error("negative squared variance");if(ns==0)continue;
    I dp=I(q)*(wm[d]-wm[c])+I(2)*I(mm[c][d])*q*q;
    I dc=an2*(I(q)*(wc[d]-wc[c])+I(2)*I(mc[c][d])*q*q);
    I dg=I(coefficient)*dp-dc;I ng=current+dg;
    if(less_score(ng,ns,bestg,bests)){best={i,j,c,d,q,dg,dp,dc,ns};bestg=ng;bests=ns;if(ng<0)return best;}
   }
  }
 }
 return best;
}
bool random_move(Mat&m,const Case&c,std::mt19937_64&rng){
 int i=rng()%c.n,j=rng()%c.n,x=rng()%c.n,y=rng()%c.n;if(i==j||x==y)return false;
 int lo=-std::min(m[i][y],m[j][x]),hi=std::min(m[i][x],m[j][y]);if(hi==lo)return false;
 int q=lo+int(rng()%uint64_t(hi-lo+1));if(q==0)return false;apply_trade(m,{i,j,x,y,q});return true;
}
Mat start(const Case&c,std::mt19937_64&rng,int trial){
 Mat m{};std::array<int,10> p{};for(int i=0;i<c.n;i++)p[i]=i;
 int blocks=(trial%3==0?c.K:trial%3==1?5:2);int used=0;
 for(int z=0;z<blocks;z++){
  std::shuffle(p.begin(),p.begin()+c.n,rng);int weight=(c.K-used)/(blocks-z);used+=weight;
  for(int i=0;i<c.n;i++)m[i][p[i]]+=weight;
 }
 if(variance(m,c)==0)for(int i=0;i<20;i++)random_move(m,c,rng);
 if(!legal(m,c)||variance(m,c)==0)throw std::runtime_error("bad actual rational start");return m;
}
struct Result{Case c;uint64_t trials=0;bool seen=false;I bestgap=0;int64_t bestS=0;Mat matrix{};U pm=0,cm=0;};
void print_matrix(std::ostream&f,const Mat&m,int n){f<<'[';for(int i=0;i<n;i++){if(i)f<<',';f<<'[';for(int j=0;j<n;j++){if(j)f<<',';f<<m[i][j];}f<<']';}f<<']';}
int main(int argc,char**argv){
 double seconds=argc>1?std::stod(argv[1]):300;std::string output=argc>2?argv[2]:"lih-wang-transport-discovery.json";
 for(int i=0;i<1024;i++)pc[i]=__builtin_popcount(unsigned(i));
 std::vector<Result> results;for(auto ab:std::vector<std::array<int,2>>{{1,2},{3,8},{1,4},{1,8}})for(int n=5;n<=10;n++)results.push_back(Result{Case{n,(n<=8?8*n:n==9?63:60),ab[0],ab[1]}});
 for(const auto& r:results){const auto& c=r.c;Mat uniform{};for(int i=0;i<c.n;i++)for(int j=0;j<c.n;j++)uniform[i][j]=c.K/c.n;auto C=mixed(uniform,c);if(gap(c,permanent(uniform,c.n),permanent(C,c.n))!=0)throw std::runtime_error("uniform exact factor control failed");}
 std::mt19937_64 rng(20261014);uint64_t trials=0,moves=0,controls=0;bool potential=false;int witness=-1;
 auto begin=std::chrono::steady_clock::now();auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count();};
 auto save=[&](){
  std::ofstream f(output);f<<"{\n\"scope\":\"Bounded exact rational discovery for full original Lih-Wang; finite nonviolations do not prove any domain.\",\n";
  f<<"\"seed\":20261014,\"wall_seconds\":"<<elapsed()<<",\"trials\":"<<trials<<",\"accepted_exact_transport_moves\":"<<moves<<",\"inclusion_exclusion_controls\":"<<controls<<",\"potential_strict_counterexample\":"<<(potential?"true":"false")<<",\n\"best_by_case\":[";
  for(size_t z=0;z<results.size();z++){if(z)f<<',';const auto&r=results[z];const auto&c=r.c;f<<"\n{\"n\":"<<c.n<<",\"K\":"<<c.K<<",\"t_a\":"<<c.a<<",\"t_b\":"<<c.b<<",\"trials\":"<<r.trials<<",\"gap_integer\":";if(r.seen)f<<'\"'<<number(r.bestgap)<<'\"';else f<<"null";f<<",\"scaled_squared_variance\":"<<r.bestS<<",\"per_integer_matrix\":\""<<number(I(r.pm))<<"\",\"per_mixed_integer_matrix\":\""<<number(I(r.cm))<<"\",\"integer_matrix\":";print_matrix(f,r.matrix,c.n);f<<'}';}
  f<<"\n],\n\"potential_witness\":";
  if(witness<0)f<<"null";else{const auto&r=results[witness];const auto&c=r.c;f<<"{\"K\":"<<c.K<<",\"a\":"<<c.a<<",\"b\":"<<c.b<<",\"gap_integer\":\""<<number(r.bestgap)<<"\",\"integer_matrix\":";print_matrix(f,r.matrix,c.n);f<<'}';}
  f<<",\n\"coverage_limit\":\"Only bounded sampled rational M/K at n=5..10 and t=1/2,3/8,1/4,1/8. Neither the entire matrix polytope, real parameter interval nor all n are enumerated. Every negative claim requires the independent Python exact verifier.\"\n}\n";
 };
 save();std::cout<<"24 uniform exact factor controls passed"<<std::endl;
 while(elapsed()<seconds&&!potential){
  int index=trials%results.size();auto&r=results[index];const auto&c=r.c;Mat m=start(c,rng,int(trials));trials++;r.trials++;
  U pm=permanent(m,c.n),cm=permanent(mixed(m,c),c.n);I g=gap(c,pm,cm);int64_t S=variance(m,c);
  if(r.trials==1){if(!independent_permanent(m,c.n,pm)||!independent_permanent(mixed(m,c),c.n,cm))throw std::runtime_error("independent permanent control failed");controls+=2;}
  auto consider=[&](){if(!r.seen||less_score(g,S,r.bestgap,r.bestS)){r.seen=true;r.bestgap=g;r.bestS=S;r.matrix=m;r.pm=pm;r.cm=cm;}if(g<0){potential=true;witness=index;save();std::cout<<"POTENTIAL original-domain actual rational witness n="<<c.n<<" t="<<c.a<<'/'<<c.b<<" gap="<<number(g)<<std::endl;}};
  consider();
  for(int phase=0;phase<3&&!potential&&elapsed()<seconds;phase++){
   for(int step=0;step<60&&!potential&&elapsed()<seconds;step++){
    Move v=best_move(m,c,g,S);if(v.i<0)break;U oldp=pm,oldc=cm;I oldg=g;
    apply_trade(m,v);if(!legal(m,c))throw std::runtime_error("illegal accepted transport");
    pm=permanent(m,c.n);cm=permanent(mixed(m,c),c.n);g=gap(c,pm,cm);S=variance(m,c);
    if(I(pm)!=I(oldp)+v.dp||I(cm)!=I(oldc)+v.dc||g!=oldg+v.dg||S!=v.next_s)throw std::runtime_error("exact cofactor/full-DP transport control failed");
    moves++;consider();
   }
   if(potential)break;
   for(int j=0;j<20;j++)random_move(m,c,rng);
   if(!legal(m,c))throw std::runtime_error("illegal shake");
   if(variance(m,c)==0)random_move(m,c,rng);
   pm=permanent(m,c.n);cm=permanent(mixed(m,c),c.n);g=gap(c,pm,cm);S=variance(m,c);if(S==0)throw std::runtime_error("uniform shake score undefined");consider();
  }
  save();if(trials%24==0)std::cout<<"trials "<<trials<<" moves "<<moves<<" controls "<<controls<<" seconds "<<elapsed()<<std::endl;
 }
 save();std::cout<<"FINISHED trials "<<trials<<" moves "<<moves<<" controls "<<controls<<" seconds "<<elapsed()<<" potential "<<potential<<std::endl;
}
