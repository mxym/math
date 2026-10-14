// Exact bounded single-cycle trades inside the five saved PG(2,3) matching orbits.
// A strict actual binary witness would disprove the whole Ryser conjecture.
// A bounded nonviolation is neither a positive theorem nor exhaustive regular enumeration.
#include <array>
#include <vector>
#include <chrono>
#include <fstream>
#include <iostream>
#include <cstdint>
#include <stdexcept>
#include <string>
using M=std::array<uint16_t,13>;
#include "ryser_hamiltonian_representatives.hpp"
constexpr int n=13,all=(1<<13)-1;
std::array<uint8_t,1<<13> pc;
uint64_t per(const M& a){
 std::array<uint64_t,1<<13> d{};d[0]=1;
 for(int mask=0;mask<all;mask++){
  int i=pc[mask];auto value=d[mask];if(!value)continue;
  int bits=a[i]&~mask;
  while(bits){int bit=bits&-bits;bits-=bit;d[mask|bit]+=value;}
 }
 return d[all];
}
uint64_t ryser(const M& a){
 int64_t value=0;
 for(int mask=0;mask<=all;mask++){
  int64_t product=1;
  for(auto row:a)product*=pc[row&mask];
  value+=((n-pc[mask])&1)?-product:product;
 }
 if(value<0)throw std::runtime_error("negative permanent");return uint64_t(value);
}
bool legal(const M& a,int k){
 for(auto row:a)if(pc[row]!=k)return false;
 for(int j=0;j<n;j++){int sum=0;for(auto row:a)sum+=(row>>j)&1;if(sum!=k)return false;}
 return true;
}
struct Cell{int rep,len;uint64_t count=0;bool complete=false;uint64_t best4=UINT64_MAX,best9=UINT64_MAX;};
int main(int argc,char** argv){
 int maxlen=argc>1?std::stoi(argv[1]):7;
 int minlen=argc>4?std::stoi(argv[4]):2;
 double seconds=argc>2?std::stod(argv[2]):180;
 std::string output=argc>3?argv[3]:"ryser-matching-cycle-discovery.json";
 for(int i=0;i<=all;i++)pc[i]=__builtin_popcount(unsigned(i));
 for(const auto& a:representatives)if(!legal(a,4)||per(a)!=3852||ryser(a)!=3852)throw std::runtime_error("plane representative check failed");
 auto starttime=std::chrono::steady_clock::now();
 auto elapsed=[&](){return std::chrono::duration<double>(std::chrono::steady_clock::now()-starttime).count();};
 uint64_t total=0,controls=0,best4=3852,best9=64803969;
 M matrix4{},matrix9{};bool potential=false,expired=false;
 std::vector<Cell> cells;std::vector<int> path;
 auto save=[&](){
  std::ofstream f(output);
  f<<"{\n\"scope\":\"Bounded exact matching-orbit single-cycle discovery; no full Ryser result or exhaustive regular enumeration.\",\n";
  f<<"\"n\":13,\"max_cycle_length\":"<<maxlen<<",\"wall_seconds\":"<<elapsed()<<",\"actual_binary_candidates\":"<<total<<",\"independent_inclusion_exclusion_controls\":"<<controls<<",\"potential_strict_counterexample\":"<<(potential?"true":"false")<<",\n";
  f<<"\"best_permanent_k4\":"<<best4<<",\"baseline_k4\":3852,\"best_permanent_k9\":"<<best9<<",\"baseline_k9\":64803969,\n";
  f<<"\"best_matrix_k4_rows\":[";for(int i=0;i<n;i++){if(i)f<<',';f<<matrix4[i];}f<<"],\n\"best_matrix_k9_rows\":[";for(int i=0;i<n;i++){if(i)f<<',';f<<matrix9[i];}f<<"],\n\"cells\":[";
  for(size_t z=0;z<cells.size();z++){
   if(z)f<<',';const auto& c=cells[z];
   f<<"\n{\"rep\":"<<c.rep<<",\"cycle_length\":"<<c.len<<",\"count\":"<<c.count<<",\"completed_within_this_representative\":"<<(c.complete?"true":"false")<<",\"smallest_k4_seen\":";
   if(c.best4==UINT64_MAX)f<<"null";else f<<c.best4;f<<",\"smallest_k9_seen\":";
   if(c.best9==UINT64_MAX)f<<"null";else f<<c.best9;f<<'}';
  }
  f<<"\n],\n\"coverage_limit\":\"Only cycles whose removed partial matching extends to the saved complete incidence matching are represented; longer cycles, other regular matrices, and any incomplete cell remain outside the search.\"\n}\n";
 };
 matrix4=representatives[0];for(int i=0;i<n;i++)matrix9[i]=all^matrix4[i];save();
 for(int length=minlen;length<=maxlen&&!expired&&!potential;length++)for(int rep=0;rep<int(representatives.size())&&!expired&&!potential;rep++){
  const auto& base=representatives[rep];cells.push_back(Cell{rep,length});auto& cell=cells.back();
  auto visit=[&](){
   M a=base;
   for(int t=0;t<length;t++){int row=path[t],next=path[(t+1)%length];a[row]^=uint16_t((1<<row)|(1<<next));}
   if(!legal(a,4))throw std::runtime_error("illegal cycle candidate");
   M b{};for(int i=0;i<n;i++)b[i]=all^a[i];
   if(!legal(b,9))throw std::runtime_error("illegal complement");
   uint64_t p=per(a),q=per(b);total++;cell.count++;
   if(cell.count==1){if(p!=ryser(a)||q!=ryser(b))throw std::runtime_error("independent control failed");controls+=2;}
   if(p<cell.best4)cell.best4=p;if(q<cell.best9)cell.best9=q;
   if(p<best4){best4=p;matrix4=a;}
   if(q<best9){best9=q;matrix9=b;}
   if(p<3852||q<64803969){potential=true;save();std::cout<<"POTENTIAL strict binary witness p="<<p<<" q="<<q<<std::endl;}
   if((total&1023)==0&&elapsed()>=seconds)expired=true;
  };
  auto dfs=[&](auto&& self,int first,int current,int used)->void{
   if(expired||potential)return;
   if(int(path.size())==length){if(!(base[current]&(1<<first)))visit();return;}
   int options=(all^base[current])&~used;
   options&=all^((1<<(first+1))-1);
   while(options&&!expired&&!potential){int bit=options&-options;options-=bit;int next=__builtin_ctz(unsigned(bit));path.push_back(next);self(self,first,next,used|bit);path.pop_back();}
  };
  for(int first=0;first<n&&!expired&&!potential;first++){path={first};dfs(dfs,first,first,1<<first);}
  cell.complete=!expired&&!potential;save();
  std::cout<<"rep "<<rep<<" length "<<length<<" count "<<cell.count<<" complete "<<cell.complete<<" seconds "<<elapsed()<<" best4 "<<best4<<" best9 "<<best9<<std::endl;
 }
 save();std::cout<<"FINISHED count "<<total<<" controls "<<controls<<" seconds "<<elapsed()<<" potential "<<potential<<std::endl;
}
