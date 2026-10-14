// Exact finite-input controls for a whole-size identity, not a Minc-sixth proof.
#include <algorithm>
#include <cstdint>
#include <functional>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
using U=unsigned __int128; using S=__int128;
std::string dec(U x){if(!x)return "0";std::string z;while(x){z.push_back('0'+x%10);x/=10;}std::reverse(z.begin(),z.end());return z;}
std::string sign_dec(S x){return x<0?"-"+dec(U(-x)):dec(U(x));}
U powu(U x,int n){U r=1;while(n--)r*=x;return r;}
using Mat=std::vector<std::vector<int>>;
std::uint64_t permanent_dp(const Mat&a){int n=a.size(),N=1<<n;std::vector<std::uint64_t>d(N);d[0]=1;for(int mask=0;mask<N-1;++mask){int i=__builtin_popcount((unsigned)mask);for(int j=0;j<n;++j)if(!(mask>>j&1)&&a[i][j])d[mask|(1<<j)]+=d[mask]*a[i][j];}return d.back();}
std::uint64_t permanent_ryser(const Mat&a){int n=a.size(),N=1<<n;S result=0;for(int mask=1;mask<N;++mask){U product=1;for(int i=0;i<n;++i){int s=0;for(int j=0;j<n;++j)if(mask>>j&1)s+=a[i][j];product*=s;}if((n-__builtin_popcount((unsigned)mask))&1)result-=S(product);else result+=S(product);}if(result<0)throw std::runtime_error("negative Ryser");return std::uint64_t(result);}
struct Table{int n,N;std::vector<std::uint64_t>A,C;std::vector<std::vector<int>>masks;
 Table(const Mat&a):n(a.size()),N(1<<n),A(std::size_t(N)*N),C(std::size_t(N)*N),masks(n+1){
  if(n>12)throw std::runtime_error("finite exact bound n<=12");
  for(int m=0;m<N;++m)masks[__builtin_popcount((unsigned)m)].push_back(m);
  A[0]=C[0]=1;
  for(int I=1;I<N;++I){int i=__builtin_ctz((unsigned)I),prev=I^(1<<i),s=__builtin_popcount((unsigned)I);for(int J:masks[s]){std::uint64_t aa=0,cc=0;for(int bits=J;bits;bits&=bits-1){int j=__builtin_ctz((unsigned)bits);std::size_t pos=std::size_t(prev)*N+(J^(1<<j));aa+=a[i][j]*A[pos];cc+=(1-a[i][j])*C[pos];}A[std::size_t(I)*N+J]=aa;C[std::size_t(I)*N+J]=cc;}}
 }
 U sum()const{U result=0;int full=N-1;for(int I=0;I<N;++I)for(int J:masks[__builtin_popcount((unsigned)I)]){std::size_t pos=std::size_t(I)*N+J,other=std::size_t(full^I)*N+(full^J);result+=U(A[pos])*C[pos]*C[other];}return result;}
};
U enumerate_extensions(const Mat&a,std::uint64_t&count){int n=a.size();Mat b=a;U result=0;std::function<void(int,int)>walk=[&](int i,int used){if(i==n){++count;auto p=permanent_dp(b);if(p!=permanent_ryser(b))throw std::runtime_error("extension DP/Ryser disagreement");result+=p;return;}for(int j=0;j<n;++j)if(!(used>>j&1)&&!a[i][j]){b[i][j]=1;walk(i+1,used|(1<<j));b[i][j]=0;}};walk(0,0);return result;}
Mat cyclic(int n,int k){Mat a(n,std::vector<int>(n));for(int i=0;i<n;++i)for(int d=0;d<k;++d)a[i][(i+d)%n]=1;return a;}
void margins(const Mat&a,int k){int n=a.size();for(int i=0;i<n;++i){int r=0,c=0;for(int j=0;j<n;++j){if(a[i][j]!=0&&a[i][j]!=1)throw std::runtime_error("not binary");r+=a[i][j];c+=a[j][i];}if(r!=k||c!=k)throw std::runtime_error("bad actual margins");}}
int main(){try{
 std::vector<std::pair<int,int>>cases;for(int n=2;n<=10;++n)for(int k=1;k<n;++k)cases.push_back({n,k});for(int k:{2,3,5,8,10})cases.push_back({11,k});for(int k:{2,3,4,6,9,11})cases.push_back({12,k});
 std::cout<<"{\n\"scope\":\"Finite exact actual-matrix controls for the all-size complement-matching average identity only; a reverse average rejects a stronger proof route, not the Minc sixth global-minimum conjecture.\",\n\"cases\":[\n";
 int emitted=0,positive=0,enumerations=0;std::uint64_t total_enum=0;
 for(auto [n,k]:cases){Mat a=cyclic(n,k),c=a;for(auto&r:c)for(int&v:r)v=1-v;margins(a,k);margins(c,n-k);Table table(a);auto pa=table.A.back(),pc=table.C.back();if(pa!=permanent_dp(a)||pa!=permanent_ryser(a)||pc!=permanent_dp(c)||pc!=permanent_ryser(c)||pc==0)throw std::runtime_error("full permanent control");U total=table.sum();std::uint64_t count=0;bool enumcheck=false;if(n<=7){U direct=enumerate_extensions(a,count);if(direct!=total||count!=pc)throw std::runtime_error("average identity mismatch");enumcheck=true;++enumerations;total_enum+=count;}S gap=S(total*powu(k,n))-S(U(pc)*pa*powu(k+1,n));if(gap>0)++positive;
 if(emitted++)std::cout<<",\n";std::cout<<"{\"n\":"<<n<<",\"k\":"<<k<<",\"matrix\":[";for(int i=0;i<n;++i){if(i)std::cout<<",";std::cout<<"[";for(int j=0;j<n;++j){if(j)std::cout<<",";std::cout<<a[i][j];}std::cout<<"]";}std::cout<<"],\"per_A_dp_and_ryser\":\""<<pa<<"\",\"per_complement_dp_and_ryser\":\""<<pc<<"\",\"sum_extension_permanents_exact_minor_identity\":\""<<dec(total)<<"\",\"average_comparison_integer\":\""<<sign_dec(gap)<<"\",\"positive_rejects_all_A_average_bound_only\":"<<(gap>0?"true":"false")<<",\"direct_complement_enumeration_checked\":"<<(enumcheck?"true":"false")<<",\"complement_matchings_directly_enumerated\":"<<count<<"}";std::cout.flush();
 }
 Mat old=cyclic(9,2),extension=cyclic(9,3);auto pa=permanent_dp(old),pb=permanent_dp(extension);if(pa!=2||pb!=78||pa!=permanent_ryser(old)||pb!=permanent_ryser(extension))throw std::runtime_error("published control mismatch");S reverse=S(U(pb)*powu(2,9))-S(U(pa)*powu(3,9));
 std::cout<<"\n],\n\"case_count\":"<<emitted<<",\"strict_reverse_average_cases\":"<<positive<<",\"direct_enumeration_cases\":"<<enumerations<<",\"total_complement_matchings_directly_enumerated\":"<<total_enum<<",\n\"published2007_every_extension_obstruction\":{\"n\":9,\"k\":2,\"per_A\":2,\"per_B\":78,\"strict_normalized_reverse_integer\":\""<<sign_dec(reverse)<<"\",\"credited_existing_result\":true,\"not_a_global_minimum_counterexample\":true},\n\"full_conjecture_solved\":false\n}\n";
 }catch(const std::exception&e){std::cerr<<e.what()<<"\n";return 1;}}
