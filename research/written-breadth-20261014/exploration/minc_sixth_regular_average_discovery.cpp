// Bounded exact actual-matrix discovery for a stronger route, no global certificate.
#define main preserved_cyclic_control_main
#include "minc_sixth_complement_average.cpp"
#undef main
#include <random>
#include <chrono>
Mat petersen_biadj(int b,int step){
 int V=2*b;std::vector<std::vector<int>>g(V);
 auto edge=[&](int u,int v){g[u].push_back(v);g[v].push_back(u);};
 for(int i=0;i<b;++i){edge(i,(i+1)%b);edge(i,b+i);edge(b+i,b+(i+step)%b);}
 std::vector<int>color(V,-1),todo={0};color[0]=0;
 for(std::size_t pos=0;pos<todo.size();++pos){int u=todo[pos];for(int v:g[u]){
  if(color[v]<0){color[v]=1-color[u];todo.push_back(v);}
  else if(color[v]==color[u])throw std::runtime_error("not bipartite");
 }}
 std::vector<int>left,right;for(int i=0;i<V;++i)(color[i]?right:left).push_back(i);
 if(left.size()!=std::size_t(b)||right.size()!=std::size_t(b))throw std::runtime_error("bad bipartition");
 Mat a(b,std::vector<int>(b));for(int i=0;i<b;++i)for(int j=0;j<b;++j)
  a[i][j]=std::find(g[left[i]].begin(),g[left[i]].end(),right[j])!=g[left[i]].end();
 margins(a,3);return a;
}
Mat lcf(){
 int n=18;int shifts[6]={5,7,-7,7,-7,-5};Mat a(9,std::vector<int>(9));
 for(int i=0;i<n;++i){int candidates[3]={(i+1)%n,(i+n-1)%n,(i+shifts[i%6]+n)%n};
  for(int j:candidates){if((i^j)%2!=1)throw std::runtime_error("LCF parity");
   int u=(i%2)?j:i,v=(i%2)?i:j;a[u/2][v/2]=1;
  }}
 margins(a,3);return a;
}
Mat fano(){Mat a(7,std::vector<int>(7));for(int u=1;u<8;++u)for(int v=1;v<8;++v)
 a[u-1][v-1]=!(__builtin_popcount((unsigned)(u&v))&1);margins(a,3);return a;}
int main(){try{
 auto begin=std::chrono::steady_clock::now();std::mt19937_64 rng(20261014);
 std::vector<Mat>inputs={fano(),petersen_biadj(8,3),lcf(),petersen_biadj(10,3)};
 for(int n:{8,9,10,11,12})for(int k:{3,4,n/2,n-3}){
  if(k<1||k>=n)continue;
  for(int seed=0;seed<6;++seed){Mat a=cyclic(n,k);auto current=permanent_dp(a);
   for(int z=0;z<2400;++z){int r=rng()%n,s=rng()%n,c=rng()%n,d=rng()%n;
    if(r==s||c==d||!a[r][c]||!a[s][d]||a[r][d]||a[s][c])continue;
    a[r][c]=a[s][d]=0;a[r][d]=a[s][c]=1;auto trial=permanent_dp(a);
    if(trial<=current)current=trial;
    else{a[r][c]=a[s][d]=1;a[r][d]=a[s][c]=0;}
   }margins(a,k);inputs.push_back(a);
  }
 }
 std::cout<<"{\n\"scope\":\"Bounded exact actual regular-matrix discovery for complement-average sufficient route only; no global-minimum certificate or complete Minc result.\",\n\"seed\":20261014,\n\"cases\":[\n";
 int count=0,positive=0;std::uint64_t best3[13]={};
 for(const auto&a:inputs){int n=a.size(),k=0;for(int v:a[0])k+=v;
  Mat c=a;for(auto&row:c)for(int&v:row)v=1-v;Table table(a);
  auto pa=table.A.back(),pc=table.C.back();
  if(pa!=permanent_dp(a)||pa!=permanent_ryser(a)||pc!=permanent_dp(c)||pc!=permanent_ryser(c))
   throw std::runtime_error("independent permanent control");
  U total=table.sum();S gap=S(total*powu(k,n))-S(U(pc)*pa*powu(k+1,n));
  if(gap>0)++positive;if(k==3&&(!best3[n]||pa<best3[n]))best3[n]=pa;
  if(count++)std::cout<<",\n";
  std::cout<<"{\"n\":"<<n<<",\"k\":"<<k<<",\"per_A_dp_and_ryser\":\""<<pa
   <<"\",\"per_C_dp_and_ryser\":\""<<pc
   <<"\",\"sum_actual_extension_permanents\":\""<<dec(total)
   <<"\",\"average_comparison_integer\":\""<<sign_dec(gap)
   <<"\",\"reverse_average_only\":"<<(gap>0?"true":"false")<<",\"matrix\":[";
  for(int i=0;i<n;++i){if(i)std::cout<<",";std::cout<<"[";
   for(int j=0;j<n;++j){if(j)std::cout<<",";std::cout<<a[i][j];}std::cout<<"]";}
  std::cout<<"]}";std::cout.flush();
 }
 std::cout<<"\n],\n\"case_count\":"<<count<<",\"reverse_average_count\":"<<positive
  <<",\"lowest_observed_degree3\":[";
 bool comma=false;for(int n=2;n<=12;++n)if(best3[n]){
  if(comma)std::cout<<",";comma=true;
  std::cout<<"{\"n\":"<<n<<",\"lowest_observed_permanent\":"<<best3[n]
   <<",\"global_minimum_proved_here\":false}";
 }
 std::cout<<"],\n\"runtime_seconds\":"
  <<std::chrono::duration<double>(std::chrono::steady_clock::now()-begin).count()
  <<",\n\"full_conjecture_solved\":false\n}\n";
 return 0;
 }catch(const std::exception&e){std::cerr<<e.what()<<"\n";return 1;}
}
