#ifdef NDEBUG
#error "do not disable invariant checks"
#endif
#include <array>
#include <algorithm>
#include <vector>
#include <iostream>
#include <set>
#include <cassert>
#include <cstdint>
#include <climits>
using namespace std;
using Tile=array<uint64_t,16>;
int pop(Tile q){int n=0;for(auto w:q)n+=__builtin_popcountll(w);return n;}
int least(const Tile&q){for(int i=0;i<16;i++)if(q[i])return 64*i+__builtin_ctzll(q[i]);return -1;}
void put(Tile&q,int x){q[x/64]|=1ULL<<(x%64);}
void rem(Tile&q,int x){q[x/64]&=~(1ULL<<(x%64));}
Tile meet(Tile a,const Tile&b){for(int i=0;i<16;i++)a[i]&=b[i];return a;}
bool bad[1024],crosses[1024];int weight,target,cut,k,t,normal,side;Tile out[1024],graph[1024],g0[1024];vector<int>anchor,L,R;
set<vector<int>>found;long long leaves;
void record(){
 vector<int> y;
 for(int s:{0,1})for(int x:(s?R:L)){
 int bit=__builtin_ctz(normal);int w=(x%(1<<bit))|((x>>bit)<<(bit+1));w|=((__builtin_parity(normal&w)^s^side)<<bit);y.push_back(w);}
 assert(y.size()==target);vector<int> all=anchor;for(int x:y)all.push_back(x|2048);
 set<int> seen;for(int i=0;i<all.size();i++)for(int j=0;j<i;j++)assert(seen.insert(all[i]^all[j]).second);
 vector<int>b;for(int x:y){vector<int> a=y;for(int&v:a)v^=x;sort(a.begin(),a.end());if(b.empty()||a<b)b=a;}
 found.insert(b);assert(leaves<LLONG_MAX);leaves++;
}
void tail(vector<int>&pool,const array<bool,1024>&used){
 if(R.size()==t){record();return;}
 while(R.size()+pool.size()>=t){
 int x=pool.back();pool.pop_back();auto use=used;bool ok=true;
 for(int y:R){if(use[x^y]){ok=false;break;}use[x^y]=true;}if(!ok)continue;
 vector<int> pp;for(int y:pool){if(use[x^y])continue;bool good=true;for(int r:R)if(use[r^y]){good=false;break;}if(good)pp.push_back(y);}
 R.push_back(x);tail(pp,use);R.pop_back();}
}
int color(Tile pool,const Tile *g,int stop,int*order=nullptr,int*labels=nullptr){
 int c=0,j=0;while(least(pool)>=0&&c<stop){c++;Tile same=pool;while(true){int x=least(same);if(x<0)break;rem(pool,x);rem(same,x);if(order){order[j]=x;labels[j++]=c;}for(int i=0;i<16;i++)same[i]&=~g[x][i];}}return order?j:c;
}
void visit(Tile choices,Tile holes){
 int need=k-int(L.size());int hn=pop(holes);if(hn<t||pop(choices)<need)return;
 if(!need){
 vector<int>pp;for(int x=least(holes);x>=0;x=least(holes)){rem(holes,x);pp.push_back(x);}
 array<bool,1024> used;copy(begin(bad),end(bad),used.begin());for(int i=0;i<k;i++)for(int j=0;j<i;j++){assert(!used[L[i]^L[j]]);used[L[i]^L[j]]=true;}
 assert(R.empty());tail(pp,used);return;}
 if(hn<=2*t+4&&color(holes,g0,t)<t)return;
 int ord[1024],lev[1024];int n=color(choices,graph,1025,ord,lev);
 for(int i=n-1;i>=0;i--){if(lev[i]<need)return;int x=ord[i];rem(choices,x);Tile next=meet(choices,graph[x]);
 for(int a=0;a<L.size();a++)for(int b=0;b<a;b++)rem(next,L[a]^L[b]^x);
 L.push_back(x);visit(next,meet(holes,out[x]));L.pop_back();}
}
int main(int argc,char**argv){assert(argc==2);target=atoi(argv[1]);assert(target>=3&&target<=40);int x;while(cin>>x)anchor.push_back(x);assert(cin.eof()&&anchor.size()==40);
 // Deliberately use the LAST largest direction; the first solver takes the first.
 int hi=-1;for(int h=1;h<2048;h++){int s=0;for(int a:anchor)s+=__builtin_parity(a&h)?-1:1;if(abs(s)>=hi){normal=h;side=s<0;hi=abs(s);}}
 vector<int> a[2];int j=__builtin_ctz(normal);for(int x:anchor){int p=(x% (1<<j))|((x>>(j+1))<<j);a[side^__builtin_parity(x&normal)].push_back(p);}
 for(int s:{0,1})for(int x:a[s])for(int y:a[s])bad[x^y]=true;for(int x:a[0])for(int y:a[1]){assert(!crosses[x^y]);crosses[x^y]=true;}
 for(int x=0;x<1024;x++)for(int y=0;y<1024;y++){if(!bad[x^y])put(g0[x],y);if(!crosses[x^y])put(out[x],y);}
 cerr<<"alternative split "<<normal<<" "<<a[0].size()<<" "<<a[1].size()<<endl;
 // Increasing least numeric XOR d; graph uses raw numeric vertices. No catalogue cap on k.
 for(k=(target+1)/2;k<=target;k++){t=target-k;leaves=0;
 for(int d=1;d<1024;d++)if(!bad[d]){Tile cand{};for(int x=d+1;x<1024;x++)if(!bad[x]&&!bad[x^d]&&(x^d)>d)put(cand,x);
 if(pop(cand)<k-2)continue;
 // Restricted graph for differences numerically greater than d
 Tile tmp=cand;for(int x=least(tmp);x>=0;x=least(tmp)){rem(tmp,x);graph[x]=meet(cand,g0[x]);for(int z=0;z<=d;z++)rem(graph[x],x^z);}
 L={0,d};visit(cand,meet(out[0],out[d]));}
 cout<<"k "<<k<<" labelled "<<leaves<<" classes "<<found.size()<<endl;
 }for(auto y:found){cout<<"B";for(int x:y)cout<<' '<<x;cout<<endl;}cout<<"TOTAL "<<found.size()<<endl;
}
