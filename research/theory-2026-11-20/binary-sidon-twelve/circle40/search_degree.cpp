#ifdef NDEBUG
#error need assertions
#endif
#include<bits/stdc++.h>
using namespace std;using U=uint64_t;
constexpr int N=1024, W=16;struct Set{array<U,W>a{};void add(int x){a[x>>6]|=U(1)<<(x%64);}void del(int x){a[x>>6]&=~(U(1)<<(x%64));}bool has(int x)const{return a[x>>6]>>(x%64)&1;}int count()const{int z=0;for(U w:a)z+=__builtin_popcountll(w);return z;}int first()const{for(int j=0;j<W;j++)if(a[j])return j*64+__builtin_ctzll(a[j]);return -1;}};
Set sw(const Set&A,const Set&B){Set C;for(int j=0;j<W;j++)C.a[j]=A.a[j]&B.a[j];return C;}
vector<int>C,T,raw;bool forb[N];int pos[N],v[N],nv,k,t,jtar;Set A[N],avoid[N],forFw,Nb[N];int cho[40];long long nodes,done,lab;
vector<int>ww;set<vector<int>>normB;int pivot,normal,srcbit;
void record(){vector<int>bb;for(int i=0;i<k;i++)bb.push_back(v[cho[i]]);for(int x:ww)bb.push_back(1024+x);
vector<int>Y;for(int y:bb){int z=y&1023;int lift=(z&((1<<pivot)-1))|((z>>pivot)<<(pivot+1));if(__builtin_parity(lift&normal)^(y>>10)^srcbit)lift|=1<<pivot;Y.push_back(lift);}
vector<int>full=raw;for(int z:Y)full.push_back(z+2048);bool D[4096]={};for(int i=0;i<full.size();i++)for(int j=0;j<i;j++){int h=full[i]^full[j];assert(h&&!D[h]);D[h]=true;}
vector<int>best;for(int z:Y){auto q=Y;for(int&x:q)x^=z;sort(q.begin(),q.end());if(best.empty()||q<best)best=q;}normB.insert(best);}

bool candw(vector<int>V,Set d,int tar){if(ww.size()==tar){record();return false;}while(ww.size()+V.size()>=tar){int x=V.back();V.pop_back();Set n=d;bool ok=true;for(int z:ww){if(d.has(x^z)){ok=false;break;}n.add(x^z);}if(!ok)continue;vector<int>q;for(int y:V){if(n.has(x^y))continue;ok=true;for(int z:ww)if(n.has(y^z)){ok=false;break;}if(ok)q.push_back(y);}ww.push_back(x);if(candw(q,n,tar))return true;ww.pop_back();}return false;}
bool eliminate(const Set&H,int need){
 Set rem=H;int c=0;while(c<need&&rem.first()>=0){c++;Set t=rem;for(int x=t.first();x>=0;x=t.first()){t.del(x);rem.del(x);for(int j=0;j<W;j++)t.a[j]&=~Nb[x].a[j];}}
 return c<need;
}
bool go(Set p,int n,Set H){
 assert(nodes<LLONG_MAX);nodes++;int h=H.count();if(h<t)return false;if(n==k){assert(done<LLONG_MAX);done++;Set F=forFw;for(int i=0;i<k;i++)for(int j=0;j<i;j++)F.add(v[cho[i]]^v[cho[j]]);
 vector<int>Q;for(int x=H.first();x>=0;x=H.first()){Q.push_back(x);H.del(x);}ww.clear();candw(Q,F,t);return false;}
 if(n>=6&&h<=2*t+2&&eliminate(H,t))return false;
 int l=k-n;if(p.count()<l)return false;int z=0,c=0,ls[1024],cs[1024];Set av=p;
 while(av.first()>=0){c++;Set q=av;for(int x=q.first();x>=0;x=q.first()){ls[z]=x;cs[z++]=c;q.del(x);av.del(x);for(int j=0;j<W;j++)q.a[j]&=~A[x].a[j];}}
 while(z--){if(cs[z]<l)return false;int x=ls[z];p.del(x);Set q=sw(A[x],p);for(int i=0;i<n;i++)for(int j=0;j<i;j++){int id=pos[v[x]^v[cho[i]]^v[cho[j]]];if(id>=0)q.del(id);}cho[n]=x;if(go(q,n+1,sw(H,avoid[v[x]])))return true;}return false;
}
int main(int ac,char**av){assert(ac==2);jtar=atoi(av[1]);int x;while(cin>>x)raw.push_back(x);assert(cin.eof()&&jtar==26&&raw.size()==40);int h=0,b=0,M=0;for(int z=1;z<2048;z++){int w=0;for(int a:raw)w+=__builtin_parity(z&a)?-1:1;if(abs(w)>M){M=abs(w);h=z;b=w<0;}}
 int j=__builtin_ctz(h);pivot=j;normal=h;srcbit=b;for(int a:raw){int z=(a&((1<<j)-1))|((a>>(j+1))<<j);(__builtin_parity(a&h)==b?C:T).push_back(z);}cerr<<"split "<<C.size()<<" "<<T.size()<<" direction "<<h<<" opposite "<<jtar<<endl;
 for(auto &a:{C,T})for(int x:a)for(int y:a)forb[x^y]=true;for(int i=0;i<N;i++)if(forb[i])forFw.add(i);
 set<int>cross;for(int x:C)for(int y:T)cross.insert(x^y);assert(cross.size()==C.size()*T.size());for(int x=0;x<N;x++)for(int y=0;y<N;y++){if(!cross.count(x^y))avoid[x].add(y);if(!forb[x^y])Nb[x].add(y);}
 vector<pair<int,int>>ps;for(int i=1;i<N;i++)if(!forb[i]){int d=0;for(int y=1;y<N;y++)if(!forb[y]&&!forb[i^y])d++;ps.emplace_back(-d,i);}sort(ps.begin(),ps.end());fill(begin(pos),end(pos),-1);v[0]=0;pos[0]=0;nv=1;for(auto [g,x]:ps){pos[x]=nv;v[nv++]=x;}
 for(k=(jtar+1)/2;k<=jtar;k++){t=jtar-k;nodes=done=0;for(int i=0;i<nv;i++){A[i]={};for(int j=1;j<nv;j++)if(!forb[v[i]^v[j]])A[i].add(j);}
 for(int d=1;d<nv;d++){Set p=A[d];for(int x=1;x<=d;x++)p.del(x);cho[0]=0;cho[1]=d;if(go(p,2,sw(avoid[0],avoid[v[d]])))return 0;
  for(int i=d+1;i<nv;i++){int j=pos[v[i]^v[d]];if(j>d)A[i].del(j);}}
 cout<<"k "<<k<<" t "<<t<<" nodes "<<nodes<<" completeV "<<done<<" stored "<<normB.size()<<endl;}for(auto&S:normB){cout<<"B";for(int x:S)cout<<" "<<x;cout<<endl;}cout<<"TOTAL "<<normB.size()<<endl;
}
