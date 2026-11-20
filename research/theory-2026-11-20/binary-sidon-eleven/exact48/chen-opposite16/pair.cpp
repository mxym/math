#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <string>
#include <sstream>
#include <iostream>
#include <cassert>
#include <cstdint>
#include <climits>
using namespace std;using W=uint64_t;
constexpr int B=16,D=2048;
struct Bits{W w[B]={};
 void add(int i){w[i/64]|=W(1)<<(i%64);}void rem(int i){w[i/64]&=~(W(1)<<(i%64));}
 int first(int s=0)const{for(int i=s/64;i<B;i++)if(w[i])return i*64+__builtin_ctzll(w[i]);return -1;}
 int size()const{int c=0;for(auto a:w)c+=__builtin_popcountll(a);return c;}
};
int id[D],v[D],pri[D],n,need,sel[64]; bool forbid[D];Bits adj[D]; long long nodes=0;
bool solve(Bits P,int k){
 assert(nodes<LLONG_MAX);nodes++;if(k==need){vector<int>X,Y;for(int i=0;i<k;i++){X.push_back(v[sel[i]]);Y.push_back(v[sel[i]]^v[sel[1]]);}sort(X.begin(),X.end());sort(Y.begin(),Y.end());if(X==Y)abort();if(X<Y){for(int x:X)cout<<x<<" ";cout<<"\n";}return false;}
 int t=need-k;if(P.size()<t)return false;
 int ls[B*64],cs[B*64],z=0,c=0;
 Bits avail=P;while(avail.first()>=0){c++;Bits Q=avail;
  for(int x=Q.first();x>=0;x=Q.first(x)){ls[z]=x;cs[z++]=c;avail.rem(x);Q.rem(x);for(int j=x/64;j<B;j++)Q.w[j]&=~adj[x].w[j];}
 }
 while(z){--z;if(cs[z]<t)return false;int x=ls[z];P.rem(x);Bits Q;
  for(int j=0;j<B;j++)Q.w[j]=P.w[j]&adj[x].w[j];
  for(int i=0;i<k;i++)for(int j=0;j<i;j++){int d=id[v[x]^v[sel[i]]^v[sel[j]]];if(d>=0)Q.rem(d);}
  sel[k]=x;if(solve(Q,k+1))return true;
 }
 return false;
}
bool run(const vector<int>&a){
 fill(begin(forbid),end(forbid),false);fill(begin(id),end(id),-1);fill(begin(pri),end(pri),-1);for(int x:a)for(int y:a)forbid[x^y]=true;vector<pair<int,int>> V;
 for(int x=1;x<D;x++)if(!forbid[x]){int d=0;for(int y=1;y<D;y++)if(!forbid[y]&&!forbid[x^y])d++;V.emplace_back(-d,x);}
 sort(V.begin(),V.end());n=1;v[0]=0;id[0]=0;for(auto [dg,x]:V){pri[x]=n;id[x]=n;v[n++]=x;}assert(n<=64*B);
 for(int i=0;i<n;i++){adj[i]={};for(int j=1;j<n;j++)if(!forbid[v[i]^v[j]])adj[i].add(j);}
 for(int d=1;d<n;d++){
  Bits P=adj[d];for(int j=1;j<=d;j++)P.rem(j);
  if(P.size()>=need-2){sel[0]=0;sel[1]=d;if(solve(P,2))return true;}
  for(int i=d+1;i<n;i++){int j=id[v[i]^v[d]];if(j>d)adj[i].rem(j);}
 }
 return false;
}
int main(int ac,char**av){need=atoi(av[1]);string l;while(getline(cin,l)){istringstream in(l);vector<int>a;int x;while(in>>x)a.push_back(x);nodes=0;bool q=run(a);cout<<"hit "<<q<<" nodes "<<nodes<<endl;if(q)break;}}
