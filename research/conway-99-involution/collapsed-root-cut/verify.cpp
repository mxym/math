#include <array>
#include <algorithm>
#include <bitset>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>
#include <vector>
using namespace std;
using U=uint32_t;
int rank2(vector<U> mat){
  array<U,21> echelon{}; int r=0;
  for(U w:mat)while(w){
    int p=31-__builtin_clz(w);
    if(echelon[p])w^=echelon[p]; else {++r;echelon[p]=w;break;}
  }
  return r;
}
int main(){
  array<U,21> edge{},D{}; int m=0;
  for(int i=0;i<7;++i)for(int j=i+1;j<7;++j)edge[m++]=(1u<<i)|(1u<<j);
  assert(m==21);
  const U all=(1u<<m)-1;
  for(int j=0;j<m;++j)for(int i=0;i<m;++i)
    if(!(edge[i]&edge[j]))D[i]|=1u<<j;
  map<array<int,7>,array<int,4>> report;
  auto signature=[](array<int,7>x){sort(x.begin(),x.end());return x;};
  for(U A=0;A<=all;++A){
    array<int,7> d{}; U q=A;
    for(;q;q&=q-1){U e=edge[__builtin_ctz(q)];++d[__builtin_ctz(e)];++d[31-__builtin_clz(e)];}
    if(any_of(d.begin(),d.end(),[](int x){return x==1||x>3;}))continue;
    auto &row=report[signature(d)]; ++row[0];
    bool ruled=false; U C=all^A;
    while(C && !ruled){
      U component=C&-C, pending=component; C^=component;
      while(pending){
        int i=__builtin_ctz(pending);pending&=pending-1;
        U hit=C&D[i];C^=hit;component|=hit;pending|=hit;
      }
      vector<U> matrix;U reps=0;
      for(U left=component;left;left&=left-1){
        int i=__builtin_ctz(left);U row=D[i]&component;
        if(find(matrix.begin(),matrix.end(),row)==matrix.end())reps|=1u<<i;
        matrix.push_back(row);
      }
      if(rank2(matrix)<=8)continue;
      for(U cp=reps;cp&&!ruled;cp&=cp-1){
        int i=__builtin_ctz(cp);
        for(U n=D[i]&reps;n&&!ruled;n&=n-1){
          int j=__builtin_ctz(n);
          for(U krest=n&(n-1)&~D[j];krest&&!ruled;krest&=krest-1){
            int k=__builtin_ctz(krest);ruled=(krest&(krest-1)&~D[k])!=0;
          }
        }
      }
    }
    if(ruled)++row[1];
    else {
      ++row[2];
      // A 3-cycle on three vertices of degree 2 is forbidden by vector alternation.
      U mask=0;for(int v=0;v<7;v++)if(d[v]==2)mask|=1u<<v;
      if(__builtin_popcount(mask)==3){
        int ct=0;for(U left=A;left;left&=left-1)ct+=(edge[__builtin_ctz(left)]&mask)==edge[__builtin_ctz(left)];
        if(ct==3)++row[3];
      }
    }
  }
  array<int,4> total{};
  for(auto [d,t]:report){
    for(int j=0;j<4;++j)total[j]+=t[j];
    for(int x:d)cout<<x;
    for(int x:t)cout<<" "<<x;
    cout<<"\n";
  }
  if(total!=array<int,4>{50208,50173,35,35}) {
    cerr<<"unexpected totals";for(int n:total)cerr<<' '<<n;cerr<<'\n';return 1;
  }
  cout<<"PASS "<<total[0]<<" "<<total[1]<<" "<<total[2]<<" "<<total[3]<<"\n";
}
