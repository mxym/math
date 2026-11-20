#include "plane.hpp"
int main(){
 init();set<vec>E;auto base=anchor;sort(base.begin(),base.end());E.insert(base);
 for(int n=7;n<=12;n++){set<vec>H;long long raw=0;for(const auto&A:E){array<bool,N>f{};
  for(int i=0;i<A.size();i++)for(int j=0;j<i;j++)for(int k=0;k<j;k++)for(int a=0;a<4;a++)for(int b=0;b<4;b++)for(int c=0;c<4;c++)f[pj[M[a][A[i]]^M[b][A[j]]^M[c][A[k]]]]=true;
  for(int k=0;k<num;k++)if(!f[V[k]]){auto X=A;X.push_back(V[k]);H.insert(canon(X));raw++;}}
  ofstream out("pg4_"+to_string(n)+".txt");for(auto&v:H){for(int j:v)out<<j<<" ";out<<endl;}cerr<<n<<" raw "<<raw<<" inequivalent "<<H.size()<<" canops "<<ops<<endl;E=move(H);
 }
}
