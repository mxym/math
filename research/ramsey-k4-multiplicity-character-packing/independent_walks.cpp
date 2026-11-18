// Independent weighted-map count from an equal-weight SK integer base and six-column triangle list.
// Standard invocation is through check_walks.py, which validates both input digests.
#include <iostream>
#include <fstream>
#include <cstdlib>
#include <gmpxx.h>
#include <vector>
#include <set>
#include <array>
#include <algorithm>
using namespace std;using Z=mpz_class;Z z128(__int128 x){bool neg=x<0;unsigned __int128 a=neg?-x:x;Z z((unsigned long)(a>>64));z<<=64;z+=(unsigned long)a;if(neg)z=-z;return z;}
const int N=3840,D=1<<20;
int main(int argc,char**argv){ if(argc!=3)return 2;
 ifstream mat(argv[1],ios::binary),f(argv[2]);vector<int>R(N*N);mat.read((char*)R.data(),R.size()*4);
 if(!mat||mat.peek()!=EOF)throw 1; int i,j,k,u,v,w; Z sum=0;int good=0,nb=0,ncol=0;set<pair<int,int>> covered;vector<unsigned> mask(N);
 while(f>>i>>j>>k>>u>>v>>w){
   if(!(0<=i&&i<j&&j<k&&k<N)) throw 2;
   int ee[3][3]={{0,u,v},{u,0,w},{v,w,0}}; int id[]={i,j,k};
   unsigned forbidden=mask[i]|mask[j]|mask[k]; int c=0;while(c<32 && ((forbidden>>c)&1))c++;if(c>=32)throw 3;ncol=max(ncol,c+1);
   for(int y:id)mask[y]|=1U<<c;
   for(int a=0;a<3;a++)for(int b=a+1;b<3;b++){
    int rr=R[id[a]*N+id[b]];if(!covered.emplace(id[a],id[b]).second||ee[a][b]==0||abs(ee[a][b])>min(rr,D-rr))throw 4;
   }
   __int128 H=0;for(int t=0;t<N;t++){
    long long A=R[N*t+i],B=R[N*t+j],C=R[N*t+k];
    H+=(__int128)A*B*C-(__int128)(D-A)*(D-B)*(D-C);
   }
   // For a fixed triangle of perturbed positions enumerate the 3! embeddings; the fourth position is free.
   Z delta=0;array<int,3>p={0,1,2};
   do{delta+=4*z128(H)*ee[p[0]][p[1]]*ee[p[1]][p[2]]*ee[p[2]][p[0]];}while(next_permutation(p.begin(),p.end()));
   // For a fixed labeled 4-cycle enumerate all its maps to {i,j,k}, including all collisions.
   for(int a=0;a<3;a++)for(int b=0;b<3;b++)for(int c=0;c<3;c++)for(int d=0;d<3;d++){
     long x=R[N*id[a]+id[c]],y=R[N*id[b]+id[d]];
     delta+=3*Z(ee[a][b])*ee[b][c]*ee[c][d]*ee[d][a]*(x*y+(D-x)*(D-y));
   }
   nb++;good+=(delta<0);sum+=delta;
 }
 cout<<nb<<" "<<good<<" "<<ncol<<" "<<covered.size()<<" "<<sum<<"\n";
}
