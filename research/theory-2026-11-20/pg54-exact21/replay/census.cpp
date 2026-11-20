#include "common.hpp"
using namespace Q;vector<long long> mass(13);using bits=bitset<341>;int reps[341],sz;int sl[64];long long raw[13]{};
void rec(bits C,int k){
 raw[k]++;for(int j=C._Find_first();j<341;j=C._Find_next(j)){int x=reps[j];C.reset(j);bits n=C;for(int h=0;h<k;h++)for(int t=0;t<h;t++)for(int a=0;a<4;a++)for(int b=0;b<4;b++)n.reset(id[x^mult[a][sl[h]]^mult[b][sl[t]]]);sl[k]=x;rec(n,k+1);}}
int main(){init();for(int x:pts)if(x<1024)reps[sz++]=x;assert(sz==341);bits C;C.set();for(int i=0;i<6;i++)sl[i]=base[i];
 for(int i=0;i<6;i++)for(int j=0;j<i;j++)for(int k=0;k<j;k++)for(int a=0;a<4;a++)for(int b=0;b<4;b++)for(int c=0;c<4;c++){int x=mult[a][sl[i]]^mult[b][sl[j]]^mult[c][sl[k]];if(x)C.reset(id[x]);}
 rec(C,6);
 for(int n=7;n<=11;n++){
 ifstream fi("pg4_"+to_string(n)+".txt");string ln;vector<vi> prior;
 while(getline(fi,ln)){istringstream ss(ln);vi A;int x;while(ss>>x)A.push_back(x);assert(A.size()==n);validate(A);for(auto&B:prior)assert(isos(A,B,true).empty());prior.push_back(A);auto g=isos(A,A);int aut=g.size()/3;assert(aut*3==(int)g.size());
 int marks=0;for(int h=1;h<1024;h++)if(normal[h]==h){int c=0;for(int v:A){int z=0;for(int i=0;i<5;i++)z^=mm[(h>>(2*i))&3][(v>>(2*i))&3];c+=!z;}assert(c<=5);if(c==5)marks+=n-5;}
 assert((marks*720)%aut==0);mass[n]+=marks*720/aut;}
 assert(mass[n]==raw[n]);cout<<"mass "<<n<<" classes "<<prior.size()<<" labeled through frame "<<raw[n]<<endl;
 }assert(raw[12]==0);cout<<"PASS mass and non-equivalence"<<endl;}
