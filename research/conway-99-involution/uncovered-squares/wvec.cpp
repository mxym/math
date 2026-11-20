#include <bits/stdc++.h>
using namespace std;using U=unsigned;int pc(U z){return __builtin_popcount(z);}
int main(){uint8_t tab[1<<18]={};int k,h;ifstream ker("ker.dat");while(ker>>k>>h)tab[k]=h;int n,i,j;while(cin>>n){int B[12][12]={};for(int z=0;z<22;z++){cin>>i>>j;B[i][j]=1;}
 vector<U>m(n);for(auto &v:m)cin>>v;vector<array<int,13>>cost(n);
 for(int p=0;p<12;p++)for(int r=p+1;r<12;r++)for(int q=0;q<12;q++)for(int s=q+1;s<12;s++){int v[6]={24,25,p,r,q+12,s+12};int y=(p<2?(1<<p):0)|(r<2?(1<<(2+r)):0)|(q<2?(1<<(4+q)):0)|(s<2?(1<<(6+s)):0);y|=B[p][q]<<8| B[p][s]<<9|B[r][q]<<10|B[r][s]<<11;
 bool nonzero=false;for(int c=0;c<64;c++)nonzero|=bool(tab[y+(c<<12)]);if(!nonzero)continue;
 for(int a=0;a<n;a++){U x=m[a];if(p>=2&&(!(x>>p&1)||!(x>>r&1)))continue;if(q>=2&&(!(x>>(q+12)&1)||!(x>>(s+12)&1)))continue;int b=0;for(int l=0;l<6;l++)b|=(x>>v[l]&1)<<l;int h=tab[y+(b<<12)];if(h)cost[a][h]++;}}
 for(auto &w:cost){for(int j=0;j<13;j++)cout<<w[j]<<" ";cout<<"\n";}cout.flush();
 }}
