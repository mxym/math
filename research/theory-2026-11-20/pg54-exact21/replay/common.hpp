#pragma once
#include <bits/stdc++.h>
namespace Q{
using namespace std;using vi=vector<int>;const int mm[4][4]={{0,0,0,0},{0,1,2,3},{0,2,3,1},{0,3,1,2}};int mult[4][4096],normal[4096],id[4096],bar[4096],dim;vi pts;
void init(){for(int x=0;x<4096;x++){for(int i=0;i<6;i++){int k=x>>(2*i)&3;for(int s=1;s<=3;s++)mult[s][x]|=mm[s][k]<<(2*i);bar[x]|=mm[k][k]<<(2*i);}}
 for(int x=1;x<4096;x++){int j=(31-__builtin_clz(x))/2;int k=x>>(2*j)&3;normal[x]=mult[mm[k][k]][x];if(normal[x]==x){id[x]=pts.size();pts.push_back(x);}else id[x]=id[normal[x]];}assert(pts.size()==1365);}
void validate(vi S){set<int>P,D;vi V;for(int x:S){for(int s=1;s<=3;s++){int a=mult[s][x];assert(P.insert(a).second);V.push_back(a);}}for(int i=0;i<(int)V.size();i++)for(int j=0;j<i;j++)assert(D.insert(V[i]^V[j]).second);}
const vi base{1,4,16,64,85,256};
vector<array<int,1024>> isos(vi A,vi B,bool justone=false){ // semilinear maps 5-space, including all 3 scalars. Known source contains base.
 set<int> sb;for(int x:B)sb.insert(normal[x]);vector<array<int,1024>> ok;
 for(int u0:B)for(int u1:B)if(u1!=u0)for(int u2:B)if(u2!=u0&&u2!=u1)for(int u3:B)if(u3!=u0&&u3!=u1&&u3!=u2)for(int a1=1;a1<=3;a1++)for(int a2=1;a2<=3;a2++)for(int a3=1;a3<=3;a3++){
 int vs[]{u0,mult[a1][u1],mult[a2][u2],mult[a3][u3],0};int fifth=normal[vs[0]^vs[1]^vs[2]^vs[3]];if(!sb.count(fifth))continue;
 bitset<1024> in;for(int z=0;z<256;z++){int v=0;for(int i=0;i<4;i++)v^=mult[(z>>(2*i))&3][vs[i]];in.set(v);}assert(in.count()==256);
 for(int y:B)if(!in[y])for(int b=1;b<4;b++)for(int ff=0;ff<2;ff++){vs[4]=mult[b][y];
 auto f=[&](int u){if(ff)u=bar[u];int v=0;for(int j=0;j<5;j++)v^=mult[(u>>(2*j))&3][vs[j]];return v;};
 bool yes=1;for(int x:A)if(!sb.count(normal[f(x)])){yes=0;break;}if(!yes)continue;
 for(int s=1;s<=3;s++){array<int,1024>T;for(int z=0;z<1024;z++)T[z]=mult[s][f(z)];ok.push_back(T);if(justone)return ok;}
 }}
 return ok;}
}
