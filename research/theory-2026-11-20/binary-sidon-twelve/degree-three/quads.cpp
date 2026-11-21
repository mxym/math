#ifdef NDEBUG
#error need assertions
#endif
#include<algorithm>
#include<vector>
#include<iostream>
#include<array>
#include<cassert>
#include<cstring>
using namespace std;
using P=array<int,3>;
int F[64][64],inv[64];
int main(){int exp[126],lg[64]={};int z=1;for(int i=0;i<63;i++){assert(i==0||z!=1);exp[i]=exp[63+i]=z;lg[z]=i;z<<=1;if(z&64)z^=67;}assert(z==1);for(int i=1;i<64;i++){inv[i]=exp[63-lg[i]];for(int j=1;j<64;j++)F[i][j]=exp[lg[i]+lg[j]];}
int n,model=0;while(cin>>n){assert(n>=66&&n<=81);vector<P> E(n);for(auto&a:E)for(auto&i:a){assert(cin>>i);assert(i>=0&&i<64);}
int count=0,eligible=0,margin=1000000;
for(int u=0;u<64;u++)for(int v=0;v<64;v++)for(int last=0;last<3;last++){if((last==0&&(u||v))||(last==1&&v))continue;
P L{0,0,0};L[last]=1;if(last>0)L[0]=u;if(last>1)L[1]=v;count++;
int n2=0,points[81],index[4096]={};int i1=(last+1)%3,i2=(last+2)%3;
for(auto&a:E){int d=F[L[0]][a[0]]^F[L[1]][a[1]]^F[L[2]][a[2]];if(!d)continue;int y=(F[a[i1]][inv[d]]<<6)|F[a[i2]][inv[d]];assert(index[y]==0);index[y]=++n2;points[n2-1]=y;}
if(n2<66)continue;eligible++;int degree[81]={},quads=0;
for(int i=0;i<n2;i++)for(int j=0;j<i;j++){int s=points[i]^points[j];for(int k=0;k<j;k++){int l=index[s^points[k]]-1;if(l<0||l>=k)continue;quads++;degree[i]++;degree[j]++;degree[k]++;degree[l]++;}}
sort(degree,degree+n2);int loss=0;for(int j=66;j<n2;j++)loss+=degree[j];
margin=min(margin,quads-loss);assert(quads>loss);
}assert(count==4161);cout<<model++<<" "<<eligible<<" "<<margin<<endl;
}assert(cin.eof());}
