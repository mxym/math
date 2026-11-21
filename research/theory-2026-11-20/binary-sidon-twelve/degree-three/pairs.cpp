#ifdef NDEBUG
#error No NDEBUG
#endif
#include<algorithm>
#include<array>
#include<iostream>
#include<cassert>
#include<vector>
#include<set>
using namespace std;
int F[64][64],iv[64];
int m(int x,int y){int z=0;while(y){if(y&1)z^=x;y>>=1;x<<=1;if(x&64)x^=67;}return z;}
int main(int ac,char**av){assert(ac==2);int target=atoi(av[1]);assert(target>=64&&target<=67);for(int x=0;x<64;x++)for(int y=0;y<64;y++){F[x][y]=m(x,y);if(F[x][y]==1)iv[x]=y;}
int n,j=0;while(cin>>n){assert(n>=64&&n<=81);vector<array<int,3>> C(n);for(auto&a:C)for(int&v:a){assert(cin>>v);assert(0<=v&&v<64);}int survive=0,hits=0,charts=0,mx=-200000;
for(int i=0;i<3;i++)for(int a=0;a<(i==2?1:64);a++)for(int b=0;b<(i==0?64:1);b++){
int p[3]={},u=(i+1)%3,v=(i+2)%3;p[i]=1;if(i<2)p[i+1]=a;if(i==0)p[2]=b;int S[81],h=0;
for(auto t:C){int den=F[p[0]][t[0]]^F[p[1]][t[1]]^F[p[2]][t[2]];if(den)S[h++]=(F[t[u]][iv[den]]<<6)|F[t[v]][iv[den]];}
charts++;if(h<target)continue;hits++;
int cell[4096]={},deg[81]={};for(int k=1;k<h;k++)for(int l=0;l<k;l++)cell[S[k]^S[l]]++;assert(!cell[0]);
int sum=0;for(int k=1;k<h;k++)for(int l=0;l<k;l++){int d=cell[S[k]^S[l]]-1;deg[k]+=d;deg[l]+=d;sum+=d;}assert(sum%6==0);sort(deg,deg+h,greater<int>());int cost=0;for(int k=0;k<h-target;k++)cost+=deg[k];int slack=cost-sum/2;mx=max(mx,slack);if(slack>=0){survive++;cout<<"SURVIVE "<<j<<" "<<h<<" "<<p[0]<<" "<<p[1]<<" "<<p[2];for(int k=0;k<h;k++)cout<<" "<<S[k];cout<<endl;}
}assert(charts==4161);cout<<"MODEL "<<j<<" points "<<n<<" charts "<<charts<<" eligible "<<hits<<" survive "<<survive<<" max3slack "<<mx<<endl;j++;}assert(cin.eof());}
