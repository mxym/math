#include <algorithm>
#include <array>
#include <bit>
#include <cstdlib>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;
using I=pair<int,int>;
// Powers zero, +/-1 of (3+4i)/5 and (5+12i)/13, scaled by 65.
I units[3][3][4];
int main(){
 for(int e=-1;e<=1;e++)for(int f=-1;f<=1;f++){
  int a=e?3:5,b=4*e,c=f?5:13,d=12*f;int x=a*c-b*d,y=a*d+b*c;
  for(int k=0;k<4;k++){units[e+1][f+1][k]={x,y};int z=x;x=-y;y=z;}
 }
 vector<vector<int>> reps={{0,1,2,4,8},{0,1,2,3,4,8},{0,1,2,4,8,15},{0,1,2,3,4,5,8},{0,1,2,3,4,8,12},{0,1,2,3,4,5,6,8},{0,1,2,3,4,5,8,9},{0,1,2,3,4,5,8,10}};
 for(int row=0;row<8;row++){
  auto S=reps[row];int h=S.size(),H=h*65;
  vector<I> edge[16];for(int i=0;i<h;i++)for(int j=i+1;j<h;j++)edge[S[i]^S[j]].push_back({i,j});
  int cmp[8];iota(cmp,cmp+8,0);for(int a=1;a<16;a++)if(edge[a].size()==1){auto [i,j]=edge[a][0];int c=cmp[j];for(int k=0;k<h;k++)if(cmp[k]==c)cmp[k]=cmp[i];}
  vector<int> names(cmp,cmp+h);sort(names.begin(),names.end());names.erase(unique(names.begin(),names.end()),names.end());
  vector<int> others;for(int j=0;j<h;j++)if(S[j]!=0 && (S[j]&(S[j]-1)))others.push_back(j);
  vector<array<int,8>> pats;for(int sign:{-1,1})for(int k=0;k<(1<<(names.size()-1));k++){
   if(k==0 && sign==1)continue;
   array<int,8> p{};int b=0;for(int c:names)if(c!=cmp[0]){if(k>>b&1)for(int j=0;j<h;j++)if(cmp[j]==c)p[j]=sign;b++;}pats.push_back(p);
  }
  vector<int> shifts(15);iota(shifts.begin(),shifts.end(),1);sort(shifts.begin(),shifts.end(),[&](int a,int b){return edge[a].size()<edge[b].size();});
  bool ok[1101]{};for(int hh=h;hh<=16;hh++)for(int t=-hh;t<=hh;t+=2)if((H*t)%hh==0)ok[abs(H*t/hh)]=true;
  long long count=0,pass=0; int u[8]{};for(auto e:pats)for(auto f:pats)for(int v=0;v<(1<<(2*others.size()));v++){
   count++;for(int k=0;k<int(others.size());k++)u[others[k]]=v>>(2*k)&3;
   bool valid=true;
   for(int a:shifts){if(!edge[a].size())continue;int re[4],im[4],xs[4];int n=0;
    for(auto [i,j]:edge[a]){auto [x,y]=units[e[j]-e[i]+1][f[j]-f[i]+1][(u[j]-u[i]+4)&3];re[n]=x;im[n]=y;xs[n++]=S[i];}
    for(int b=0;b<16;b++){int k=0;bool imag=popcount(unsigned(a&b))%2;for(int j=0;j<n;j++){int val=imag?im[j]:re[j];k+=((popcount(unsigned(xs[j]&b))%2)?-val:val);}int val=2*k;
     if(!ok[abs(val)]||abs(val)==H){valid=false;break;}
    }if(!valid)break;
   }
   if(!valid)continue;
   // These are only amplitudes, not a claim of admitting an actual cover.
   cout<<row<<' ';for(int i=0;i<h;i++)cout<<(e[i]+1)*12+(f[i]+1)*4+u[i]<<' ';cout<<'\n';pass++;
  }
  const long long pre[]={1,4,4,16,144,64,4161600,61504}, post[]={1,4,4,16,16,64,56,64};
  if(count!=pre[row] || pass!=post[row])return 1;
  cerr<<row<<" candidates="<<count<<" survive="<<pass<<"\n";
 }
}
