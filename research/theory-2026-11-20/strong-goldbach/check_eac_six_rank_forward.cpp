// Ascending input order; exact signed minors; no isomorphism or weight cut.
#include <cstdio>
#include <vector>
#include <algorithm>
#include <array>
#include <set>
#include <cstdint>
using namespace std;
struct E {array<int,3> fan{};array<int,6> exp{};int t;int mask;};
array<E,6> P; vector<E> G[6];
long long states[7][5]={};
set<array<int,7>> kept;
int det5(int q[6][6],int ei,int ej){long long v[5][5];int ii=0,jj;for(int i=0;i<6;++i)if(i!=ei){jj=0;for(int j=0;j<6;++j)if(j!=ej)v[ii][jj++]=q[i][j];ii++;}long long last=1,sign=1;for(int i=0;i<4;i++){if(!v[i][i]){int r=i+1;while(r<5&&!v[r][i])r++;if(r==5)return 0;for(int j=0;j<5;++j)swap(v[i][j],v[r][j]);sign=-sign;}for(int r=i+1;r<5;r++)for(int j=i+1;j<5;j++)v[r][j]=(v[r][j]*v[i][i]-v[r][i]*v[i][j])/last;last=v[i][i];}return sign*v[4][4];}
void examine(){
 int arc[6]={},rec=0,has=0;int triple=0;
 for(int i=0;i<6;i++){arc[i]=P[i].mask;has|=arc[i];triple+=P[i].t==3;for(int j=0;j<i;j++)rec+=P[i].exp[j]*P[j].exp[i];}
 if(has!=63)return; auto &counts=states[triple];
 counts[0]++;
 for(int j=0;j<6;j++)for(int i=0;i<6;i++)if(arc[i]&(1<<j))arc[i]|=arc[j];
 for(int i=0;i<6;i++)if(arc[i]!=63)return;
 counts[1]++;if(rec<(triple>0?8:7))return;counts[2]++;
 int B[6][6];for(int i=0;i<6;i++)for(int j=0;j<6;j++)B[i][j]=(i==j)-P[i].exp[j];
 for(int i=0;i<6;i++)for(int j=0;j<6;j++)if(det5(B,i,j))return;
 counts[3]++;
 int A[6][6];int det=0;for(int i=0;i<6;i++)for(int j=0;j<6;j++)A[i][j]=P[i].exp[j];
 for(int i=0;i<6;i++)det+=(i%2?-1:1)*A[0][i]*det5(A,0,i);
 array<int,7> id{}; for(int i=0;i<6;i++)for(int j=0;j<6;j++)id[i]=id[i]*4+A[i][j];id[6]=det;kept.insert(id);if(!det)counts[4]++;
}
void dfs(int i,int up){
 if(i==6){examine();return;}
 for(auto const& e:G[i]){
   int nu=((~((2<<i)-1))&e.mask);if(nu&up)continue;
   bool good=true;
   for(int j=0;j<i;j++){auto const& a=P[j];if(e.t!=a.t)continue;bool dom=true;for(int h=0;h<e.t;h++)if(a.fan[h]>e.fan[h])dom=false;if(dom){good=false;break;}}
   if(!good)continue;P[i]=e;dfs(i+1,up|nu);
 }
}
int main(){
  for(int i=0;i<6;i++){G[i].clear();
   for(int a=0;a<6;a++)for(int b=a;b<6;b++)for(int c=-1;c<6;c++){
    if(a==i||b==i||c==i)continue;
    if(c>=0&&c<b)continue;
    E e{};e.fan={a,b,c};e.t=c<0?2:3;
    for(int k=0;k<e.t;k++)e.exp[e.fan[k]]++,e.mask|=1<<e.fan[k];
    G[i].push_back(e);
   }
  }
  for(const auto& g:G) if(g.size()!=50) return 3;
  dfs(0,0);
  bool ok=true;
  for(int t=0;t<=6;t++){auto &n=states[t];printf("triple %d complete %lld SCC %lld trace %lld rank %lld both %lld\n",t,n[0],n[1],n[2],n[3],n[4]);if(n[4])ok=false;}
  for(auto const& id:kept){printf("chart");for(int a:id) printf(" %d",a);puts("");}
  return ok?0:1;
}
