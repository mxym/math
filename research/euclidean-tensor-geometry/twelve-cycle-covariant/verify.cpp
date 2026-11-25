#include <array>
#include <vector>
#include <iostream>
#include <cstdint>
#include <cassert>
#include <stdexcept>
#include <algorithm>
using namespace std;
#ifndef Q
#define Q 5
#endif
constexpr int q=Q,n=q*q*q*q*q*q,p=61;
int pw(int x,int k){int z=1;for(;k;k/=2,x=x*x%p)if(k&1)z=z*x%p;return z;}
int md(int x){x%=p;return x<0?x+p:x;}
using W=array<int,6>;vector<W> w(n);
int encode(W x){int y=0;for(int i=5;i>=0;i--)y=q*y+x[i];return y;}
int idx(int i,int r,int s){W x;for(int j=0;j<6;j++)x[j]=(w[i][(j+r)%6]+s)%q;return encode(x);}
struct O{int first;vector<array<int,3>> elems;vector<array<int,2>> stab;};
int main(int argc,char**argv){
 static_assert(q==5||q==6);
 if(argc!=1)throw runtime_error("no arguments: exact static certificate");
 const int a5[5][5]={{41,27,49,50,11},{26,42,45,33,23},{21,34,45,60,14},
                     {55,2,11,51,26},{11,38,27,23,10}};
 const int a6[6][6]={{44,44,21,55,36,14},{33,39,60,6,6,14},{28,49,31,46,31,32},
                     {48,10,48,22,24,19},{15,8,20,25,12,15},{3,6,50,13,53,51}};
 int A[q][q][q];
 for(int i=0;i<q;i++)for(int j=0;j<q;j++)
  for(int k=0;k<q;k++)A[k][(i+k)%q][(j+k)%q]=q==5?a5[i][j]:a6[i][j];
 for(int i=0;i<n;i++){int k=i;for(auto &v:w[i])v=k%q,k/=q;}
 vector<bool> used(n); vector<O> orbs;
 for(int i=0;i<n;i++)if(!used[i]) {
  O o{i,{},{}};
  for(int r=0;r<6;r++)for(int s=0;s<q;s++){
   int b=idx(i,r,s);
   if(b==i)o.stab.push_back({r,s});
   if(!used[b])o.elems.push_back({b,r,s});
   used[b]=true;
  }
  orbs.push_back(o);
 }
 int ret=0,root=2;while(pw(root,30)==1||pw(root,20)==1||pw(root,12)==1)root++;
 const int expected5[6][5]={{31,55,38,38,55},{51,16,30,50,32},{33,32,54,41,11},{20,51,39,39,51},{26,29,36,37,40},{51,32,50,30,16}};
 const int expected6[6][6]={{29,37,25,56,25,37},{18,56,44,51,11,9},{23,4,42,37,56,10},{3,59,58,57,58,59},{44,10,56,37,42,4},{53,9,11,10,44,56}};
 int dimensions=0;
 vector<vector<uint8_t>> forms(orbs.size(),vector<uint8_t>(n));
 vector<array<uint8_t,q*q>> left(n),right(n);
 for(int i=0;i<n;i++){
  int X[q][q]={};
  for(int j=0;j<q;j++)X[j][j]=1;
  for(int z:w[i]){
   int Y[q][q]={};
   for(int j=0;j<q;j++)for(int k=0;k<q;k++){
    for(int a=0;a<q;a++)Y[j][k]+=X[j][a]*A[z][a][k];
    Y[j][k]%=p;
   }
   for(int j=0;j<q;j++)for(int k=0;k<q;k++)X[j][k]=Y[j][k];
  }
  for(int j=0;j<q;j++)for(int k=0;k<q;k++){left[i][j*q+k]=X[j][k];right[i][k*q+j]=X[j][k];}
 }
 auto half=[](const W&a,const W&b,int j){
  int s=0,t=1;
  for(int i=j;i<j+3;i++){s+=t*a[i];t*=q;s+=t*b[i];t*=q;}
  return s;
 };
 for(int i=0;i<(int)orbs.size();i++)for(int j=0;j<n;j++){
  const auto &a=w[orbs[i].first],&b=w[j];
  const auto &x=left[half(a,b,0)],&y=right[half(a,b,3)];
  int z=0;
  for(int k=0;k<q*q;k++)z+=x[k]*y[k];
  forms[i][j]=z%p;
 }
 for(int h=0;h<6;h++)for(int k=0;k<q;k++){
  int t[6][q];for(int r=0;r<6;r++)for(int s=0;s<q;s++)t[r][s]=pw(root,(10*h*r+(60/q)*k*s)%60);
  vector<int> keep;
  for(int i=0;i<(int)orbs.size();i++){bool ok=true;for(const auto &e:orbs[i].stab)if(t[e[0]][e[1]]!=1)ok=false;if(ok)keep.push_back(i);}
  int m=keep.size(); vector<vector<int>> M(m,vector<int>(m));
  for(int i=0;i<m;i++)for(int j=0;j<m;j++){
   int s=0;for(const auto &e:orbs[keep[j]].elems)s+=t[e[1]][e[2]]*forms[keep[i]][e[0]];
   M[i][j]=s%p;
  }
  int rk=0,det=1;
  for(int j=0;j<m;j++){
   int a=rk;while(a<m&&!M[a][j])a++;if(a==m)continue;
   if(a!=rk)swap(M[a],M[rk]),det=md(-det);
   int s=M[rk][j];det=det*s%p;int b=pw(s,p-2);
   for(int i=rk+1;i<m;i++)if(M[i][j]){
    int d=md(-M[i][j]*b);for(int k=j+1;k<m;k++)M[i][k]=(M[i][k]+d*M[rk][k])%p;
   }
   rk++;
  }
  cout<<h<<" "<<k<<" "<<m<<" "<<rk<<" "<<(rk==m?det:0)<<endl;
  ret+=m-rk; dimensions+=m;
  if(rk!=m||det!=(q==5?expected5[h][k]:expected6[h][k]))throw runtime_error("block certificate mismatch");
 }
 if(dimensions!=n)throw runtime_error("sector dimension sum mismatch");
 cout<<"defect "<<ret<<endl;return ret!=0;
}
