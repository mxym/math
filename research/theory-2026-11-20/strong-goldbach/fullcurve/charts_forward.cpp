#include <array>
#include <vector>
#include <algorithm>
#include <iostream>
#include <numeric>
#include <cstdio>
using namespace std;using R=array<int,5>;
R w,G[6],M[6];int ids[6],used,d,tt;vector<R> opts;int usedopt[70],masks[70]; long long st[10],sumt[10];bool loud;
int det(int idx[],int col[],int n,R a[]){
 int ord[5],s=0;copy(col,col+n,ord);do{int v=1;for(int i=0;i<n;i++){v*=a[idx[i]][ord[i]];for(int j=0;j<i;j++)if(ord[j]>ord[i])v=-v;}s+=v;}while(next_permutation(ord,ord+n));return s;
}
const int prime=101;int invs[101];
int mrank(const vector<array<int,6>>& rows,int n){
 int m[25][6]={},i=0;for(auto&r:rows){for(int j=0;j<n;j++)m[i][j]=(r[j]%prime+prime)%prime;i++;}
 int rr=0;for(int j=0;j<n;j++){
   int k=rr;while(k<i&&!m[k][j])k++;if(k==i)continue;
   for(int l=j;l<n;l++)swap(m[k][l],m[rr][l]);int inv=invs[m[rr][j]];
   for(k=rr+1;k<i;k++){int x=m[k][j]*inv%prime;for(int l=j;l<n;l++)m[k][l]=(m[k][l]+prime*prime-x*m[rr][l])%prime;}rr++;
 }return rr;
}
void enddfs(){
 st[0]++;int h=1;for(int it=0;it<6;it++)for(int i=0;i<6;i++)if(h&(1<<i)) h|=(masks[ids[i]]<<1);
 if(h!=63)return;st[1]++;
 if(accumulate(G[0].begin(),G[0].end(),0,[](int x,int y){return gcd(x,y);})!=1)return;
 for(int i=0;i<6;i++)for(int j=0;j<5;j++)M[i][j]=(j+1==i)-G[i][j];
 int ix[5],col[]={0,1,2,3,4};vector<array<int,6>> bt(6);for(int i=0;i<6;i++)for(int j=0;j<5;j++)bt[i][j]=M[i][j];
 if(mrank(bt,5)==5)return;
 bool rank5=false;for(int no=0;no<6;no++){int k=0;for(int i=0;i<6;i++)if(i!=no)ix[k++]=i;if(det(ix,col,5,G)){rank5=true;break;}}if(!rank5)return;
 int v[6]={};int ds=0;
 for(int i=0;!ds&&i<6;i++)for(int j=i+1;!ds&&j<6;j++){int k=0;for(int b=0;b<6;b++)if(b!=i&&b!=j)ix[k++]=b;
  int oth[]={1,2,3,4};ds=det(ix,oth,4,M);if(!ds)continue;
  for(int l=0;l<5;l++){int tmp[4],z=0;for(int o=0;o<5;o++)if(o!=l)tmp[z++]=o;v[l+1]=(l%2?-1:1)*det(ix,tmp,4,M);}
 }
 if(!ds)return;for(auto&r:M){int s=0;for(int j=0;j<5;j++)s+=r[j]*v[j+1];if(s)return;}st[2]++;
 int m=d/2+1;for(int i=1;i<6;i++)if(w[i-1]<m)for(int j=0;j<i;j++)if(v[i]==v[j])return;
 int pos=0,neg=0;for(int x:v){pos+=x>0;neg+=x<0;}if(min(pos,neg)<2)return;
 bool signok=false;for(int sm=0;sm<32;sm++){bool ok=true;for(int i=0;i<6;i++){int z=i?((sm>>(i-1))&1):0;for(int j=0;j<5;j++)if(sm&(1<<j))z+=G[i][j];if(!(z&1)){ok=false;break;}}if(ok){signok=true;break;}}if(!signok)return;st[3]++;
 cout<<"raw "<<tt;for(int i:ids)cout<<" "<<i;cout<<endl;
}
void dfs(int i,int sm){if(i==6){enddfs();return;}for(int id=0;id<opts.size();id++){auto&r=opts[id];if(usedopt[id]||(i&&r[i-1]))continue;int n=masks[id]&~((1<<i)-1);if(n&sm)continue;ids[i]=id;G[i]=r;usedopt[id]=1;dfs(i+1,sm|n);usedopt[id]=0;}}
int main(int argc,char**argv){loud=argc>1;for(int i=1;i<prime;i++)for(int j=1;j<prime;j++)if(i*j%prime==1)invs[i]=j;
 while(cin>>w[0]>>w[1]>>w[2]>>w[3]>>w[4]>>d){opts.clear();for(int a=0;a<=7;a++)for(int b=0;b<4;b++)for(int c=0;c<4;c++)for(int x=0;x<4;x++)for(int y=0;y<4;y++){R r={a,b,c,x,y};if(inner_product(r.begin(),r.end(),w.begin(),0)!=d)continue;int m=0;for(int k=0;k<5;k++)if(r[k])m|=1<<k;masks[opts.size()]=m;opts.push_back(r);}
 tt++;fill(st,st+10,0);dfs(0,0);cout<<"profile "<<tt;for(int x:w)cout<<" "<<x;cout<<" / "<<d<<" :";for(int j=0;j<4;j++){cout<<" "<<st[j];sumt[j]+=st[j];}cout<<endl;}
 cerr<<"totals";for(int j=0;j<4;j++)cerr<<" "<<sumt[j];cerr<<endl;}
