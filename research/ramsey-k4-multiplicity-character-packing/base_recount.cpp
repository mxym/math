// Exact recount of the published SK base matrix. Input: headerless int32, row-major,
// little-endian file exported from the pinned JSON using verify.py.
#include <gmpxx.h>
#include <cstdint>
#include <cstdio>
#include <vector>
#include <array>
#include <algorithm>
#include <iostream>
#include <stdexcept>
#include <string>
using namespace std;using cpp_int=mpz_class;using u128=unsigned __int128;
static const int N=3840,q=20,m=N/q,D=1<<20;
cpp_int big(u128 n){cpp_int v=(unsigned long)(n>>64);v<<=64;v+=(unsigned long)n;return v;}
using Block=array<int,q*q>;
using Tup=array<int,4>;
int main(int argc,char**argv){
 if(argc!=2)return 2;
 vector<int>W(N*N);FILE*f=fopen(argv[1],"rb");if(!f||fread(W.data(),sizeof(int),W.size(),f)!=W.size()||fgetc(f)!=EOF)throw runtime_error("input size");fclose(f);
 vector<int>C(m*m),rowsum(m*m);vector<Block>blocks(m*m);
 for(int i=0;i<m;i++)for(int j=0;j<m;j++){auto&t=blocks[i*m+j];int s=0;bool constant=true;
   for(int a=0;a<q;a++)for(int b=0;b<q;b++){int z=W[(i*q+a)*N+j*q+b];if(z<0||z>D||z!=W[(j*q+b)*N+i*q+a])throw runtime_error("invalid matrix");
     t[a*q+b]=z;if(a==0)s+=z;if(z!=t[0])constant=false;
   }
   if(constant&&t[0]!=0&&t[0]!=D)throw runtime_error("expected monochromatic constant block");
   C[i*m+j]=constant?(t[0]?1:0):2;rowsum[i*m+j]=s;
   // Simultaneous group action (Z/5)x(F2)^2 is transitive within a coarse part.
   for(int a=0;a<q;a++)for(int b=0;b<q;b++){int av=(a+4)%q,bv=(b+4)%q;
     if(t[a*q+b]!=t[av*q+bv]||t[a*q+b]!=t[(a^1)*q+(b^1)]||t[a*q+b]!=t[(a^2)*q+(b^2)])throw runtime_error("group check");
   }
 }
 cpp_int total=0;
 for(int i=0;i<m;i++)for(int j=i;j<m;j++)for(int k=j;k<m;k++)for(int l=k;l<m;l++){
   Tup x{i,j,k,l};int idx[]={i*m+j,i*m+k,i*m+l,j*m+k,j*m+l,k*m+l};
   int ends[][2]={{0,1},{0,2},{0,3},{1,2},{1,3},{2,3}};
   int c[3]={},deg[4]={};for(int e=0;e<6;e++){int col=C[idx[e]];c[col]++;if(col==2){deg[ends[e][0]]++;deg[ends[e][1]]++;}}
   if(c[0]&&c[1])continue;
   int mult=24; for(int t=1,run=1;t<4;t++){if(x[t]==x[t-1]){run++;mult/=run;}else run=1;}
   for(int red=0;red<=1;red++){
     if(c[red?0:1])continue;
     int s=c[2]; cpp_int count=0;
     auto coeff=[&](int e,int a,int b){int v=blocks[idx[e]][a*q+b];return red?v:D-v;};
     bool forest=(s<=2 || (s==3&&*min_element(deg,deg+4)>=1));
     if(forest){
       count=1;for(int p=0;p<4-s;p++)count*=q;
       for(int e=0;e<6;e++){if(C[idx[e]]!=2)count*=D;else{int v=rowsum[idx[e]];count*=red?v:q*D-v;}}
     }else if(s==3){
       int pair[3],r=0;for(int e=0;e<6;e++)if(C[idx[e]]==2)pair[r++]=e;
       int noniso[3];r=0;for(int h=0;h<4;h++)if(deg[h])noniso[r++]=h;
       u128 v=0;int fiber[4]={};
       for(int a=0;a<q;a++)for(int b=0;b<q;b++){fiber[noniso[1]]=a;fiber[noniso[2]]=b;
         u128 p=1;for(int h=0;h<3;h++){int e=pair[h];p*=coeff(e,fiber[ends[e][0]],fiber[ends[e][1]]);}v+=p;}
       count=big(v);count*=q*q;count*=cpp_int(D)*D*D;
     }else{
       for(int a=0;a<q;a++)for(int b=0;b<q;b++){
         u128 p=(u128)coeff(0,0,a)*coeff(1,0,b)*coeff(3,a,b);u128 acc=0; // <=20 D^6 <2^125
         for(int h=0;h<q;h++)acc+=p*coeff(2,0,h)*coeff(4,a,h)*coeff(5,b,h);
         count+=big(acc);
       }
       count*=q;
     }
     total+=count*mult;
   }
 }
 cpp_int denom=cpp_int(N)*N*N*N;denom<<=120;
 cpp_int a=total,b=denom;while(b!=0){cpp_int t=a%b;a=b;b=t;}cout<<total/a<<"/"<<denom/a<<"\n";
}
