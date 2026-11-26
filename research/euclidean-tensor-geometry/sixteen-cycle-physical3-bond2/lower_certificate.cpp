#include<bits/stdc++.h>
using namespace std;
int main(int argc,char**argv){int s=atoi(argv[1]), t=atoi(argv[2]),p=atoi(argv[3]);int N=pow(3,s);vector<vector<vector<int>>> w(2*s+1);
for(int i=0;i<N;i++){int z=i,q=0;vector<int>a;for(int k=0;k<s;k++){int x=z%3;z/=3;a.push_back(x);q+=x==1?1:x==2?-1:0;}w[q+s].push_back(a);}
vector<int>I(p),T(2*s+1,1);for(int x=1;x<p;x++)for(int y=1;y<p;y++)if(x*y%p==1)I[x]=y;for(int i=1;i<=2*s;i++)T[i]=T[i-1]*t%p;
int total=0;for(int q=0;q<=2*s;q++){int n=w[q].size();vector<vector<unsigned short>>A(n,vector<unsigned short>(n));
for(int i=0;i<n;i++)for(int j=0;j<n;j++){int z=0;for(int a=0;a<2;a++){int b=a,k=0;bool ok=true;for(int h=0;h<2*s;h++){int x=h%2?w[2*s-q][j][h/2]:w[q][i][h/2];if(x!=0){if(b!=x-1){ok=false;break;}b^=1;}else k+=b;}if(ok&&a==b)z+=T[k];}A[i][j]=z%p;}
int r=0;for(int j=0;j<n&&r<n;j++){int i=r;while(i<n&&A[i][j]==0)i++;if(i==n)continue;swap(A[r],A[i]);int z=I[A[r][j]];
for(int k=r+1;k<n;k++)if(A[k][j]){int f=A[k][j]*z%p;for(int l=j;l<n;l++)A[k][l]=(A[k][l]+p*p-f*A[r][l])%p;}r++;}
cout<<q-s<<" "<<n<<" "<<(n-r)<<endl;total+=n-r;}
cout<<"defect "<<total<<endl;}
