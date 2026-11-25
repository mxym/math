#include <array>
#include <iostream>
#include <vector>
#include <numeric>
using namespace std; constexpr int P=1009; using W=array<int,4>;
int powmod(int a,int b){int r=1;while(b){if(b&1)r=r*a%P;a=a*a%P;b/=2;}return r;}
int rankmod(vector<vector<int>>&A){int n=A.size(),r=0;for(int j=0;j<n;j++){int k=r;while(k<n&&!A[k][j])k++;if(k==n)continue;swap(A[r],A[k]);auto& row=A[r];int iv=powmod(row[j],P-2);for(int k=r+1;k<n;k++){auto& target=A[k];if(target[j]){int f=P-target[j]*iv%P;for(int l=j;l<n;l++)target[l]=(target[l]+f*row[l])%P;}}++r;}return r;}
int main(int argc,char**argv){for(int ip=1;ip<argc;ip++){int q=stoi(argv[ip]);vector<vector<W>> Wq(q);for(int a=0;a<q;a++)for(int b=0;b<q;b++)for(int c=0;c<q;c++)for(int d=0;d<q;d++)Wq[(a+b+c+d)%q].push_back({a,b,c,d});
vector<vector<int>>D(q,vector<int>(q));for(int i=0;i<q;i++)for(int j=0;j<q;j++)D[i][j]=powmod(i+1,j);
int sum=0;for(int ch=0;ch<q;ch++){auto& U=Wq[ch];auto& V=Wq[(q-ch)%q];int n=U.size();vector<vector<int>> A(n,vector<int>(n));for(int i=0;i<n;i++)for(int j=0;j<n;j++){int s=0;for(int a=0;a<q;a++){int x=a,e=1;for(int t=0;t<4;t++){e=e*D[U[i][t]][x]%P;x=(x+U[i][t])%q;e=e*D[V[j][t]][x]%P;x=(x+V[j][t])%q;}s+=e;}A[i][j]=s%P;}int r=rankmod(A);sum+=r;cout<<q<<" "<<ch<<" "<<r<<endl;}cout<<"total "<<q<<" "<<sum<<endl;}}
