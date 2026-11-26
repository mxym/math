#include<bits/stdc++.h>
using namespace std;
int main(int argc,char**argv){int s=atoi(argv[1]), t=atoi(argv[2]),p=atoi(argv[3]);int N=pow(3,s),h=N/3;
vector<int> I(p),T(2*s+1,1),Z(s),P(s,1);for(int x=1;x<p;x++)for(int y=1;y<p;y++)if(x*y%p==1)I[x]=y;for(int i=1;i<=2*s;i++)T[i]=T[i-1]*t%p;for(int a=2;a<p;a++){Z[0]=1;int k=1;for(;k<=s;k++){int z=Z[k-1]*a%p;if(z==1)break;if(k<s)Z[k]=z;}if(k==s)break;}for(int j=1;j<s;j++)P[j]=3*P[j-1];
auto rot=[&](int x){return x/3+(x%3)*h;};auto charge=[&](int x){int r=0;for(int j=0;j<s;j++){int z=x%3;x/=3;r+=z==1?1:z==2?-1:0;}return r;};
vector<bool>seen(N);vector<vector<int>> dec(N,vector<int>(s));
auto flip=[&](int j){int u=0;for(int i=0;i<s;i++){int x=j%3;j/=3;if(x)x=3-x;u+=x*P[i];}return u;};
auto ent=[&](int u,int v){int z=0;for(int a=0;a<2;a++){int b=a,k=0;bool ok=true;for(int j=0;j<s&&ok;j++){int x=dec[u][j],y=dec[v][j];for(int i:{x,y}){if(i!=0){if(b!=i-1){ok=false;break;}b^=1;}else k+=b;}}if(ok&&a==b)z+=T[k];}return z;};
for(int q=0;q<=s;q++){ vector<vector<int>>orbs; fill(seen.begin(),seen.end(),false); for(int i=0;i<N;i++){for(int j=0;j<s;j++)dec[i][j]=(i/P[j])%3;if(seen[i]||charge(i)!=q)continue;vector<int>a;for(int u=i;!seen[u];u=rot(u)){seen[u]=true;a.push_back(u);}orbs.push_back(a);}
for(int k=0;k<s;k++){vector<vector<int>>O;for(auto o:orbs)if(k*o.size()%s==0)O.push_back(o);int n=O.size();vector<vector<int>>A(n,vector<int>(n));for(int i=0;i<n;i++)for(int j=0;j<n;j++){int z=0;for(int x=0;x<O[j].size();x++)z=(z+Z[k*x%s]*ent(O[i][0],flip(O[j][x])))%p;A[i][j]=z;}
int r=0;for(int j=0;j<n&&r<n;j++){int i=r;while(i<n&&A[i][j]==0)i++;if(i==n)continue;swap(A[r],A[i]);int z=I[A[r][j]];for(int l=r+1;l<n;l++)if(A[l][j]){int f=A[l][j]*z%p;for(int c=j;c<n;c++)A[l][c]=(A[l][c]+p*p-f*A[r][c])%p;}r++;}
cout<<q<<" "<<k<<" "<<n<<" "<<n-r<<endl;}}}
