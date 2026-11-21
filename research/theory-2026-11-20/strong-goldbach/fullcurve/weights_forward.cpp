#include <vector>
#include <array>
#include <algorithm>
#include <numeric>
#include <set>
#include <cstdio>
using namespace std; using V=array<int,5>;vector<V> R; int sets[5];set<array<int,6>> weights;long long ncheck=0;
void go(int j,int start){
 if(j<5){for(int k=start;k+5-j<=(int)R.size();k++){sets[j]=k;go(j+1,k+1);}return;}
 long long a[5][6];
 for(int i=0;i<5;i++){for(int k=0;k<5;k++)a[i][k]=R[sets[i]][k];a[i][5]=1;}
 long long v=1;for(int c=0;c<4;c++){int r=c;while(r<5&&!a[r][c])r++;if(r==5)return;if(r>c)for(int j=c;j<6;j++)swap(a[c][j],a[r][j]);
  for(int i=c+1;i<5;i++)for(int j=c+1;j<6;j++)a[i][j]=(a[i][j]*a[c][c]-a[i][c]*a[c][j])/v;v=a[c][c];}
 if(!a[4][4])return;long long d=abs(a[4][4]);array<int,6>w{};
 for(int i=4;i>=0;i--){long long rhs=d*a[i][5];for(int k=i+1;k<5;k++)rhs-=a[i][k]*w[k];if(rhs%a[i][i])throw 1;w[i]=rhs/a[i][i];if(w[i]*8<=d||w[i]>=d)return;if(i<4&&w[i]>w[i+1])return;}
 if(2*(w[0]+w[1])<=d||w[2]*2>d)return;
 int g=d;for(int i=0;i<5;i++)g=gcd(g,w[i]);for(int i=0;i<5;i++)w[i]/=g;w[5]=d/g;
 if(weights.count(w))return;int n=0;for(auto v:R)n+=inner_product(v.begin(),v.end(),w.begin(),0)==w[5];if(n<6)return;weights.insert(w);
}
int main(){for(int a=0;a<=7;a++)for(int b=0;b<4;b++)for(int c=0;c<4;c++)for(int d=0;d<4;d++)for(int e=0;e<4;e++){int t=b+c+d+e;if(!( (!t&&a>=2) || (t==1&&a>=1&&a<=4) ||(t==2&&a<=1)||(t==3&&a==0)))continue;R.push_back({a,b,c,d,e});}fprintf(stderr,"rows %zu\n",R.size());go(0,0);for(auto w:weights){for(int x:w)printf("%d ",x);puts("");}fprintf(stderr,"weights %zu\n",weights.size());}
