#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <unordered_map>
#include <vector>
using namespace std;
constexpr int P=17,K=12;
const array<int,K> s{0,1,2,3,4,5,6,7,8,9,11,15};
int inv[P],pwr[P][11],v[K][8],lambda[K];
int m(int a){ a%=P; return a<0?a+P:a;}
using Poly=array<int,8>;
Poly bank7[P][3][P],bank6[P][P];
Poly shift(const Poly&a,int h){
 Poly r{}; for(int k=7;k>=0;k--){
  for(int j=7;j>0;j--)r[j]=m(r[j-1]-h*r[j]);
  r[0]=m(a[k]-h*r[0]);
 }return r;
}
int choose_weight(const Poly& a){int tot=0,sq=0; for(int t=0;t<P;t++){
 int x=0;for(int j=7;j>=0;j--)x=m(x*t+a[j]); if(x>6)return -1;
 tot+=x;sq+=x*x;
}return tot==34?(sq-68)/34:-1;}
struct Choice{array<int,3> i{-1,-1,-1},which{};};
long long leaders=0, centers=0, degree5=0, radon=0, physical=0;
int main(){
 for(int a=0;a<P;a++){for(int b=1;b<P;b++)if(a*b%P==1)inv[a]=b;pwr[a][0]=1;
  for(int j=1;j<=10;j++)pwr[a][j]=m(a*pwr[a][j-1]);}
 for(int i=0;i<K;i++){int den=1;for(int j=0;j<K;j++)if(i!=j)den=m(den*(s[i]-s[j]));lambda[i]=inv[den];
  for(int j=0;j<=7;j++)v[i][j]=pwr[s[i]][j];}
 const Poly sextic[2]={{2,0,1,0,2,0,1,0},{6,0,13,0,12,0,3,0}};
 const Poly septic[3]={{2,1,0,7,0,7,0,1},{3,0,9,3,8,12,0,1},{6,16,0,8,14,6,0,1}};
 for(int l=1;l<P;l++){
  for(int t=0;t<2;t++){Poly A=sextic[t];for(int j=0;j<8;j++)A[j]=m(A[j]*pwr[l][j]);
   if(choose_weight(A)!=2)abort();for(int h=0;h<P;h++)bank6[A[6]][h]=shift(A,h);}
  for(int t=0;t<3;t++){Poly A=septic[t];for(int j=0;j<8;j++)A[j]=m(A[j]*pwr[l][j]);
   if(choose_weight(A)!=(t?2:1))abort();for(int h=0;h<P;h++)bank7[A[7]][t][h]=shift(A,h);}
 }
 const auto process=[&](array<int,K> a){
  vector<int> L,H;for(int i=0;i<K;i++)if(a[i])H.push_back(i);else L.push_back(i);
  if(H.size()<9)return;leaders++;
  int R=L.size(),extra=3-R, mat[6][9]={};
  for(int j=0;j<6;j++){for(int k=0;k<R;k++)mat[j][k]=v[L[k]][j];mat[j][R+j]=1;}
  for(int k=0;k<R;k++){
   int u=k;while(u<6&&!mat[u][k])u++;if(u==6)abort();
   for(int j=0;j<R+6;j++)swap(mat[u][j],mat[k][j]);
   int invp=inv[mat[k][k]];for(int j=0;j<R+6;j++)mat[k][j]=m(mat[k][j]*invp);
   for(int j=0;j<6;j++)if(j!=k){int c=mat[j][k];for(int l=0;l<R+6;l++)mat[j][l]=m(mat[j][l]-c*mat[k][l]);}
  }
  int col[K][6]={},base[6]={},baseC[K]={},factors[K]={},ih[K]={},t[6]={};
  for(int i:H){baseC[i]=bank7[a[i]][0][0][5];ih[i]=inv[m(-7*a[i])];}
  for(int i=0;i<K;i++)factors[i]=m(lambda[i]*(s[i]-s[H[0]])*(s[i]-s[H[1]]));
  for(int i:H)for(int j=R;j<6;j++){for(int k=0;k<6;k++)col[i][j]+=mat[j][R+k]*v[i][k];col[i][j]=m(col[i][j]);base[j]+=col[i][j]*baseC[i];}
  for(int j=R;j<6;j++)base[j]=m(base[j]);
  unordered_map<int,vector<Choice>> lookup;Choice choice; int incr[6]={};
  auto gen=[&](auto&&self,int begin,int depth)->void{
   if(depth==extra){int key=0;for(int j=R;j<6;j++)key=17*key+m(incr[j]);lookup[key].push_back(choice);return;}
   for(int q=begin;q<=(int)H.size()-(extra-depth);q++){int i=H[q];choice.i[depth]=i;
    for(int k=1;k<=2;k++){choice.which[depth]=k;int dif=bank7[a[i]][k][0][5]-baseC[i];for(int j=R;j<6;j++)incr[j]+=dif*col[i][j];
     self(self,q+1,depth+1);for(int j=R;j<6;j++)incr[j]-=dif*col[i][j];
    }
   }
  };gen(gen,0,0);
  for(int q0=0;q0<P;q0++)for(int q1=0;q1<P;q1++)for(int q2=0;q2<P;q2++){
   int c6[K]={},cent[K]={};bool ok=true;
   for(int i:L){c6[i]=m(factors[i]*(q0+q1*s[i]+q2*pwr[s[i]][2]));if(!c6[i]){ok=false;break;}}
   if(!ok)continue;
   centers++;
   for(int j=R;j<6;j++)t[j]=base[j];
   for(int i:H){int b=m(factors[i]*(q0+q1*s[i]+q2*pwr[s[i]][2]));cent[i]=m(b*ih[i]);int diff=m(4*a[i]*cent[i]*cent[i]);for(int j=R;j<6;j++)t[j]+=diff*col[i][j];}
   int key=0;for(int j=R;j<6;j++)key=17*key+m(-t[j]);
   auto it=lookup.find(key);if(it==lookup.end())continue;
   for(const Choice& T:it->second){
    int which[K]={};for(int i=0;i<extra;i++)which[T.i[i]]=T.which[i];
    array<const Poly*,K> Pp{};
    int syn[6]={};for(int i:H){Pp[i]=&bank7[a[i]][which[i]][cent[i]];for(int k=0;k<6;k++)syn[k]+=(*Pp[i])[5]*v[i][k];}
    for(int i=0;i<R;i++){int b=0;for(int j=0;j<6;j++)b-=mat[i][R+j]*syn[j];int h=m(b*inv[m(-6*c6[L[i]])]);Pp[L[i]]=&bank6[c6[L[i]]][h];}
    for(int k=0;k<6;k++){int z=0;for(int i=0;i<K;i++)z+=(*Pp[i])[5]*v[i][k];if(m(z))abort();}
    degree5++; bool ok0=true;
    for(int d=4;d>=0&&ok0;d--)for(int k=0;k<=d;k++){int z=d==0?-22:0;
     for(int i=0;i<K;i++)z+=(*Pp[i])[d]*v[i][k];
     if(m(z)){ok0=false;break;}
    }
    if(!ok0)continue;
    radon++;
    for(int x=0;x<P&&ok0;x++)for(int y=0;y<P;y++){int n=-22;for(int i=0;i<K;i++){int t=m(x+s[i]*y),v0=0;for(int j=7;j>=0;j--)v0=m(v0*t+(*Pp[i])[j]);n+=v0;}if(n!=0&&n!=17){ok0=false;break;}}
    if(ok0){physical++;cerr<<"Physical witness\n";}
   }
  }
 };
 for(int p0=0;p0<P;p0++)for(int p1=0;p1<P;p1++)for(int p2=0;p2<P;p2++)for(int p3=0;p3<P;p3++){
  int first=p0?p0:(p1?p1:(p2?p2:p3));if(first!=1)continue;
  array<int,K> a{};
  for(int i=0;i<K;i++)a[i]=m(lambda[i]*(p0+p1*s[i]+p2*pwr[s[i]][2]+p3*pwr[s[i]][3]));
  process(a);
 }
 if(leaders!=5220||centers!=24601160||degree5!=3088||radon||physical)abort();
 cout<<"leading="<<leaders<<" centers="<<centers<<" degree5="<<degree5<<" Radon="<<radon<<" physical="<<physical<<endl;
}
