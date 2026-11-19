/* Exact polynomial-minor arithmetic. The Python driver generates all input. */
#include <gmpxx.h>
#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <limits>
#include <numeric>
#include <set>
#include <stdexcept>
#include <vector>
using namespace std;
using P=array<int,5>; struct Term{P e; long c;};
using Coeff=array<array<vector<Term>,4>,4>;using Mat=array<array<mpz_class,4>,4>;
static void ck(bool v,const char*s){if(!v)throw runtime_error(s);}
static mpz_class det(const Mat&m,int n){
 if(n==1)return m[0][0];
 if(n==2)return m[0][0]*m[1][1]-m[0][1]*m[1][0];
 if(n==3)return m[0][0]*(m[1][1]*m[2][2]-m[1][2]*m[2][1])-m[0][1]*(m[1][0]*m[2][2]-m[1][2]*m[2][0])+m[0][2]*(m[1][0]*m[2][1]-m[1][1]*m[2][0]);
 // Laplace expansion along rows 0,1.
 mpz_class s=0;
 for(int i=0;i<4;i++)for(int j=i+1;j<4;j++){
  int k=0;while(k==i||k==j)++k;int l=k+1;while(l==i||l==j)++l;
  mpz_class a=m[0][i]*m[1][j]-m[1][i]*m[0][j],b=m[2][k]*m[3][l]-m[3][k]*m[2][l];
  if((i+j)%2==1)s+=a*b;else s-=a*b;
 }
 return s;
}
int main(int argc,char**argv){
 ck(argc==2,"expected generated input");ifstream f(argv[1]);int blocks=0;f>>blocks;ck(f&&blocks==33,"bad task count");
 set<string>names;long long allpos=0;int npoly=0;constexpr int bits=256,limbs=4;ck(sizeof(unsigned long)==8,"requires 64-bit word");
 for(int h=0;h<blocks;h++){
  string name;int hd,nm;f>>name>>hd>>nm;ck(f&&names.insert(name).second&&hd>=13&&hd<=15&&nm==(h<25?1:3),"bad block");
  vector<Coeff> H(nm);
  for(int k=0;k<nm;k++)for(int i=0;i<4;i++)for(int j=i;j<4;j++){
   int nz;f>>nz;ck(f&&nz>0&&nz<=3876,"invalid support size");set<P>distinct;
   for(int x=0;x<nz;x++){Term t;for(int& a:t.e)f>>a;f>>t.c;ck(f&&t.c!=0&&t.c>-(1L<<45)&&t.c<(1L<<45)&&distinct.insert(t.e).second,"invalid coefficient");for(int b:t.e)ck(b>=0&&b<=hd,"invalid degree");ck(accumulate(t.e.begin(),t.e.end(),0)==hd,"wrong homogeneous degree");H[k][i][j].push_back(t);}
   if(i!=j)H[k][j][i]=H[k][i][j];
  }
  for(int n=1;n<=4;n++){
   // Bounding box for exponents of det across all permutations;
   // L1 bound uses the triangle inequality even when coefficients cancel.
   array<array<P,4>,4>lo{},hi{};mpz_class norm=0;
   for(int i=0;i<n;i++)for(int j=0;j<n;j++){
    lo[i][j].fill(100);hi[i][j].fill(-100);mpz_class l1=0;
    for(const auto& A:H)for(const auto&t:A[i][j]){
     l1+=labs(t.c);for(int r=0;r<5;r++){lo[i][j][r]=min(lo[i][j][r],t.e[r]);hi[i][j][r]=max(hi[i][j][r],t.e[r]);}}
    if(norm<l1)norm=l1;
   }
   mpz_class bound=1;for(int k=1;k<=n;k++){bound*=norm;bound*=k;}ck(bound<(mpz_class(1)<<(bits-1)),"ambiguous packed digits");
   vector<int>perm(n);iota(perm.begin(),perm.end(),0);P lower,upper;lower.fill(1000);upper.fill(-1000);
   do{for(int s=0;s<5;s++){int a=0,b=0;for(int i=0;i<n;i++){a+=lo[i][perm[i]][s];b+=hi[i][perm[i]][s];}lower[s]=min(lower[s],a);upper[s]=max(upper[s],b);}}while(next_permutation(perm.begin(),perm.end()));
   // Set one gap equal to one by homogeneity. Encode the other four
   // exponents injectively after subtracting componentwise lower bounds.
   P ix={0,1,2,3,4},stride{};stable_sort(ix.begin(),ix.end(),[&](int i,int j){return upper[i]-lower[i]<upper[j]-lower[j];});
   long cells=1;for(int k=0;k<4;k++){int r=ix[k],len=1+upper[r]-lower[r];ck(len>0&&cells<=5000000/len,"packing size");stride[r]=cells;cells*=len;}
   auto power=[&](P e){return inner_product(e.begin(),e.end(),stride.begin(),0L);};long off=power(lower);
   vector<Mat>A(nm);for(int k=0;k<nm;k++)for(int i=0;i<n;i++)for(int j=i;j<n;j++){
    long len=0;for(const auto&t:H[k][i][j])len=max(len,power(t.e));
    vector<unsigned long>pos((len+1)*limbs),neg(pos.size());
    for(const auto&t:H[k][i][j]){auto& a=t.c>0?pos:neg;auto& word=a[power(t.e)*limbs];unsigned long add=labs(t.c);ck(word<=numeric_limits<unsigned long>::max()-add,"coefficient collision overflow");word+=add;}
    mpz_class vp,vn;mpz_import(vp.get_mpz_t(),pos.size(),-1,8,0,0,pos.data());mpz_import(vn.get_mpz_t(),neg.size(),-1,8,0,0,neg.data());A[k][j][i]=A[k][i][j]=vp-vn;
   }
   // Recover coefficients in the auxiliary nonnegative ratio from its
   // values at 0,...,2n (constant matrices need only t=0).
   int d=(nm-1)*n;vector<mpz_class>diff,coef(d+1);Mat M;
   for(int t=0;t<=d;t++){for(int i=0;i<n;i++)for(int j=0;j<n;j++){M[i][j]=A[0][i][j];if(nm==3)M[i][j]+=t*A[1][i][j]+t*t*A[2][i][j];}diff.push_back(det(M,n));}
   vector<long>basis={1};int den=1;
   for(int r=0;r<=d;r++){
    ck(mpz_divisible_ui_p(diff[0].get_mpz_t(),den),"Newton denominator");mpz_class v=diff[0]/den;
    for(int k=0;k<=r;k++)coef[k]+=basis[k]*v;
    for(int k=0;k<d-r;k++)diff[k]=diff[k+1]-diff[k];
    vector<long>next(r+2);for(int k=0;k<=r;k++){next[k+1]+=basis[k];next[k]-=r*basis[k];}basis=next;den*=r+1;
   }
   for(int k=0;k<=d;k++){
    mpz_class v=coef[k];ck(v>0&&mpz_divisible_2exp_p(v.get_mpz_t(),size_t(off)*bits),"nonpositive evaluation / bad shift");v>>=size_t(off)*bits;
    ck(mpz_sizeinbase(v.get_mpz_t(),2)<=size_t(bits)*cells,"support overflow");vector<unsigned long>digits(cells*limbs);size_t got=0;
    mpz_export(digits.data(),&got,-1,8,0,0,v.get_mpz_t());
    long pos=0;for(long s=0;s<cells;s++){ck(!(digits[s*limbs+3]>>63),"negative monomial");if(digits[s*limbs]|digits[s*limbs+1]|digits[s*limbs+2]|digits[s*limbs+3])++pos;}
    ck(pos>0,"zero polynomial");allpos+=pos;npoly++;
    cout<<name<<" minor "<<n<<" coefficient "<<k<<" positive "<<pos<<endl;
   }
  }
 }
 string extra;ck(!(f>>extra)&&f.eof()&&names.size()==33&&npoly==292,"bad final count");
 cout<<"PASS "<<npoly<<" nonzero nonnegative-coefficient polynomials; positive monomials "<<allpos<<endl;
}
