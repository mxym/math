#include <gmpxx.h>
#include <cstdlib>
#include <iostream>
#include <array>
#include <vector>
using namespace std;
const int P[]={3,5,7,11,13,17,19,23,29,31,37,41,43,47,53};
int peel(mpz_class& z,int p){int k=0;while(mpz_divisible_ui_p(z.get_mpz_t(),p)){z/=p;++k;}return k;}
int main(){
 long long cells=0,direct=0,powers=0,roots=0,possible=0;
 for(auto p:P)for(auto q:P)if(p!=q){
 mpz_class u=q;
 for(int d=2;d<=750;d++){
 ++cells;u*=q;mpz_class n=u+p,h=n-q;
 int e=peel(h,p);
 auto test=[&](mpz_class r,int f){
 if(r<=max(p,q)||e+f<2)return;
 mpz_class z=n-r;if(z<=1)return;int b=peel(z,p),c=peel(z,q);
 if(z!=1||b+c<2)return;
 // Since p only sees q, q sees r and possibly p, strong connectivity requires
 // b>0 or (c>0 and e>0). If r composite, these are still optimistic checks.
 if(!(b>0||(c>0&&e>0)))return;
 cout<<"possible "<<p<<" "<<q<<" "<<d<<" "<<e<<" "<<r<<" "<<f<<" "<<b<<" "<<c<<" n "<<n<<endl;possible++;};
 if(e>0){direct++;test(h,1);}
 if(h<=1||!mpz_perfect_power_p(h.get_mpz_t()))continue;
 powers++;unsigned bits=mpz_sizeinbase(h.get_mpz_t(),2);
 for(unsigned f=2;f<=bits;f++){mpz_class r;if(mpz_root(r.get_mpz_t(),h.get_mpz_t(),f)){roots++;test(r,f);}}
 }}
 cout<<"cells "<<cells<<" direct "<<direct<<" perfect-powers "<<powers<<" exact-roots "<<roots<<" possible "<<possible<<endl;
 return possible!=0;}
