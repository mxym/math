#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <cstdio>
#include <vector>
using namespace std;

struct Fields{
 int m,q,N,poly;
 vector<int> sq,tr;
 Fields(int mm,int pp):m(mm),q(1<<m),N(q*q),poly(pp),sq(q),tr(q){
  for(int x=0;x<q;x++)sq[x]=km(x,x);
  for(int x=0;x<q;x++){
   int y=x,z=0;
   for(int i=0;i<m;i++){z^=y;y=sq[y];}
   assert(y==x&&(z==0||z==1));tr[x]=z;
  }
  for(int x=1;x<q;x++)assert(kpow(x,q-1)==1);
  assert(tr[1]==1);
 }
 int km(int x,int y)const{
  int z=0;
  for(;y;y>>=1){if(y&1)z^=x;x<<=1;if(x&q)x^=poly;}
  return z;
 }
 int kpow(int x,int e)const{
  int z=1;for(;e;e>>=1,x=sq[x])if(e&1)z=km(z,x);return z;
 }
 int em(int z,int w)const{
  int a=z&(q-1),b=z>>m,c=w&(q-1),d=w>>m;
  int ac=km(a,c),bd=km(b,d),all=km(a^b,c^d);
  return (ac^bd)|((all^ac)<<m);
 }
 int epow(int x,int e)const{
  int z=1;for(;e;e>>=1,x=em(x,x))if(e&1)z=em(z,x);return z;
 }
 int sqe(int x)const{int a=sq[x&(q-1)],b=sq[x>>m];return (a^b)|(b<<m);}
 int lintrace(int x)const{return tr[x>>m];}
 int fs(int x,int k)const{for(int i=0;i<k;i++)x=sqe(x);return x;}
};

void fwht(vector<int>& w){
 for(size_t h=1;h<w.size();h*=2)for(size_t i=0;i<w.size();i+=2*h)
  for(size_t j=i;j<i+h;j++){int a=w[j],b=w[j+h];w[j]=a+b;w[j+h]=a-b;}
}

int add_to_basis(int x,vector<int>& b){
 for(int j=int(b.size())-1;j>=0;j--)if((x>>j)&1){
  if(b[j])x^=b[j];else{b[j]=x;return j;}
 }
 return -1;
}

int inverse_on_line(const Fields& F,int c){return F.epow(c,F.N-2);}

void confirm_small_N(const Fields&,const vector<int>&,const vector<int>&,bool);

void spectrum_and_lines(const Fields& F,const vector<int>& x3,const vector<uint8_t>& C,int a){
 int q=F.q,N=F.N,m=F.m;
 const int ai=inverse_on_line(F,a),a3=F.epow(a,3);
 vector<int> w(N),trace_map(N);
 // Direct truth values of the stated F_a, not the image criterion of the proof.
 for(int z:x3){
  int z3=F.em(F.sqe(z),z);
  int y=z^(F.lintrace(F.em(a3,z3))?ai:0);
  w[y]++;
 }
 vector<uint8_t> im(N);
 int image=0;
 for(int v=0;v<N;v++){
  assert(v==0?w[v]==1:w[v]==0||w[v]==3);
  im[v]=w[v]!=0;image+=im[v];
 }
 fwht(w);
 int nb=0;
 assert(w[0]==N);
 for(int u=1;u<N;u++){assert(w[u]==2*q||w[u]==-q);nb+=w[u]==2*q;}
 assert(nb==(N-1)/3&&image==(N+2)/3);
 for(int j=0;j<2*m;j++){
  int b=1<<j,v=0;
  for(int i=0;i<2*m;i++)v|=F.lintrace(F.em(b,1<<i))<<i;
  trace_map[b]=v;
 }
 for(int b=1;b<N;b++)if(!has_single_bit(unsigned(b))){
  unsigned bit=unsigned(b)&(-unsigned(b));
  trace_map[b]=trace_map[b^bit]^trace_map[bit];
 }

 int nlines=0;
 for(int line=-1;line<q;line++){
  int c=line<0?1:q|line,ci=inverse_on_line(F,c);
  bool spectral=true,dual=true;
  for(int t=1;t<q;t++){
   spectral&=w[trace_map[F.em(c,t)]]==2*q;
   dual&=im[F.em(ci,t)]!=0;
  }
  int normalized=F.em(c,ai);
  bool predicted=C[c]&&F.epow(normalized,3)<q;
  assert(spectral==dual&&dual==predicted);
  nlines+=spectral;
 }
 assert(nlines==(m%3?1:C[a]?3:0));
 if(!C[a])assert(w[trace_map[a]]==-q);
 printf("m=%d a=%s: signed spectrum %d nonbent; %d/%d allowed spread lines, direct/dual/analytic agree.\n",
        m,C[a]?"cube":"noncube",nb,nlines,q+1);
 if(m==5)confirm_small_N(F,w,trace_map,C[a]);
}

// Enumerate subspaces by increasing highest-pivot RREF bases; every prefix
// in a permitted subspace must itself be permitted. Used only for m=5.
struct SmallSubspaces{
 const Fields& F;const vector<uint8_t>& permitted;vector<int> pts;
 int target;uint64_t found=0;
 SmallSubspaces(const Fields& f,const vector<uint8_t>& p,int d):F(f),permitted(p),target(d){
  for(int v=1;v<F.N;v++)if(p[v])pts.push_back(v);
 }
 void rec(int pv,int mask,vector<int>& S){
  if((int)S.size()==1<<target){
   ++found;
   int a=inverse_on_line(F,S[1]);
   for(int b:S)assert(F.em(a,b)<F.q);
   return;
  }
  for(int v:pts){
   int p=bit_width(unsigned(v))-1;
   if(p<=pv||(mask&v))continue;
   int n=S.size();bool ok=true;
   for(int i=0;i<n;i++)if(!permitted[S[i]^v]){ok=false;break;}
   if(!ok)continue;
   for(int i=0;i<n;i++)S.push_back(S[i]^v);
   rec(p,mask|(1<<p),S);S.resize(n);
  }
 }
 uint64_t run(){vector<int>S{0};rec(-1,0,S);return found;}
};

void confirm_small_N(const Fields& F,const vector<int>& w,const vector<int>& trace_map,bool cube){
 vector<uint8_t> allowed(F.N);allowed[0]=1;
 for(int b=1;b<F.N;b++)allowed[b]=w[trace_map[b]]==2*F.q;
 auto n=SmallSubspaces(F,allowed,F.m).run();
 assert(n==1);
 printf("m=5 a=%s: exact all-subspace search finds one dimension-5 space, spread-contained.\n",
        cube?"cube":"noncube");
}

// Build the root polynomial using L_{S+<v>}=L_S^2+L_S(v)L_S,
// then independently check the necessary Frobenius span conditions on it.
vector<int> subpoly(const Fields& F,const vector<int>& basis){
 vector<int> L{1};
 for(int x:basis){
  int y=x,z=0;
  for(int c:L){z^=F.em(c,y);y=F.sqe(y);}
  assert(z!=0);
  vector<int> R(L.size()+1);
  for(size_t i=0;i<L.size();i++){R[i]^=F.em(z,L[i]);R[i+1]^=F.sqe(L[i]);}
  L.swap(R);
 }
 return L;
}
vector<int> advance(const Fields& F,const vector<int>& z,const vector<int>& L){
 assert(z.size()+1==L.size()&&L.back()==1);
 vector<int> s(z.size());
 for(size_t i=0;i<z.size();i++){
  int x=F.sqe(z[i]);
  if(i+1<z.size())s[i+1]^=x;
  else for(size_t j=0;j<s.size();j++)s[j]^=F.em(x,L[j]);
 }
 return s;
}
bool even_coordinates_vanish(const vector<int>& v){
 for(size_t j=2;j<v.size();j+=2)if(v[j])return false;
 return true;
}
void cube_subspace_controls(const Fields& F,const vector<uint8_t>& C){
 int m=F.m,q=F.q;
 for(int t:{1,2,3,q-1}){
  vector<int> R(m),basis;
  for(int x=1;x<q;x++)if(F.tr[F.km(t,x)]==0&&add_to_basis(x,R)>=0)basis.push_back(x);
  assert((int)basis.size()==m-1);
  for(int c:{1,2,q|3}){
   vector<int> scaled;
   for(int x:basis)scaled.push_back(F.em(c,x));
   vector<int> L=subpoly(F,scaled), z(L.begin(),L.end()-1), b=advance(F,z,L),d=advance(F,b,L);
   assert(even_coordinates_vanish(b)&&even_coordinates_vanish(d));
   assert(L[m-2]!=0);  // Trace-hyperplane polynomial over a spread line.
   // Rescale the highest non-leading coefficient to 1 by inverse Frobenius.
   int s=F.fs(F.epow(L[m-2],F.N-2),m+2);
   for(int &x:scaled)x=F.em(s,x);
   L=subpoly(F,scaled);
   assert(L[m-2]==1&&L[m-3]==1&&L[0]!=0);
   for(int j=1;j<=(m-3)/2;j++){
    assert(L[2*j]==F.sqe(L[2*j-1]));
    assert(L[2*j-1]==F.sqe(L[2*j-2]));
   }
  }
 }
 // Negative control: a genuinely noncanonical, F4-linear binary (m-1)-space.
 // Its top non-leading coefficient vanishes. It contains 1 and a noncube,
 // and must fail at least one of the proof's two necessary Frobenius tests.
 vector<int> R(2*m),basis;
 int k=0;
 while(C[++k]){}
 auto adjoin=[&](int x){
  vector<int> newR=R;
  int y=F.em(q,x);
  if(add_to_basis(x,newR)<0||add_to_basis(y,newR)<0)return false;
  basis.push_back(x);basis.push_back(y);R.swap(newR);return true;
 };
 assert(adjoin(1));
 if(add_to_basis(k,R)>=0){
  // Rebuild from the actual selected vectors, then append the noncube line.
  R.assign(2*m,0);
  for(int v:basis)add_to_basis(v,R);
  assert(adjoin(k));
 }else{
  R.assign(2*m,0);
  for(int v:basis)add_to_basis(v,R);
 }
 for(int j=1;(int)basis.size()<m-1;j++)adjoin(j);
 vector<int> L=subpoly(F,basis),z(L.begin(),L.end()-1),y=advance(F,z,L);
 assert(L[m-2]==0);
 assert(!even_coordinates_vanish(y)||!even_coordinates_vanish(advance(F,y,L)));
 int toggles=0;
 vector<int> w(q);
 for(int x=0;x<q;x++)w[x]=F.tr[F.kpow(x,3)]?-1:1;
 fwht(w);
 toggles=(q-*max_element(w.begin(),w.end()))/2;
 assert(toggles==q/2-(1<<((m-1)/2))&&toggles>(q-2)/3);
 printf("m=%d: 12 scaled trace hyperplanes, F4-linear counter-control, minimum Gold-shift weight %d.\n",m,toggles);
}

void check_kernel_selectors(const Fields& F,bool switched){
 int q=F.q,m=F.m;
 vector<vector<int>> X(m,vector<int>(m)),Y=X;
 for(int i=0;i<m;i++)for(int j=0;j<m;j++){
  int x=1<<i,y=1<<j;
  X[i][j]=F.km(F.sq[x],y)^F.km(x,F.sq[y]);
  Y[i][j]=F.tr[F.km(F.kpow(x,8),y)^F.km(x,F.kpow(y,8))];
 }
 vector<int> u(q);vector<uint8_t> seen(q);
 for(int t=1;t<q;t++){
  vector<int> row(m),b(m);int rank=0,s=switched?F.tr[t]:0;
  for(int j=0;j<m;j++){
    for(int i=0;i<m;i++)row[j]|=(F.tr[F.km(t,X[j][i])]^(s&Y[j][i]))<<i;
    rank+=add_to_basis(row[j],b)>=0;
  }
  assert(rank==m-1);
  for(int j=0;j<m;j++)if(!b[j])u[t]=1<<j;
  for(int j=0;j<m;j++)if(popcount(unsigned(b[j]&u[t]))&1)u[t]^=1<<j;
  for(int r:row)assert((popcount(unsigned(r&u[t]))&1)==0);
  assert(u[t]&&!seen[u[t]]);seen[u[t]]=1;

  // Independent closed form for the inverse kernel coordinate. This is a
  // regression check, not an input to the alternating-minor proof.
  int v=u[t],vi3=F.kpow(v,q-4),h=switched?F.tr[vi3]:0;
  int z=F.kpow(v,9),r=z^F.kpow(z,q/2)^F.kpow(z,q/4);
  int pred=F.km(vi3,h?r:1);
  assert(pred==t);
 }
 vector<int> anf=u;
 for(int i=1;i<q;i*=2)for(int t=0;t<q;t++)if(t&i)anf[t]^=anf[t^i];
 int degree=0;
 for(int t=0;t<q;t++)if(anf[t])degree=max(degree,popcount(unsigned(t)));
 assert(degree<=(m-1)/2);
 auto moments=[&](const vector<int>& v){
  vector<int> out(m);
  for(int t=1;t<q;t++)for(int i=0;i<m;i++)if((t>>i)&1)out[i]^=v[t];
  return out;
 };
 auto M=moments(u);for(int a:M)assert(a==0);
 u[1]^=1;M=moments(u);assert(M[0]==1);
 printf("m=%d %s kernel selector: degree %d, all bilinear parity moments zero, mutation rejected.\n",m,
        switched?"switched":"Gold",degree);
}

int main(){
 const int ms[]={5,7,9,11},polys[]={0x25,0x83,0x211,0x805};
 for(int p=0;p<4;p++){
  Fields F(ms[p],polys[p]);
  vector<int> cube(F.N);vector<uint8_t>C(F.N);C[0]=1;
  for(int x=0;x<F.N;x++){cube[x]=F.em(F.sqe(x),x);C[cube[x]]=1;}
  assert(count(C.begin(),C.end(),uint8_t(1))==(F.N+2)/3);
  for(int x=1;x<F.q;x++)assert(C[x]);
  int a=1;while(C[a])a++;
  spectrum_and_lines(F,cube,C,1);
  spectrum_and_lines(F,cube,C,a);
  if(F.m==5){
   auto h=SmallSubspaces(F,C,4).run(),s=SmallSubspaces(F,C,5).run();
   assert(h==341&&s==11);
   printf("m=5 independent all-cube subspace enumeration: %llu dimension-4; %llu dimension-5, all spread-contained.\n",
          (unsigned long long)h,(unsigned long long)s);
  }
  cube_subspace_controls(F,C);
  check_kernel_selectors(F,false);
  check_kernel_selectors(F,true);
 }
 puts("PASS all exact finite-field regressions and negative controls.");
}
