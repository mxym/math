#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstdio>
#include <vector>
#include <cstdlib>
#include <limits>
#include <cfenv>
using namespace std;
struct I { double l,r; I(double a=0):l(a),r(a){} I(double a,double b):l(a),r(b){} double ab()const{return max(abs(l),abs(r));} };
double dw(double x){return x-(abs(x)*2e-15+1e-20);}
double up(double x){return x+(abs(x)*2e-15+1e-20);}
I box(double a,double b){return I(dw(a),up(b));}
I operator + (I a,I b){return box(a.l+b.l,a.r+b.r);}
I operator - (I a,I b){return box(a.l-b.r,a.r-b.l);}
I operator * (I a,I b){ double x=a.l*b.l,y=a.l*b.r,z=a.r*b.l,w=a.r*b.r;return box(min({x,y,z,w}),max({x,y,z,w})); }
I operator / (I a,I b){assert(b.l>0);return a*box(1/b.r,1/b.l);}
I neg(I a){return I(-a.r,-a.l);}
I sq(I a){return box(a.l<=0&&a.r>=0 ? 0 : min(a.l*a.l,a.r*a.r), max(a.l*a.l,a.r*a.r));}
I fplus(I a){return I(max(0.,a.l),max(0.,a.r));}
const int P=10000;
const I HALF=I(.5);
int A;
I af;
I bf[2][P+10]; // 0 plus, 1 minus
I pref[2][P+10], pf[2][P+10]; // interval of prefix integral at cell starts
I at0;
I densities[2][15][P+10], profile[15][P+10];
int lg[P+20];
void sparse(I (&x)[15][P+10],int end){
 for(int j=1;(1<<j)<=end+1;j++)
  for(int i=0;i+(1<<j)<=end+1;i++){
    I A=x[j-1][i], B=x[j-1][i+(1<<(j-1))];
    x[j][i]=I(min(A.l,B.l),max(A.r,B.r));
  }
}
I range(I (&x)[15][P+10],int l,int r){
 int k=lg[r-l+1]; I a=x[k][l], b=x[k][r-(1<<k)+1];
 return I(min(a.l,b.l),max(a.r,b.r));
}
void prep_b(int a){
 A=a;af=I(A)/P;
 for(int i=2;i<=P+10;i++)lg[i]=lg[i/2]+1;
 for(int id=0;id<=1;id++) for(int i=0;i<=P+2;i++) bf[id][i]=pref[id][i]=0;
 for(int id=0;id<=1;id++){
  I sign = id==0 ? I(1):-1;
  for(int i=A;i<=P+1;i++){
   I x=I(i,i+1)/P, br=I(0);
   if(i>=2*A){
    int j=i-A;
    br=I(pref[id][j].l,pref[id][j+1].r);
    if(id==1)br=I(pref[id][j+1].l,pref[id][j].r);
   }
   bf[id][i]=sign*(I(1)+br)/x;
   if(id==1) bf[id][i].r=min(0.0,bf[id][i].r); // Dickman
   pref[id][i+1]=pref[id][i]+bf[id][i]/P;
  }
  for(int i=0;i<=P+1;i++){
   if(!id)pf[id][i] = I(max(0.,bf[id][i].l),bf[id][i].r);
   else pf[id][i] = neg(bf[id][i]);
  }
  for(int i=0;i<=P+1;i++)densities[id][0][i]=pf[id][i];
  sparse(densities[id],P+1);
 }
}
I fdd(I z){
 // h from .5-z, clipped. F''=528x-3360x^2; vertex at 11/140.
 I x=sq(fplus(HALF-z));
 I cl=I(11)/140, xx1=I(x.l),xx2=I(x.r), p1=xx1*(528-3360*xx1), p2=xx2*(528-3360*xx2);
 double top=max(p1.r,p2.r);
 if(x.l<=cl.r && x.r>=cl.l) top=max(top,(cl*(528-3360*cl)).r);
 return I(min(p1.l,p2.l),top);
}
I fp(I z){
 I h=fplus(HALF-z), q=sq(h);return h*q*(176-672*q);
}
I g1(I t,I x){
 // center plus mean-value error for -F', avoid cancellation of F-values.
 I hc=x+t/2; double cm=(hc.l+hc.r)/2;
 I v=fp(cm);
 // first-order term in uniform variable has mean zero about hc.
 // max |F'''| <= 2400 globally, outer variation about exact fixed center by local F''.
 I err=(I(.5)*I(2400)*sq(t)/12);
 double widen=(I(fdd(hc).ab())*I(up(max(cm-hc.l,hc.r-cm)))+err).r;
 return I(dw(v.l-widen),up(v.r+widen));
}
I g2(I u,I v,I x){
 I T=u+v, h=fplus(HALF-(x+T/2)), c=sq(h);
 if ((x+T).r > .5) return fdd(I(x.l,(x+T).r));
 I var=(sq(u)+sq(v))/12;
 I fourth=(sq(sq(u))+sq(sq(v)))/80+sq(u)*sq(v)/24;
 return fdd(x+T/2)+var*(528-20160*c)-3360*fourth;
}
int idxlo(double x){return max(A,min(P,int(dw(P*x))));}
int idxhi(double x){return max(A,min(P,int(up(P*x))));}
I rr(int mode,I t){
 if(t.r<0 || t.l>1.001)abort();
 int x=idxlo(t.l),y=idxhi(t.r);
 return range(densities[mode],x,y);
}
I gg(int mode, I x){
 int l=max(0,min(P,int(dw(P*x.l)))),h=max(0,min(P,int(up(P*x.r))));
 if(l>=P/2)return 0;
 return range(profile,l,min(h,P/2));
}
I integral(int n,const int* codes,int mode,I T,I tag1,I tag2,int d,int divs,int kind){
 if(n==0 || T.r<(I(n)*af).l)return 0;
 I spanT=T-n*af;
 spanT.l=max(0.,spanT.l);
 I sum=0;
 int m=n-1;
 auto term=[&](array<int,3> iy,int repeat){
   I g[4]={0,0,0,0};
   I fac=1;
   int ix[5]={0,0,0,0,0}; for(int j=0;j<m;j++)ix[j+1]=iy[j];ix[n]=divs;
   for(int j=0;j<n;j++){
    // ordered boundary last=1, first=0. Others inside their cells.
    int i1=ix[j],i2=ix[j+1];
    I gap=I(max(0,i2-i1-(j>0)),min(divs,i2-i1+(j<m)))/divs;
    I ang=af+spanT*gap;
    fac=fac*(kind==3 ? I(1)/ang:rr(codes[j]==1||codes[j]==2,ang));
    g[codes[j]]=ang;
   }
   auto value=[&](int id) {
    if(g[id].r==0 && g[3].r==0)return at0 + d;
    int lower=0,upper=0,ns=0;
    for(int j=0;j<n;j++)if(codes[j]==3||codes[j]==id)ns++;
    if(codes[n-1]==3||codes[n-1]==id)lower=upper=divs;
    for(int j=1;j<n;j++){
     int v=(codes[j-1]==3||codes[j-1]==id)-(codes[j]==3||codes[j]==id);
     lower+=v==1?ix[j]:v==-1?-(ix[j]+1):0;
     upper+=v==1?ix[j]+1:v==-1?-ix[j]:0;
    }
    I x=ns*af+spanT*(I(max(0,lower),min(divs,upper))/divs);
    return gg(mode,x);
   };
   if(kind==1) return (fac*value(1))/repeat;
   if(kind==2) return (fac*value(1)*value(2))/repeat;
   if(kind==3){ // A positive on true quotient rank 2, so use coordinate slots 1,2
     I ret=fplus(at0-gg(0,g[1])-gg(0,g[2]));
     return fac*ret/repeat;
   }
   abort();
 };
 // local indexed dyads, repeats correction = factorial within equal grid bins
 if(m==0)sum=term({0,0,0},1);
 if(m==1)for(int i=0;i<divs;i++)sum=sum+term({i,0,0},1);
 if(m==2)for(int i=0;i<divs;i++)for(int j=i;j<divs;j++)sum=sum+term({i,j,0},i==j?2:1);
 if(m==3)for(int i=0;i<divs;i++)for(int j=i;j<divs;j++)for(int k=j;k<divs;k++)
  sum=sum+term({i,j,k},i==k?6:(i==j||j==k?2:1));
 I factor=1; for(int i=0;i<m;i++)factor=factor*spanT/divs;
 I out=factor*sum;
 if(kind<=2) {
    int c=0;for(int i=0;i<n;i++)c+=(codes[i]==1||codes[i]==2);
    if(c%2)out=neg(out);
 }
 return out;
}
void prep_g(int mode,I t,I u) {
 at0=(mode==0 ? g1(t,0):g2(t,u,0));
 for(int i=0;i<=P/2;i++) {
  I x=I(i,i+1)/P; profile[0][i] = (mode==0 ? g1(t,x) :g2(t,u,x));
 }
 profile[0][P/2].l=min(profile[0][P/2].l,0.); profile[0][P/2].r=max(profile[0][P/2].r,0.);
 sparse(profile,P/2);
}
I mean(int mode,I t,I u,int divs){
 I T=I(1)-t-u,V=0;
 for(int bits:{1,2,3}){
  int codes[2],c=0;
  if(bits&1)codes[c++]=0;
  if(bits&2)codes[c++]=1;
  V=V+integral(c,codes,mode,T,t,u,0,divs,1);
 }
 return V;
}
I mean2(int mode,I t,I u,int d,int divs){
 I T=I(1)-t-u,V=0;
 for(int bits=1;bits<16;bits++){
  int codes[4],c=0;
  for(int i=0;i<4;i++)if(bits&(1<<i))codes[c++]=i;
  V=V+integral(c,codes,mode,T,t,u,d,divs,2);
 }
 return V;
}

long long fac(int r){long long v=1;for(int j=2;j<=r;j++)v*=j;return v;}
I powI(I v,int r){I w=1;for(int j=0;j<r;j++)w=w*v;return w;}
I positive(I t,int divs){
  I T=1-t,D=at0/T;
  int codes[2]={1,2};
  D=D+integral(2,codes,0,T,t,0,0,divs,3)/2;
  for(int j=9;j<=15;j+=2){ // even ranks above six are zero; q=8+ tails if live.
    int q=j-1;
    if(T.r<=(I(q)*af).l)continue;
    I V=fplus(T-q*af);
    I amp=1056*I(1<<(j-5))*powI(T/q,3)+80640*I(1<<(j-7))*powI(T/q,5);
    // factor must contain actual smallest tag; the other least mean is <= T/q.
    D=D+powI(V,q-1)*amp/powI(af,q)/I(fac(q))/I(fac(q-1));
  }
  return D;
}
void sieve_constants(){
 I low=0;
 for(int j=0;j<6;j++)low=low+I(2)*powI(I(.5),2*j+1)/(2*j+1);
 if(low.l<= (I(1098)/1000).r)abort();
 I U=0;
 for(int i=1;i<=128;i++){
  I t=I(i)/128,y=t/(2+t), val=0;
  for(int j=0;j<5;j++)val=val+2*powI(y,2*j+1)/(2*j+1);
  val=val+2*powI(y,11)/(11*(1-sq(y)));
  U=U+val/((2+t)*128);
 }
 if(((1+U)/2).r>=(I(575)/1000).l)abort();
}
int main(){
 static_assert(numeric_limits<double>::is_iec559);
 if(fesetround(FE_TONEAREST))abort();
 sieve_constants();
 const int ns=256, dt=10, dq=20;
 const int thi=260;
 struct L {int tl; I mean,sq,pos;I a;};
 vector<L> LL;
 for(int t=30;t<thi;t+=dt){
  int A=t<60?800:1080;
  prep_b(A); I l=I(t,min(t+dt,thi))/P;
  prep_g(0,l,0);
  LL.push_back({t,mean(0,l,0,ns),mean2(0,l,0,0,ns),positive(l,ns),af});
  printf("L %d mean %.6f sq %.6f pos %.6f\n",t,LL.back().mean.r,LL.back().sq.r,LL.back().pos.r); fflush(stdout);
 }
 prep_b(800);
 I A0=af,vol=0,credit=0;
 int good=0,seen=0;
 for(int i=60;i+2*dq<=800;i+=dq) for(int j=i+dq;j+dq<=800;j+=dq){
  if(i+j<=650 || i+j+2*dq>=1560)continue;
  I u=I(i,i+dq)/P,v=I(j,j+dq)/P;
  prep_g(1,u,v);
  int d=(990000-380*(i+j+dq))/10000;
  I bs=mean2(1,u,v,d,ns);
  double lmin=1e10,lmax=-1e10;
  int ncurr=0;
  for(auto &L:LL){
    I k=(I(549)/1000)/A0, U=(I(575)/1000)/A0, Ul=(I(575)/1000)/L.a;
    I left=I(d)*(neg(k*L.mean)-(U-k)*L.pos);
    I crit=(U*Ul*L.sq*bs);
    if(crit.r<0) abort();
    const double cap=up(up(sqrt(crit.r)));
    if((I(cap)*I(cap)).l<crit.r) abort();
    I val=left-I(0,cap);
    lmin=min(lmin,val.l);lmax=max(lmax,val.l);seen++;
    if(val.l>10){
       I w=I(min(thi,L.tl+dt)-L.tl)*I(dq)*I(dq)/I((double)P*P*P);
       vol=vol+w;credit=credit+w*I(val.l);good++;ncurr++;
    }
  }
  printf("R %d %d d %d b² %.6f lower %.3f .. %.3f new %d total %.9f\n",i,j,d,bs.r,lmin,lmax,ncurr,credit.l); fflush(stdout);
 }
 printf("TOTAL %d/%d V %.12g credit one %.12g both %.12g\n",good,seen,vol.l,credit.l,(I(2)*credit).l);
 if(good!=4465||seen!=11086||(I(2)*credit).l<=(I(357971)/10000000).r)abort();
}
