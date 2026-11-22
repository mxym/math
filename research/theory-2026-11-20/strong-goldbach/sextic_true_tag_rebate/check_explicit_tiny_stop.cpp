#include <bits/stdc++.h>
using namespace std;
using U=__uint128_t;using W=uint64_t;
const W M=256, S=1000000000000ULL, SN=1000, JMAX=40; // t grid 1000, angular bins M
const int cap=1152; // κ=9/2
template<class A> A sumcheck(A a,A b){if(a+b<a)throw 1;return a+b;}
W ceilq(U a,U b){ if(a==0)return 0; U q=1+(a-1)/b; if(q>numeric_limits<W>::max())throw 1; return (W)q;}
W powexp(W w){ // exp(w/S) for w<=S by recurrence, with explicit eventual geometric
 W den=S;W term=S,sum=S;
 for(W i=1;i<=22;i++){term=ceilq((U)term*w,(U)i*S);sum=sumcheck(sum,term);}
 return sumcheck(sum,ceilq((U)term*w,(U)23*S-w));
}
W sqrtdn(U x){W r=sqrtl((long double)x);while((U)r*r>x)--r;while((U)(r+1)*(r+1)<=x)++r;return r;}
W Xbeta_bnd(W i,W t){ // integral in angular bin of min(t x,2)^2 / x^{5/2}, ∫ sqrt floor/ceil
 // x upper as f; integral ≤ local near-zero formula if bin fully below split, else use max
 const W PS=10000000000ULL;
 if(i==0) return ceilq((U)2*t*t*S,SN*SN*16);
 // bound by (upper integral of squared phase / x) times (M/i)^{3/2}
 W xi1=ceilq((U)M*PS,i);
 W sqrtUp=sqrtdn((U)xi1*PS)+1;
 W p=0;
 if((U)t*(i+1)<=2ULL*SN*M) p=ceilq((U)t*t*(i+1)*S,(U)SN*SN*M*M);
 else if((U)t*i>=2ULL*SN*M) p=ceilq((U)4*S,i);
 else p=ceilq((U)2*t*S,SN*M);
 return ceilq((U)p*xi1*sqrtUp,(U)PS*PS);
}
pair<W,W> cert(W t,int k){
 vector<W> poly(cap+1), next(cap+1),w(M);poly[0]=S;
 W total=0;U out=0;
 for(W i=0;i<M;i++){
  if(k==1)w[i]= min(ceilq((U)t*S,SN*M), i?ceilq((U)2*S,i):UINT64_MAX);
  else{
   if((U)t*(i+1)<=2ULL*SN*M) w[i]=ceilq((U)t*t*(i+1)*S,(U)SN*SN*M*M);
   else if((U)t*i>=2ULL*SN*M) w[i]=ceilq((U)4*S,i);
   else w[i]=ceilq((U)2*t*S,SN*M);
  }
  total=sumcheck(total,w[i]);
 }
 W expW=S;
 // exp(total/S) upper: exp(unit part) repeatedly; scaled arithmetic.
 for(int j=0;j<total/S;++j) expW=ceilq((U)expW*powexp(S),S);
 expW=ceilq((U)expW*powexp(total%S),S);
 W tail=S;
 for(int j=1;j<=JMAX+1;++j)tail=ceilq((U)tail*total,(U)j*S);
 tail=ceilq((U)tail*expW,S);
 for(int i=M-1;i>=0;i--){
  W outer=(k==1)?w[i]:Xbeta_bnd(i,t);
  W known=0; // physical t<=κ and >=κ-x0-(j/M), with j≤JMAX
  if(i>0){
   next=poly;W c=S;
   for(int j=1;j*i<=cap;++j){
    c=ceilq((U)c*w[i],(U)j*S); // tiny high-degree terms safe, merged into positive bound
    for(int s=0;s+j*i<=cap;++s) if(poly[s])next[s+j*i]=sumcheck(next[s+j*i],ceilq((U)poly[s]*c,S));
   }
   poly.swap(next);
   W b=min<W>(JMAX, cap/i);
   for(int s=max(0,cap-i-1-(int)b);s<=cap;++s)known=sumcheck(known,poly[s]); // conservative equality
   if((W)cap/i>JMAX) known=sumcheck(known,tail);
  }else{
   W b=JMAX;
   for(int s=cap-1-(int)b;s<=cap;++s)known=sumcheck(known,poly[s]);
   known=sumcheck(ceilq((U)known*powexp(w[i]),S),tail);
  }
  out=sumcheck(out,(U)known*outer);
 }
 return {ceilq(out,S*10000ULL),total};
}
int main(){
 vector<W> T{0};
 for(W j=150;j<=10000;j+=150)T.push_back(j);
 for(W j=10500;j<=18000;j+=500)T.push_back(j);
 for(W j=19000;j<=40000;j+=1000)T.push_back(j);
 for(W i=1;i<T.size();++i){
   auto [r,u]=cert(T[i],1);auto[v,a]=cert(T[i],2);
   cout<<T[i-1]<<" "<<T[i]<<" "<<r<<" "<<v<<" "<<u<<" "<<a<<"\n";
 }
}
