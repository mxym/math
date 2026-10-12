# Parent research: centered compound-Poisson moment (internal)

Status: auxiliary analytic lemma, not real-rootedness or completion of the conjecture.
Source definitions: de Castro, arXiv:2609.06096v1, Sections 8–9.

Fix 0<x<=15. Write R=1/lambda(x), p=x/(1+x),
nu=integral_0^1 xt/(2+(x-1)t) dt, q=(1+x)R<1.
Let v_a=(1+x)P_a(x)R^a. The nonnegative logarithmic
majorant B has components indexed by (a,h), with dimension s=ha,
weight w_(a,h)=v_a phi(h)/h^2 q^((h-1)a), and degree distributed as
K=X_(a,x)+Binomial((h-1)a+1,p), independently.
All these statements follow exactly from the factorization of P_a and B.

Put D=K-ha nu. Since f(t)=xt/(2+(x-1)t) is increasing,
0<=a nu-mu_a<=p (also for a=1). Thus
0<=E D<=p+(h-1)a(p-nu),
and Var(D)<=mu_a+((h-1)a+1)p<=ha p, since mu_a<=(a-1)p.
Consequently:
 h=1: E D^2<=a p+p^2;
 h>=2: E D^2<=ha p+(ha)^2 p^2.

Let beta=sum w, M1=sum w E D, M2=sum w E D^2.
The first moment bound in the source, sum ha w<11, gives
0<=M1<11p.
The primitive weights have sum < (6/5)sum a^(-5/2)<9/5.
For the periodic second dimension moment, using phi(h)<=h,
 sum_(a,h>=2) (ha)^2 w
 <= sum_a a^2 v_a ((1-q^a)^(-2)-1)
 <= (12/5)/(1-q)^2 sum_a a^(-1/2)q^a
 <= (12/5)q/(1-q)^3 <=240,
where q<=4/5 and v_a< (6/5)a^(-5/2).
Hence M2<11p+242p^2.

For H_major=exp B, let c_(s,k)>=0 be its coefficient weighted by R^s x^k.
The compound-Poisson exponential formula, justified first for finite component
truncations and then by monotone convergence of nonnegative second moments,
gives exactly
 sum_(s,k) c_(s,k)(k-s nu)^2 = exp(beta)(M2+M1^2).
With beta<5/2 and exp(beta)<16 this is less than
16(11p+363p^2).

This proves a uniform finite centered second moment despite the divergent
uncentered second dimension moment of the primitive distribution. It does
not yet provide the required relative local probability comparison or bound
the large-component contribution to the marked identity. Those two steps,
with constants strong enough to cover the entire finite gap, remain open.
