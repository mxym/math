# Parent lemma: degree smoothing in the positive correction majorant

Internal, not a completed conjecture proof. Retain the notation in the other
parent notes. Let Hhat_s(x)=[u^s]exp(B(u,x)), normalized by R^s, and let
hhat_s be its total nonnegative coefficient mass at z=x.
Set v*=p(1-p)=x/(1+x)^2 and c(x)=min(2/3,(1+x)^2/6).

Each logarithmic component (a,h), dimension n=ha, has degree distribution
X_a+Binomial((h-1)a+1,p). Its Bernoulli variance integrand is
 g(t)=x t(2-t)/[2+(x-1)t]^2.
For x>=1, g(t)>=v* t(2-t); for 0<x<=1,
 g(t)>=(1+x)^2 v* t(2-t)/4.
Include the FIRST extra Bernoulli as the endpoint t=1. Then
 sum_(q=1)^a (q/a)(2-q/a) = (a+1)(4a-1)/(6a)>=2a/3.
Consequently Var(X_a)+v*>=c(x)a v*. The other (h-1)a extra
Bernoulli variables yield variance at least c(x)ha v*, because c(x)<=1.

Correction during parent self-review: the earlier scratch integrand 2xt/den^2
was incorrect; the factor is xt(2-t). The c(x) constants above and all
subsequent scalar certificates must use the corrected factor 2/3.

A fixed composition of logarithmic components of total dimension s likewise
has an independent Bernoulli degree sum of variance at least c(x)s v*.
The degree distribution of Hhat_s is a positive mixture of these laws.
Fourier inversion and the Gaussian bound on Bernoulli characteristic functions
give for any PB law of variance V>0:
 max_j Pr(X=j) <= sqrt(pi)/(2sqrt(2V)).
It follows that every normalized degree coefficient of the s-th positive
majorant is at most
 hhat_s * sqrt(pi)/(2sqrt(2 c(x) s v*)).
The same bound holds after convolution with any normalized nonnegative
polynomial, since taking a weighted average cannot increase the maximal atom.

This supplies the missing s^(-1/2) in a large-s convolution bound. In the
marked identity, combining hhat_s=O(s^(-5/2)), n/d, the primitive d^(-5/2)
scale, and the mode denominator of order d^(-1/2), produces O(d^(-1)) instead
of the source's O(d^(-1/2)). Uniform x->0 constants must still be combined
with the x-dependent mode bound (v* also tends to zero); no singular uniform
bound is asserted here.

## Pointwise heavy-tail coefficient refinement to investigate

If b_n=[u^n]B(Ru,x)<=B n^(-5/2), mass beta and first moment beta1 are known,
and h_j<=C j^(-5/2) is already established for the relevant earlier indices,
the recurrence s h_s=sum n b_n h_(s-n), split at n=s/2, gives
 h_s <= s^(-5/2) [ (6 beta1/s)C
                         + B exp(beta)(1+9 beta1/s) ].
For the first part use (1-n/s)^(-5/2)<=2^(5/2)<6.
For the second set j=s-n and use (1-j/s)^(-3/2)<=1+9j/s on [0,1/2],
then sum h_j<=exp(beta), sum j h_j=exp(beta)beta1.
This is a conditional induction bound, NOT an unconditional optimized C.
A valid base range and a rigorous uniform bound B (or a split primitive and
periodic bound) are still required before it can be used numerically.
