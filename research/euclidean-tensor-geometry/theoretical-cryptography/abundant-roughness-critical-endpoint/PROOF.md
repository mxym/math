# Squarefree abundant numbers at the critical roughness constant

All logarithms are natural. For an integer n>1 let p_min(n) denote its least prime divisor, and call n abundant if sigma(n)>2n.

**Theorem.** For every fixed real A>0, there are infinitely many squarefree abundant integers n of the form product of all primes from p through q, inclusive, with
```
log n <= p^2 - A p^(3/2),       p = p_min(n).
```
In particular there are infinitely many squarefree abundant n with p_min(n)>sqrt(log n). No assumption on zeta zeros is made.

The only inputs about the primes are the prime number theorem in its usual Chebyshev-theta form, Mertens' product asymptotic, and the unconditional negative oscillation of Diamond and Pintz (2009), Theorem 1.1 or its logarithmic form (2.1). We first construct a bound that any counterexample to the asserted infinitude would impose on a continuously interpolated prime product.

## 1. The interpolation

Write theta(x)=sum_{p<=x} log p, M(x)=product_{p<=x}(1-1/p)^(-1), and theta(p-)=sum_{r<p} log r. For y>=0 define the continuous function S by
```
S(theta(p)) = log M(p),
S(0) = 0,
```
and linear interpolation between these consecutive knots. In the open segment theta(p-)<y<theta(p), its slope is
```
r(p) = -log(1-1/p)/log p.
```
The function S is increasing. The slopes r(p) strictly decrease with p, since the numerator strictly decreases and the positive denominator increases. Either adjacent endpoint may be used to bound S at a knot. Define
```
f(u) = S(exp u) - gamma - log u                 (u>0).
```
Uniformly as y tends to infinity, the prime p of the segment containing y (either adjacent prime if y is a knot) satisfies p/y -> 1. Indeed, theta(p)=p(1+o(1)) and theta(p-)=theta(p)-log p also equals p(1+o(1)). Mertens' product asymptotic at the two adjacent knots and interpolation therefore give f(u)->0. At every nonknot,
```
f'(u) = (exp u) r(p) - 1/u = o(1/u)
```
uniformly as u tends to infinity. This follows from r(p)=(1+O(1/p))/(p log p) and p/exp u ->1; no rate for this last limit is needed. The function f is locally absolutely continuous, since every compact u-interval has finitely many knots and smooth pieces. At each knot its derivative has a strictly downward jump. These statements use the ordinary prime number theorem, not a bound of power-saving strength.

## 2. The budget inequality

Suppose, to the contrary, that only finitely many of the integers in the theorem are abundant. For every sufficiently large prime p, put
```
B_p = theta(p-) + p^2 - A p^(3/2).
```
Take q to be the last prime with theta(q)<=B_p, which is at least p for all large p. The squarefree product n_p over p<=r<=q then satisfies the required budget. Its least prime p tends to infinity, so n_p is nonabundant for all large p under the contrary supposition. Using its squarefree Euler factors,
```
log(sigma(n_p)/n_p)
 = S(theta(q))-S(theta(p-)) + sum_{p<=r<=q} log(1-1/r^2)
 <= log 2.
```
The absolute value of the final sum is O(1/p), by comparison with the convergent integer square tail. The fractional unused segment from theta(q) to B_p adds at most the next prime's log Euler factor, O(1/p^2), because B_p is asymptotic to p^2 and the segment prime there is asymptotic to B_p. Thus
```
S(B_p)-S(theta(p-)) <= log 2 + O(1/p).
```
For the endpoint alone one could instead take the budget p^2-1; in that case B_p>=p^2 for large p, and monotonicity gives the sharper O(1/p) error in (1). For the quantitative statement with fixed A>0, both B_p and p^2 are asymptotic to p^2. On the interval between them, the segment primes are uniformly asymptotic to p^2, and the slopes are O(1/(p^2 log p)). Since |B_p-p^2|=O_A(p^(3/2)), it follows that there is a constant K_A such that for all sufficiently large primes p,
```
S(p^2)-S(theta(p-)) <= log 2 + K_A/(sqrt(p) log p).   (1)
```
In particular, if exp u is in the segment of p then S(exp u)>=S(theta(p-)), so substituting the definition of f yields
```
f(2 log p)-f(u) <= -log((log p)/u) + K_A/(sqrt(p) log p).  (2)
```
The notation here is log of the ratio (log p)/u, not a ratio of logs.

## 3. A maximum argument for the interpolated error

We prove from (2) that
```
f(u) >= -C exp(-lambda u) for all sufficiently large u,    (3)
```
where lambda is any fixed number with 1/4<lambda<1/2 and C may depend on A and lambda. For example lambda=1/3 suffices.

Take an arbitrary C>=1 for the estimates below. Consider an interior positive global maximum at v of
```
g(u) = -f(u) - C exp(-lambda u)
```
on an interval [u0,infinity), and write z=C exp(-lambda v). Its positivity gives 0<z<-f(v)=o(1), uniformly as v tends to infinity. Such a maximum cannot be at a knot: the one-sided derivatives of g have a strictly upward jump, whereas a local maximum requires the left derivative nonnegative and the right derivative nonpositive. Thus v belongs to a unique open segment of p and
```
f'(v) = lambda z.
```
In particular v z=o(1) uniformly at these contact points, by the derivative estimate from section 1. Let delta=v-log p. The prime number theorem gives delta=o(1). The exact derivative formula and the estimate for r(p) give
```
v lambda z = exp(delta) * v/(v-delta) * (1+O(1/p)) - 1
           = (1+1/v) delta + O(delta^2+1/p).           (4)
```
For sufficiently large v we can absorb O(delta^2) into the linear term, so |delta|=O(vz+1/p). Dividing (4) by v, using delta=o(1), gives
```
-log((log p)/v) = -log(1-delta/v)
                = delta/v + O(delta^2/v^2)
                = lambda z + o(z).
```
Indeed the discarded terms are bounded by expressions of order |delta|/v^2, delta^2/v and 1/(vp); the first two are o(z) using |delta|=O(vz+1/p) and delta=o(1), and 1/(vp)=o(z) since p is asymptotic to exp v and C>=1. Every small-o bound in this argument is uniform at such contact points in C>=1. By the uniform derivative bound from section 1 and local absolute continuity,
```
|f(2 log p)-f(2v)| <= 2 |delta| * o(1/v) = o(z).
```
This estimate does not ask for an exponential error in the prime number theorem. It uses the improved small displacement at the maximum. Also K_A/(sqrt(p) log p)=o(z), since lambda<1/2. Consequently (2) gives
```
f(2v)-f(v) <= (lambda+o(1)) z.
```
But 2v also belongs to [u0,infinity); maximality gives
```
f(2v)-f(v) >= C(exp(-lambda v)-exp(-2 lambda v))
             = (1-exp(-lambda v)) z.
```
For all sufficiently large v these inequalities conflict. The threshold can be chosen independent of C>=1 by the uniform estimates. Now choose u0 beyond it and take C>=1 with g(u0)<=0. If g is positive anywhere after u0, its continuity and limit zero at infinity give a positive global maximum, attained at some interior v. The contradiction shows g<=0 and proves (3).

## 4. Unconditional negative oscillation

Return to (1). Evaluating (3) at 2 log p gives, for every large prime p,
```
log M(p-) = S(theta(p-))
 >= gamma + log log p - C p^(-2 lambda) - K_A/(sqrt(p) log p)
 >= gamma + log log p - K'_A/(sqrt(p) log p),           (5)
```
for a fixed constant K'_A, because 2 lambda>1/2.

In Diamond and Pintz, *Oscillation of Mertens' product formula*, J. Théor. Nombres Bordeaux 21 (2009), printed p. 524, Theorem 1.1, the quantity sqrt(x)(M(x)-exp(gamma)log x) is unbounded negatively for x tending to infinity. Their equation (2.1) equivalently says that for any fixed H>0 there are arbitrarily large real x with
```
log M(x) - gamma - log log x < -H/(sqrt(x) log x).
```
For each such x take p to be the next prime strictly greater than x. Then M(p-)=M(x), including if x is a prime, and log log p>=log log x. Also sqrt(p)log p>=sqrt(x)log x. Thus this gives arbitrarily large p with
```
log M(p-) < gamma + log log p - H/(sqrt(p) log p),
```
contradicting (5) for H>K'_A. This finishes the proof. In particular, there are infinitely many qualifying consecutive prime products, not merely abundant numbers allowing arbitrary multiplicities.

For context, the theorem settles the existence endpoint in the last sentence of section 5.2 of Shunia (arXiv:2611.34242v1). It does not show that the abundance-oracle restriction of Theorem 5.2 there can itself be made at c=1, and it gives no efficient bound on the first witness. Existence, effective search cost and oracle-query construction are distinct claims.
