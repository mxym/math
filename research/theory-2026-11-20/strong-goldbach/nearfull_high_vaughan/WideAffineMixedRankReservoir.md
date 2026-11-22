# A conditional true high-semiprime versus higher-rank negative sector

Use the fixed even target \(N\), \(L=\log N\), and a fixed
nondegenerate interval \(J\subset[1/2,2/3]\) as in
[the whole mark transfer](WholeMarkPrimeTransfer.md). Put
\(x\in NJ\), \(y=N-x\), \(M_N=|J|N\mathfrak S(N)\).
All rows are target units. Let
\[
 R_J(N)=\sum_{\substack{x\in NJ\\(x,N)=1}}\Pi(x)\Pi(N-x),
 \qquad \Pi(v)=1_{v\ {\rm prime}}\log v.
\]
Fix \(\rho=.518\). There exist fixed \(0<\lambda\le .006\),
\(\eta>0\), and a finite integer \(R\), depending only on
\(J\) and the fixed smooth cutoff used below, with the
following property.

At every sufficiently large even \(N\) satisfying
\[
                         R_J(N)\le .01 M_N,                         \tag{1}
\]
there are \(\gg_{J,\lambda,\eta,R} M_N/L^2\) distinct true
rows \(x+y=N\), with:
* \(x=m r\) an actual squarefree semiprime, \(r>N^\rho\) and
  \(m,r\) literal primes;
* \(y\) squarefree, \(3\le\omega(y)\le R\), and \(P^-(y)>N^\eta\);
* the actual wide affine composite mark \(P_\lambda(y)\) defined
  below strictly negative.

The weighted magnitude of these rows is at least a fixed
positive multiple of \(M_N\). This is a conditional genuine
negative mixed-rank sector, not a lower bound for the total
low–low covariance or a conclusion about \(R_J\).

## 1. A forced mixed sign in the actual wide affine score

Take a fixed smooth cutoff \(C\), equal to \(1\) on
\([0,.486]\), zero on \([.490,\infty)\), and \(0\le C\le1\).
For \(0<\lambda\le.006\) let
\[
    F_\lambda(t)=(1+t/(1-\lambda))C(t).
\]
Use its actual composite mark, with lower threshold
\(U=N^\lambda\):
\[
 P_\lambda(v)
   = \sum_{\substack{r\mid v,\ r\ {\rm prime}\\U<r<v}}
         (\log r)\sum_{d\mid v/r}
          \mu(d)F_\lambda\!\left(\frac{\log(dN/v)}L\right).
                                                                    \tag{2}
\]
On a true high mark \(r>N^\rho\), all arguments in its
inner sum are at most \(\log(N/r)/L<.482\). For \(m=v/r>1\)
it therefore has the exact coefficient
\(-\Lambda(m)/((1-\lambda)L)\). Define the nonnegative
high score
\[
  E_\lambda(v)
     =\sum_{\substack{v=m r,\ m>1,\ r>N^\rho\\r\ {\rm prime}}}
                  \frac{(\log r)\Lambda(m)}{(1-\lambda)L}.
\]
Its high mark is unique. Prime powers \(m=p^j,j\ge2\)
are still present in this definition; we pay them below.

In the whole mark transfer, the right calibration is
\(a_{F_\lambda}=F_\lambda(0)-(1-\lambda)F_\lambda'(0)=0\).
The left true high source equals \(-E_\lambda\). The exact
transfer therefore gives
\[
 \sum_{\substack{x\in NJ\\(x,N)=1}} E_\lambda(x)P_\lambda(y)
    =-\sum_{\substack{x\in NJ\\(x,N)=1}}
                     E_\lambda(x)\Pi(y)+o_\lambda(M_N).             \tag{3}
\]
There is no imposed roughness on either side in this
identity, and it uses the original \((\lambda,F_\lambda)\)
on both arms. The error is used only at a fixed
\(\lambda\).

By [the central genuine trim](../least_factor_trim_2685/Proof.md),
in the same central normalization, the true \(\log x\,\Pi(y)\)
mass on the squarefree semiprimes \(x=m r\) with
\(m>(N/2)^{.252}\), plus \(R_J(N)\), exceeds \(.3001M_N\).
To retain only \(m\le N^{.481}\), apply
[the true product-prime angular upper](../angular_prime_first_composite/Proof.md)
to the removed least-angle interval. Its upper is
\[
      \left( 3.446\int_{.481}^{.5}
                    \frac{du}{u(1-u)}+o(1)\right)M_N
      =\big(3.446\log(519/481)+o(1)\big)M_N<.263 M_N
\]
for large \(N\), with the fixed own-log versus target-log
endpoint difference paid by the usual angular collar.
Thus under (1) the retained true \(\log x\,\Pi(y)\) mass
exceeds \(.0271M_N\). Here \(r=x/m\gg_J N^{.519}\) is a
genuine high mark, and
\[
  \frac{E_\lambda(x)}{\log x}
      =\frac{\log m}{L}\frac{\log r}{\log x}
               \frac1{1-\lambda}
       \ \ge\ (.252+o(1))(.519+o(1)).
\]
It follows that the true \(E_\lambda\Pi\) term in (3)
exceeds \(.0034M_N\) for sufficiently large \(N\).
This lower uses genuine squarefree semiprimes regardless
of other positive terms.

The opposite score \(P_\lambda(y)\) vanishes at a
prime. It is nonnegative on every actual squarefree
semiprime \(y=u v\) with \(u<v\), \(u>U\). Indeed both
marks are then present; \(F_\lambda(t_d)\le
1+t_d/(1-\lambda)\) for every \(d\), and
\(F_\lambda(\log(vN/y)/L)=0\) because
\(v\ge\sqrt y\) is above its support. The term from the
\(u\)-mark is at least \(\log u\); the \(v\)-mark costs
at most \((\log u)(\log v)/((1-\lambda)L)\).
Since \(v=y/u<N/U\), their sum is nonnegative.
The true semiprimes with \(u\le U\), as well as possible
nonsquarefree opposite \(y\), must still be paid in
(3); the next section does so.

## 2. True mixed tails while keeping the high source prime

Extend \(F_\lambda\) smoothly to the negative half-line
with compact support, by using a fixed continuation of
\(C\) equal to one near zero. The resulting Schwartz
Fourier seminorms are uniformly bounded as
\(0<\lambda\le.006\). For real \(t\) define
\[
 w_t(p)=|1-e^{it\log p/L}|+\frac{\log p}L,\qquad
 W_t(v)=\prod_{p\mid v}w_t(p).
\]
In applications \(p\le N\); the weight may be defined
as \(1\) on primes above \(N\) if needed. The following
physical envelope holds, including repeated prime factors:
\[
    |P_\lambda(v)|\le
            2L\int_{\mathbb R}
                 |\widehat F_\lambda(t)| W_t(v)\,\frac{dt}{2\pi}.
                                                                    \tag{4}
\]
To see this, the exact Fourier factor for the inner
divisor sum in (2) is
\(\prod_{p\mid v/r}(1-e^{it\log p/L})\), with a unit
central phase. For \(r\parallel v\), its normalized
mark weight \((\log r)/L\) is allocated to the term of
degree one in the positive expansion of \(W_t(v)\)
in the summands \(\log p/L\). These terms exhaust the
possible singly occurring marks without any rank
multiplicity loss. For \(r^2\mid v\) the inner product
still contains \(r\), and \(\sum_{r^2\mid v}\log r/L\le1\);
this entire part costs at most \(W_t(v)\) again.

Fix the actual source \(m\) with \((m,N)=1\) and
\(m\ll_J N^{1-\rho}\). The true source prime \(r\)
and \(y=N-mr\) are two primitive affine forms in a
real interval of size \(\asymp_J N/m\). Use
[Henriot, Theorem 3](https://arxiv.org/pdf/1102.1643)
with its [erratum](https://doi.org/10.1017/S0305004114000280).
The true prime \(r\) is majorized by the
multiplicative \(N^{\epsilon_0}\)-rough integer
weight, zero at positive powers of all primes dividing
\(N\), for a fixed small \(\epsilon_0>0\) (say \(.01\)).
No nonmultiplicative prime indicator is fed into the
theorem. On the \(y\)-form use the multiplicative
weight \(\theta^{\omega(y)}W_t(y)\), zero at all
positive powers of primes dividing \(N\), for any
fixed \(\theta\ge1\). Its values at each positive
power of \(p\nmid N\) are \(\theta w_t(p)\), bounded
by \(3\theta\) independently of \(t,\lambda,N\);
the fixed-growth hypotheses of that theorem hold
uniformly. The resultant is \(N\); the corrected
bad-prime set consists of primes of \(N m\). All
positive divisibilities at target primes are already
excluded by the weights. At a prime dividing \(m\)
the \(y\)-form is a nonzero constant; only the
source form has a root, with its good bounded
single-prime factor. In our sum \(m\) is a prime
power, so any exceptional factors introduced by
the leading coefficient cost at most an absolute
constant. The root at 2 is single because \(N\)
is even and \(m\) is odd. At other primes away
from \(Nm\) the two roots are distinct. There is
no fixed prime divisor of the product.

The resulting positive upper has factor
\(\mathfrak S(N)c(m)/L^2\), up to a fixed constant,
where \(c(m)=\prod_{p\mid m,p>2}(p-1)/(p-2)\).
The power scale of the interval permits the
hypotheses on the size and length in the corrected
theorem; split into finitely many fixed-aspect
intervals if needed. The two remaining good Euler
harmonics are uniformly bounded by
\[
 \prod_{N^{\epsilon_0}<p\le N}(1+O(1)/(p-1))
          \ll_{\epsilon_0}1,\qquad
 \prod_{p\le N}\left(1+\frac{\theta w_t(p)}{p-1}\right)
          \ll_\theta (2+|t|)^{C_\theta}.
\]
For the latter split the reciprocal harmonic at
\(\log p=L/(1+|t|)\) and use
\(|1-e^{iz}|\le\min(2,|z|)\); the additional
\(\log p/L\) contribution is bounded. This verifies
the model bound for every actual \(\lambda,t\).

If one also requires a true \(p\mid y\) with
\(p\le N^\eta\), where \(0<\eta\le.01\), then
\(p\nmid Nm\) by the actual target units. Write
\(r=r_0+p k\) with \(0\le r_0<p\) on the
appropriate true progression and \(Y=y/p\).
The two forms \(r_0+p k,\ (N-mr_0)/p-m k\)
are primitive (in particular \(r_0\ne0\bmod p\))
and still have resultant \(N\). The parameter length
is now \(\asymp_J N/(mp)\gg N^{.50}\).
The extra leading prime \(p\) introduces only a
bounded local factor, as the first form is a unit
constant mod \(p\) and the second has one root.
For \(\theta=1\) one can write \(W_t(y)=w_t(p)W_t^{(p)}(Y)\)
where \(W_t^{(p)}\) has value \(1\) at every positive
power of \(p\). This extracts the marked factor
exactly once, even when \(p^2\mid y\); at all other
primes the old weight is retained. Unit masks at
target primes are unchanged. Apply the same
true-source estimate with interval length divided
by \(p\), and sum
\[
       \sum_{p\le N^\eta}\frac{c(p)w_t(p)}p
                         \ll \eta(1+|t|).
\]
Thus no joint primality estimate is presumed for
the opposite residue.

In (3) the source log \(\log r\) and the \(L\)
in (4) cancel the \(L^{-2}\) in these bounds.
The remaining real source harmonic is
\[
       \sum_{m\le N}\frac{c(m)\Lambda(m)}{Lm}\ll 1,
       \qquad
       \sum_{m=p^j,\ j\ge2}\frac{c(m)\log p}{Lm}=O(L^{-1}).
\]
The unrestricted upper is therefore \(O(M_N)\);
the absolute cost of the proper powers on the
high source is \(O(M_N/L)\). The two uniform
absolute tail bounds on the opposite side are
\[
 \sum_{\substack{x\in NJ,\ (x,N)=1\\P^-(y)\le N^\eta}}
                  E_\lambda(x)|P_\lambda(y)|\ll_J \eta M_N,
 \qquad
 \sum_{\substack{x\in NJ,\ (x,N)=1\\\omega(y)>R}}
                  E_\lambda(x)|P_\lambda(y)|\ll_{J,\theta}
                                                  \theta^{-R}M_N.
                                                                    \tag{5}
\]
The second follows by inserting \(\theta^{\omega(y)}\)
for any fixed \(\theta>1\). Integrate the common
Schwartz envelope in (4); all constants in (5)
are uniform in \(\lambda\) in the stated interval.
Once the actual \(N^\eta\) floor on \(y\) is imposed,
the nonsquarefree \(y\)'s occupy \(O(N^{1-\eta})\)
integers by summing \(N/p^2\) over primes above
that floor. The weights in (3) are at most fixed
divisor powers times \(L^2\). Cauchy with their
ordinary divisor moments therefore charges all
these nonsquarefree opposite rows with a power
saving at fixed \(\eta\).

## 3. Keep the genuine mixed ranks

Choose \(\theta>1\) fixed and \(R\) large, then
\(0<\eta\le.01\) small enough that the two fixed
upper bounds in (5) cost altogether less than
\(.001 M_N\). Choose any fixed \(0<\lambda<\min(.006,\eta)\)
and only then take \(N\) sufficiently large for
(3), the actual lower, and the square-error bound.
The surviving opposite squarefree semiprimes have
their smaller prime above \(U\), by the imposed
rough floor, and so their \(P_\lambda\) signs
are nonnegative. Opposite actual primes have
zero score. Proper power source quotients have
been removed. It follows from (3) and the lower
for \(E_\lambda\Pi\) that the negative parts with
the stated \(3\le\omega(y)\le R\) have total
magnitude \(\gg M_N\) on the exact surviving
true high semiprime source. At this fixed rank
each term is bounded by \(O_{F_\lambda,R}(L^2)\).
The source high mark remains unique and the
opposite partitions are by actual \(y\), not by
multiple representations. This yields the stated
distinct-row lower.
