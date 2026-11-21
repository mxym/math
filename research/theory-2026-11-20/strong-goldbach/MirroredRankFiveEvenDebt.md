# A rank-five mirror match forces a genuine rank-two debt

This is a pointwise limitation of the near-half \(\mu\)-only design,
not an obstruction to an arithmetic signed comparison. Use the genuine
central \(sq+ph=N=2x\) row, balanced true \(m=ph\), weights \(W_s(q)\)
and \(F_s(m)=-2\log p\) of
[BalancedSemiprimeEvenRankNeck.md](BalancedSemiprimeEvenRankNeck.md).
In the opened row \(q\) is composite on the profiles below.
Write \(L=\log x\), \(s\) true prime with exponent \(.10<\alpha<.14\),
\(c=(1-\alpha)/2\), and take the true \(p\)-band
\(|\log_x p-(c-\eta)|<w=\eta/1000\).
Keep \(|\mathcal R(F)|\asymp wM_N\).

In this note log shares of **q** factors are normalized by \(\log q\),
so they sum to 1. At fixed exterior scale \((x,s,\log q)\), consider
any real finite signed cutoff measure of total mass 1 on thresholds
\[
             .415\le z\le u\le \tfrac12,\qquad 0<v<.17 .
\tag{1}
\]
The one-sided center uses \(U=q^u\), \(Z=q^z\), \(B=q/Z\),
\(V=q^v\), with literal \(\le U\) and \(<Z\) on its short pieces.
The cutoff law is a law on **scale**, not on the unknown
factorization of q: compare its action on different exponent
shapes at the same scale. It may vary with the exterior
parameters. If interpreting a measure as an equivalent whole
prime-quotient row, take inner supports satisfying the reserves
for the whole switches of the cited note; this only restricts the
class in (1). The algebra below does not need those exchanges.

## 1. An exact two-profile invariant

For either squarefree q profile below, all true prime bases
are \(>V\), and q is not a prime power. On this support the
literal one-sided kernel is exactly
\[
 C_{u,z,v}(q)=-\sum_{\substack{d\mid q\\\sigma_d\le u}}
                       \mu(d)(1-\sigma_d)
               -\sum_{\substack{d\mid q\\\sigma_d<z}}
                       \mu(d)\sigma_d ,
          \qquad \sigma_d=\frac{\log d}{\log q}.
\tag{2}
\]
Indeed the original \(k>V\) test omits no nonzero
\(\Lambda(k)\) divisor of q. Thus the original high short-r
cut becomes \(\Lambda(q)-\sum_{r\le U,r\mid q}\mu(r)\log(q/r)\)
before dividing by \(\log q\). The exact long piece being removed is
\(\sum_{a<Z,a\mid q}\mu(a)\log a/\log q\), by
\(-\mu*\Lambda=\mu\log\). It is subtracted from the
original high kernel, giving (2).

Take \(a\in J=[.458,.462]\). The **rank-five** profile
has two large shares near \(a/2\), with sum exactly \(a\),
and three small shares near \((1-a)/3\), with sum \(1-a\).
Use fixed small open widths for these shapes so all prime
factors can be distinct; the geometry depends only on the
large pair's total a. Every singleton and every pair other
than that large pair lies below .415; the cross-pair upper
is \((2+a)/6\) plus the small width, strictly below .415.
Every triple or higher subset lies above \(1/2\), since
the smallest triple has share \(1-a>.5\).
All five bases have shares \(>.17\).
Thus (2) has the base contribution \(-(1-5+9)=-5\),
and one additional pair of Möbius sign \(+1\), giving
\[
       C_5(a)=-5-\{(1-a)1_{a\le u}+a1_{a<z}\}.
\tag{3}
\]
For the true **rank-two** shape with shares \(a,1-a\),
only \(d=1\) and the small prime can enter (2); the latter
has Möbius sign \(-1\). Hence
\[
       C_2(a)=-1+\{(1-a)1_{a\le u}+a1_{a<z}\}.
\tag{4}
\]
In particular for any common signed mass-one cutoff law,
including an arbitrary signed sweep and unequal \(u,z\),
\[
                          C_5(a)+C_2(a)=-6.
\tag{5}
\]
This is exact at inclusive/strict cutoff boundaries.

## 2. The true mirror value on rank five

For \(n=sq\) on the rank-five profile, keep the reflected
opposite half coefficient \(C^\dagger(n)\) of
[ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md).
All \(n\)-prime factors are polynomially large and \(s\nmid q\),
since all \(q\)-prime factors in absolute exponent are
larger than .15, while \(s<x^{.14}\).
Set \(t=\tfrac12\log q\), \(\Delta=\tfrac12\log s\),
and \(S_q(y)=\sum_{d\mid q,\log d\le y}\mu(d)\).
The literal forward short reassembly gives
\[
       C^\dagger(sq)
          =-\sum_{d\mid sq}\mu(d)(\log(sq)-2\log d)_+
          =-2\int_{t-\Delta}^{t+\Delta} S_q(y)\,dy .
\tag{6}
\]
Indeed no divisor of \(sq\) is in a subpower band about
its half: for \(d\mid q\) the corresponding thresholds
on \(d\) are \(t\pm\Delta\), which avoid every subset log
by fixed margins in the displayed five-factor geometry.
Consequently the forward \(J\) term is zero, the original
high \(d\,k\) cut follows from \(d\) high and every true
\(k\) having a fixed exponent margin, and both remaining
forward short sums use the same divisors below the half.
Splitting each divisor by its \(s\)-bit gives the second
expression in (6).

For the odd squarefree rank-five q, complement gives
\(S_q(t+b)=S_q(t-b)\) for almost all b.
Let \(\Delta'=\Delta/\log q\), so
\(\Delta'\) ranges asymptotically from \(1/18\) to \(7/86\).
On \(y/\log q\in[1/2-\Delta',1/2]\),
\(S_q(y)=5+1_{y/\log q\ge a}\): the ten pairs are as
described above and no triple enters. Thus the normalized
mirror is
\[
 \frac{C^\dagger(sq)}{2\log s}
        =-6+H_0(a),\qquad H_0(a)=1-\frac{1/2-a}{\Delta'}.
\tag{7}
\]
Throughout \(J\), \(H_0(a)>.24\) for large \(x\).
Under the would-be log calibration
\((\log p/\log s)W_s(q) C^\dagger(sq)\) the algebraic
mirror on this rank-five shape cancels the forward
opened term \(W_s(q)F_s(m) C_5(a)\) precisely when
\(C_5(a)\) equals (7).

Therefore **any law** in (1) that matches this mirror
pointwise across the indicated rank-five shapes to
error \(\epsilon_0\) forces
\[
                         C_2(a)\le -H_0(a)+\epsilon_0
                                <-.24+\epsilon_0
                      \quad(a\in J).
\tag{8}
\]
It forces an adverse even-rank coefficient far from the
original rank-two near-half seam. For actual \(q\) in
that rank-two band, \(n=sq\) has three macro prime
factors, all below its half with a fixed margin, since
\((1-\alpha)(1-a)\le .90\cdot .542<.488\) up to
\(O(1/L)\), and each double product is above the half.
The same off-seam \(C^\dagger(n)=0\) follows by
complementation of the centered linear ramp. Thus the
ordinary opposite-half mirror does not pay (8).
The hypothesis here is **pointwise matching across the
exponent shapes** at a common scale, not an assumed
asymptotic for the weighted population at an individual
even target.

## 3. Genuine population of the forced debt

Suppose such a pointwise match is requested throughout
the \(s\)-band above with \(\epsilon_0\le .01\).
The adverse contribution in (8) is not supported only
on synthetic tuples or endpoints. Take large auxiliary \(X\)
and true \(s\) in any fixed inner exponent band inside
\((.10,.14)\) relative to \(X\). Write \(Q_0=X/s\);
take true primes
\[
          Q_0^{.459}<r<Q_0^{.461},\qquad
            .79Q_0/r<R<.81Q_0/r,\qquad q=rR.
\]
For fixed s the number of such q is \(\gg X/(s\log X)\),
by ordinary prime PNT for \(R\) and the positive harmonic
mass on the r-band. This provides \(n=sq\in[.79X,.81X]\).
Independently take true p in
\(p s^{1/2}\in(X^{1/2-\eta-w/2},X^{1/2-\eta+w/2})\)
and true \(h\in[1.19X/p,1.21X/p]\), excluding the finitely
many labels dividing n. There are \(\gg wX/\log X\)
such m per fixed s,q; both m labels remain prime and the
factorization is unique. All choices give actual even
\(N=n+m\in[1.98X,2.02X]\), central window and \((m,N)=1\).
Passing to \(x=N/2\) changes exponent shares by
\(O(1/\log X)\), so the true profile and \(a\in J\) still
hold. With \(C_2(a)<-.23\), \(W_s(q)\gg1\) and
\(-F_s(m)\asymp\log X\), the sum of this strictly adverse
subsum over these even N is \(\gg w X^2/\log X\).

The singular factor has bounded mean over this interval,
by its elementary squarefree-divisor expansion proved in
[BalancedSemiprimeCutoffTuningObstruction.md](BalancedSemiprimeCutoffTuningObstruction.md).
Thus this adverse even cohort is \(\gg wM_N\asymp|\mathcal R(F)|\)
for some even \(N\) in every sufficiently large such interval.
This is **not** a uniform lower on every N, nor does it
prohibit other negative physical contributions from paying
that debt. It rules out curing that rank-five packet by
pointwise mirror matching while keeping all rank-two
subsum costs \(o(|\mathcal R(F)|)\) in this one-sided
near-half family. No original cubic sign budget or
strong Goldbach conclusion is inferred.

**Dated comparison.** [Arneth XII, September 28, 2026](https://zenodo.org/records/23016346) analyzes five-factor cutoff coefficients and a conditional capacity comparison. The invariant (5) concerns two paired actual factor shapes, with an explicit rank-two consequence of matching the specified mirror. The earlier [compact-cutoff obstruction](BalancedSemiprimeCutoffTuningObstruction.md) ensures some adverse chamber but does not force this particular rank-two debt. Neither result bounds net arithmetic compensation.
