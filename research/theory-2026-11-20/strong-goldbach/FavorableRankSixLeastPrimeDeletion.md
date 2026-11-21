# A fixed-target least-prime deletion in the favorable rank-six rows

Use the **actual true reflected rank-six inputs** \(T_{6,i}\)
of [FullFavorableRankSixAbsorption.md](FullFavorableRankSixAbsorption.md),
for \(i=1,2,3\). Thus \(N=2x\), \(L=\log x\), \(n=sq\in(x/2,x]\),
\(m=N-n=pA_1A_2A_3DE\) with the literally specified six true
prime bands, the original \(s\)-band \(i\), and \((m,N)=1\).
In an opened row \(q\) is an integer. The weight
\[
 {\cal W}(s,q)=W_s(q)(-C^\dagger(m))
\]
is nonnegative and \(O(L)\) on exactly this input; it contains the
rank-six shape, unit and central restrictions by convention.
No prime weight on the reflected \(m\) is relaxed.

Fix a smooth real function \(f\) which is 1 for \(0\le t\le.196\)
and 0 for \(t\ge.199\), and extend it smoothly to compact support
on the negative line as well. Use the alternate opened coefficient
\[
 D_f(q)=\sum_{d\mid q}\mu(d)f(\log d/L),\qquad
 C_f(q)=\Lambda(q)/\log q-D_f(q).
 \tag{1}
\]
On the indicated true rank-six rows, replacing the true \(q\)-prime
indicator by \(C_f\) preserves the whole signed sum up to
\(O_{A,\eta,f}(xL^{-A})\) for every fixed \(A\).
On the same common physical \(Q\) of the cited note this coefficient
is **exactly \(+3\)**: there are just four short prime singletons
for \(D_f\), no short pairs, and \(q\) is composite.
Thus this alternative preserves all three signed same-equation
compensations, with their actual occupancies and with no altered
weight or new prime-supply assumption.

**Least-prime deletion.** For every fixed \(0<\delta\le.01\), in
each of these rows independently and uniformly in the actual even \(N\),
\[
 \sum_{\substack{s,q\\P^-(q)\le x^\delta}}
       {\cal W}(s,q)|C_f(q)|
   \ \ll_{\eta,f}\ 
        \mathfrak S(N)\frac{x}{L}
               \big(\sqrt\delta+L^{-1/2}\big)+O_{A,\eta,f}(xL^{-A}).
 \tag{2}
\]
The coefficient of the displayed \(\sqrt\delta\) bound does not
grow when \(\delta\) is decreased. In particular the absolute
smallest-factor portion of the physical outside-\(Q\) complement
can be made arbitrarily small on the actual reference scale, before
taking \(x\) sufficiently large. The remaining polynomially rough
complement is not bounded here.

## 1. The uniform physical progression input

Write \(R=Nsm\) for the exact local mask in a reduced mean.
For a divisor modulus \(a\) of \(q\) the physical progression is
\(m\equiv N\bmod s a\), with varying target \(N=2x\).
As in [SameEquationRankCompensation.md](SameEquationRankCompensation.md),
[Lichtman's Proposition 5.2](https://arxiv.org/html/2309.08522v1#S5)
applies with the three modulus slots \((a,s,1)\), and independent
true SW source \(p\) and other source \(A_1A_2A_3DE\).
It applies uniformly through
\[
                            a\le x^{.408}.
 \tag{3}
\]
Indeed \(\log_x p=.4305-\eta+O(\rho)>.4284\).
The first rail has margin \(>.020\), the second
\(2\log_x p+\log_x s<1\) has margin \(2\eta-O(\rho)\)
in the tightest row \(i=1\), and the two other rails are
strictly below 2 as in the earlier ranks with larger \(a\).
The actual source bands remain independent; their grouped coefficient
has multiplicity at most one. SW, the exact unit mask, the independent
slot of size one, and smooth log weights use precisely the previous
reductions.

For clarity (3) also handles divisor-bounded coefficients of \(a\)
after arbitrary logarithmic reserve. Clip a coefficient
\(\ll\tau(a)^C L^C\) at \(L^J\) and apply the 1-bounded theorem
after division by \(L^J\). To pay the clipped tail, for each \(s,a\)
the integer count in the physical residue class is
\(O(x/(sa)+1)\), while the reduced expected count is
\(O(x/\phi(sa))\). Harmonic divisor moments and
\(\sum_{s\text{ in band}}1/s\ll1\) give arbitrary log reserve on
\(\tau(a)^C L^C>L^J\) for sufficiently large \(J\).
The total floor cost is \(x^{.548+o(1)}\).
The factor \(sa/\phi(sa)\) has only log-power cost.
This proof is independent of any signs used to aggregate errors.
The possible \(s\mid a\) errors can also be deleted at power
cost: in the same trivial count their harmonic sum is
\(O(xL^C\sum_s1/s^2)\), and the naive floor is power-small.
Terms \((a,N)>1\) are absent physically and need not be included
in an expected value. The \(m\)-source in a reduced progression
is counted with \((m,sa)=1\), so the exact remaining mask is
\((a,R)=1\), and \(\phi(sa)=(s-1)\phi(a)\).

All such replacements can be applied to the positive
\({\cal W}\) by standard fine independent meshes. In the physical
central boundary a changed \(m\) lies in an interval of length
\(O(xL^{-K})\); summing the true progression floors
\(xL^{-K}/(sa)+1\) over the stated \(s,a\) ranges, with divisor
moments, gives arbitrary log reserve. The analogous estimate in
the reduced center uses an interval count of integers and its
harmonic modulus sum. Within a box replace the normalized smooth
weights by their midpoint values to relative log accuracy in
absolute terms; \({\cal W}=L\) times a bounded smooth function
of the actual factors and of the central ratio by formula (5)
of the cited note. These meshes cost at most fixed powers of
\(L\), which the arithmetic remainders can absorb. No sieve test
or divisibility relation on \(q\) is inferred by an approximate
mesh: these are retained as actual residue classes.

The reduced reference mass before a local divisor condition is
\[
 T_0=\sum_{s,m\text{ of the actual source}}
        \frac{{\cal W}(s,(N-m)/s)}{s-1}\ll_\eta x ,
 \tag{4}
\]
where the smooth weights are evaluated at the real indicated
\(q\) in the reference, without requiring \(s\mid N-m\).
The count of the six-factor \(m\)-products is \(O_\eta(x/L)\):
fix five of the actual prime factors, use ordinary PNT upper
bounds in the fixed proportional interval for the last polynomial
prime, and sum the bounded harmonic masses of the five fixed
polynomial bands. The weight is \(O_\eta(L)\).
For fixed source \(s,m\), each of the finitely many additional
prime factors in \(R=Nsm\) is large, and
\(\mathfrak S(R)\ll \mathfrak S(N)\); adjoining one extra prime
costs at most 2.

Whole centering in (1) now follows by (3) and the truncated
coprime \(\mu/\phi\) identity from
[TrueRankFiveReflectedTypeI.md](TrueRankFiveReflectedTypeI.md).
Write \(f(\log d/L)\) as the integral of the smooth cutoff layers
against \(-f'\) supported in \([.196,.199]\) on the positive line.
For each layer the finite masked constant \(\mu/\phi\) sum is
log-small, uniformly for polynomial \(R\). Thus the entire
weighted mean of \(D_f\) is log-small. Proper prime powers of
\(q\) have power-small mass by counting \(s\) and \(q\) before
the reflected restriction.

## 2. A local shifted variance at a true small prime divisor

Let \(r\le x^\delta\) be prime. On the actual \(r\mid q\) support
we necessarily have \(r\nmid Ns\), as \(r<s\) and \((n,N)=1\).
The identity
\[
 D_f(q)=
 \sum_{\substack{d\mid q\\(d,r)=1}}\mu(d)
       \big[f(\log d/L)-f((\log d+\log r)/L)\big]
 \tag{5}
\]
holds regardless of the exponent of \(r\) in \(q\),
since the Möbius sum contains only squarefree divisors.
Put \(\varepsilon_r=\log r/L\), \(g_r(t)=f(t)-f(t+\varepsilon_r)\).
Its fixed compact-support \(C^k\) norms are \(O_{f,k}(\varepsilon_r)\)
for every fixed \(k\). In particular the upper divisor support is
still \(d\le x^{.199}\).

For even polynomial \(H\), consider the exact harmonic density
\[
 B_H(g)=\sum_{\substack{d,e\ge1\\(de,H)=1}}
   \frac{\mu(d)\mu(e)}{\phi([d,e])}
              g(\log d/L) g(\log e/L).
\]
For the smooth \(g=g_r\), uniformly in \(H\le x^C\),
\[
                        |B_H(g_r)|
          \ll_{f,C}\frac{\mathfrak S(H)}{L}\,\varepsilon_r^2 .
 \tag{6}
\]
This is a localized Goldston–Yıldırım smooth divisor-square bound
(compare [Goldston–Pintz–Yıldırım](https://annals.math.princeton.edu/wp-content/uploads/annals-v170-n2-p10-p.pdf));
the exact \(1/\phi\) factors are as follows.
Write \(g(t)=e^{-t}\int_{\mathbb R}\widehat{(e^\cdot g)}(u)
e^{-iut}\,du\), with any fixed normalizing Fourier convention.
The transform decays as
\(O_{f,B}(\varepsilon_r(1+|u|)^{-B})\).
With \(z=(1+iu)/L,w=(1+iv)/L\), the squarefree double series is
the absolutely convergent Euler product
\[
 B_H(z,w)=\prod_{\ell\nmid H}
 \left(1-\frac{\ell^{-z}+\ell^{-w}-\ell^{-z-w}}{\ell-1}\right).
\]
The full product
\(Z(z,w)=\zeta(1+z+w)/(\zeta(1+z)\zeta(1+w))\) has local
factor \((1-\ell^{-1-z})(1-\ell^{-1-w})/(1-\ell^{-1-z-w})\).
For all \(\ell\nmid H\) their ratios have absolute product \(O(1)\):
the local difference is \(O(\ell^{-2})\) and the denominator
factor is uniformly bounded away from zero. For \(\ell\mid H\)
one divides by that full local factor. At \(z=w=0\) the inverse
product over the excluded primes is \(H/\phi(H)\ll\mathfrak S(H)\).
For \(|u|,|v|\le L^{1/2}\), the change in the product's log absolute
value is \(O((|z|+|w|)\sum_{\ell\mid H}(\log\ell)/\ell)=O(1)\).
Here \(\sum_{\ell\mid H}(\log\ell)/\ell\ll_C\log L\), by splitting
at \(L^2\) and using \(\log H\ll L\) above it.
On this near-origin range Laurent expansion of \(\zeta\) gives
\[
              |Z(z,w)|\ll \frac{|z||w|}{|z+w|}
                      \ll \frac{(1+|u|)(1+|v|)}{L}.
\]
On the Fourier tails the direct absolute Euler product is \(O(L^C)\)
for an absolute \(C\); indeed each term of the series has real
shift at least \(1/L\) on an active prime. Rapid decay then
beats any log power. These bounds prove (6), including the uniform
\(\varepsilon_r^2\) factor.

On the actual rank-six input define
\(V_r=\sum_{r\mid q}{\cal W}(s,q)|D_f(q)|^2\).
Use (5), with modulus \(a=r[d,e]\), and (3); its largest exponent
is \(.01+2(.199)=.408\).
Since \(r\nmid[d,e]\) and \(r\nmid s\), its harmonic density is
\(1/((r-1)\phi([d,e]))\) in addition to \(1/(s-1)\),
with mask \(H=Rr\) on \(d,e\); if \(r\mid R\) there is no
such contribution. Equations (4), (6) give an upper bound
\[
 V_r\ll_{\eta,f}
   \frac{\mathfrak S(N)x}{(r-1)L}
             \left(\frac{\log r}{L}\right)^2+|E_r|,
                  \qquad \sum_{r\le x^\delta}|E_r|\ll_A xL^{-A}.
 \tag{7}
\]
To see the assertion about the error vector, take arbitrary signs
on \(r\) and combine all \(r,d,e\) into the single modulus \(a\)
coefficient. It has multiplicity at most \(\tau(a)^3\) since
\(r\mid a,\ d,e\mid a\). Its dependence on \(r\) and on the two
smooth factors \(g_r\) is wholly inside this coefficient, independent
of the \(s\)-slot. Apply the divisor clipping and meshes from §1,
then take the signs of the actual aggregated errors. This accounts
for the errors uniformly without requiring individual BV for a
fixed \(r\).

## 3. Exact least-prime support and absolute pairing

Let \(K_r=\sum_{P^-(q)=r}{\cal W}(s,q)\) on this same actual row.
Apply an upper dimension-one Rosser sieve to the smaller primes
conditional on \(r\mid q\), with divisor level \(x^{.10}\).
Then \(a=r d\le x^{.11}\) is inside (3).
In the reduced density, for fixed \(s,m\) with \((r,R)=1\),
the divisor local law is \(1/(\ell-1)\) at primes
\(\ell\nmid Rr\), and zero at the others.
The upper bound for this dimension-one law is
\(\ll \prod_{\ell<r,\ell\nmid Rr}(1-1/(\ell-1))
 \ll \mathfrak S(Rr)/\log r\).
The upper-sieve ratio \(\log(x^{.10})/\log r\ge10\)
has ample reserve; removing local primes only decreases the
standard dimension-one product ratio. This is the usual
Rosser upper-bound sieve (or the elementary upper Selberg sieve
with a fixed sufficiently smaller level).
Accounting for \(r\mid q\) and (4), we obtain
\[
 K_r\ll_\eta
   \frac{\mathfrak S(N)x}{(r-1)\log r}+|E'_r|,
                   \qquad\sum_{r\le x^\delta}|E'_r|\ll_A xL^{-A}.
 \tag{8}
\]
Here \(r=2\) is absent on the physical unit support. The error
statement again follows by arbitrary signs on \(r\) and slot
aggregation; in fact \(r\) is the largest prime of \(a=r d\) with
all factors in \(d\) smaller than \(r\), so its representation is
unique. Both bounds are uniform in the actual target and are for
the above same positive weight.

For a composite \(q\) not a proper prime power,
\(|C_f(q)|=|D_f(q)|\); the exceptional proper powers have a
power-small total before the smallest-factor split.
Cauchy for each actual least prime \(r\) bounds (2) by
\(\sum_{r\le x^\delta}\sqrt{V_r K_r}\), up to that negligible error.
Summed error terms have arbitrary log reserve by Cauchy across \(r\)
and (7), (8). The leading upper bound is
\[
 \ll_{\eta,f}\ \frac{\mathfrak S(N)x}{L^{3/2}}
      \sum_{r\le x^\delta,\ r\text{ prime}}\frac{\sqrt{\log r}}{r-1}
 \ll_{\eta,f}\ \frac{\mathfrak S(N)x}{L^{3/2}}
                   (1+\sqrt{\delta L}).
\]
The last step is prime partial summation from
\(\sum_{r\le T}(\log r)/r\ll\log T\).
This proves (2) for the genuinely weighted fixed-target sequence,
not a statement merely in a local random model.

The alteration (1) is made **only** in the favorable rank-six
rows and does not alter the true \(T_2\) exchange or its remaining
high \(h\) terms. In particular it does not turn the already
absorbed physical profile into a proof of a lower bound for actual
true prime \(q\) on the whole rank-six input. It removes the
polynomial-small least-factor part of that specific outside-\(Q\)
complement, uniformly to arbitrarily small reference-scale error;
its polynomially rough part remains.

**Dated comparison.** [Pham, October 30 v1](https://www.preprints.org/manuscript/202610.3061) studies a separate weighted Type I analysis and rough benchmark. The present result is an absolute estimate in the stated actual rank-six reflected profile, with its original sign and simultaneous varying-(r) error accounting. It uses classical Fourier-weighted divisor-square calculations and the cited fixed-target progression estimate, with no priority or global-sign claim.
