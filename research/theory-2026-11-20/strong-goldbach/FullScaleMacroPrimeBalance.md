# Full-scale reflected cofactor balance on the original balanced marker range

Freeze only the **cutoff tests** in the original literal reflected weight on fine \(p\)-intervals, with an actual physical divisor-neck estimate for every disagreement. Every reflected divisor can then be combined into a single arbitrary cofactor \(G\)-coefficient before full-scale distribution. In particular the resulting genuine different-integer balance reaches the earlier \(s\simeq x^{.139},p\simeq x^{.4305}\) reflected source, using a short \(q\)-cutoff that keeps its adverse rank-five coefficient.

Use the original central support and abbreviations:
\(N=2x,L=\log x,n=sq\in(x/2,x]\), \(m=N-n=pG\in[x,3x/2)\),
\((n,N)=1\), with \(s,p\) genuine primes. Put
\(W_s(q)=(1-t)(1-2t)^2,\ t=\log s/\log n\), and
\(F(m)=C^\dagger(m)\) with exactly its original \(H,U,V,Q_0,B,Z=m/B\)
from [ParityBalancedHalfSwitch.md](ParityBalancedHalfSwitch.md).
In particular \(U=\sqrt{x}/H^4,\ V=H,\ Q_0=\sqrt{x}/H^2,
B=\sqrt{x}H\) with \(H=\exp(L^{\sigma_0})\), \(0<\sigma_0<1\).
The variable \(G\) is arbitrary, including squareful inputs;
\(q\) is an integer on an opened row.

Keep fixed genuine prime windows
\[
 s\in[x^{\alpha_0},x^{\alpha_1}],\quad
 p\in[x^{\beta_0},x^{\beta_1}],\qquad
 .1\le\alpha_0\le\alpha_1\le.14,\quad
 .42<\beta_0\le\beta_1<.49 .
\]
Let \(f\) be a fixed smooth real function equal to 1
near 0, with positive-side support below exponent \(u>0\),
and put \(D_f(q)=\sum_{d\mid q}\mu(d)f(\log d/L)\).
The only level condition needed here is
\[
                              \alpha_1+u<1/2 .
 \tag{1}
\]
For each \(G\) choose arbitrary subintervals of the indicated
\(p,s\) windows; even the maximizing
rectangles are allowed separately for each \(G\). Then
\[
 \sum_G \ \sup_{I_p,I_s}
 \left|\sum_{\substack{p\in I_p,\ s\in I_s,\ p,s\ {\rm prime}\\
          m=pG\in[x,3x/2),\ n=N-m,\ s\mid n,\ (n,N)=1}}
       W_s(n/s)\,F(pG)\,D_f(n/s)\right|
                              \ll_{A,f}xL^{-A}.
 \tag{2}
\]
Any independent bounded \(G\)-only restriction is allowed,
as is the labelled counting convention when two \(p\)'s
from the window divide \(m\). One may impose absence
of another eligible \(p\) in \(G\) to count each \(m\) once.
The theorem estimates the **whole exact \(F\)**, not \(F\)
with its true \(-2\Lambda(G)\) term omitted.
It does not assert an individual estimate for a single
chosen cofactor of size \(o(xL^{-A})\) relative to its own
density; the actual statement is the averaged absolute one.

## 1. Direct p-bit separation with all genuine squareful cofactors

First discard \(p^2\mid m\) on the true side only.
There are \(O(x\sum_{p\ge x^{\beta_0}}p^{-2})\) actual marked
\(m\)'s before weighting. At fixed \(m\) the numbers of
\(s\)- and \(p\)-markers, \(|F(m)|\), and \(|D_f(n/s)|\)
are bounded by fixed powers of \(L,\tau(m),\tau(n)\).
Ordinary divisor moments on the integer ranges of \(m,n\)
and Hölder give arbitrary log reserve on this power-small
support. This is the only squareful discard concerning \(G\).
In particular prime powers at all small bases of \(G\)
remain physically present.

Use formula (10) of the [original half-switch note](ParityBalancedHalfSwitch.md):
\[
\begin{split}
 F(m)={}&\sum_{\substack{d\mid m\\ d\ge Z}}\mu(d)\log(m/d)
       +\sum_{\substack{d\mid m\\ d<Z}}\mu(d)\log d
       + E_H-E_C+E_P,\\
 E_H={}&\sum_{\substack{d\ell\mid m\\d>U,\ d\ell<Z}}
                            \mu(d)\Lambda(\ell),\\
 E_C={}&\sum_{\substack{d\ell\mid m\\d>U,\ \ell\le V\ {\rm or}\ d\ell\le Q_0}}
                            \mu(d)\Lambda(\ell),\\
 E_P={}&\sum_{\substack{d\ell\mid m\\\ell\le V,\ d\ell<Z}}
                            \mu(d)\Lambda(\ell).
\end{split}
 \tag{3}
\]
The union in \(E_C\) has the \(d>U\) condition on both
parts and is counted only once. The \(\ell\)'s in all
corrections have size \(O(H^3)\) on the whole actual
central band: \(\ell<Z/U\) for \(E_H\), \(\ell\le V\)
or \(\ell<Q_0/U\) for \(E_C\), and \(\ell\le V\) for \(E_P\).
Retain a common bound \(\ell\le3H^3\), also valid after
any of the following relative log-small changes of tests.
Since \(p\) is polynomially large, none of these \(\ell\)'s
has the base \(p\).

Split the \(p\)-bit of each Möbius divisor \(d=p^\iota a\),
\(\iota\in\{0,1\}\).
On the retained \(p\nmid G\) support this is the true
bijection, with \(\mu(d)=(-1)^\iota\mu(a)\).
The independent physical divisor requirements are \(a\mid G\)
in the first two terms and \(a\ell\mid G\) in all corrections,
including when \(a,\ell\) have a common small base.
They are not altered at any stage. The coefficients
\(\log(m/d)=(1-\iota)\log p+\log(G/a)\) and
\(\log d=\iota\log p+\log a\) separate at once.
The only tests for \(F\) which may depend on \(p\) are
\[
 p^\iota a\gtrless pG/B,\quad
 p^\iota a\ell <pG/B,\quad
 p^\iota a>U,\quad p^\iota a\ell\le Q_0 .
\]
For the first two comparisons with \(Z=pG/B\), equivalently
compare the **true complementary divisor**
\(m/(p^\iota a)\) or \(m/(p^\iota a\ell)\) with the fixed \(B\).
The other two compare a true divisor with fixed \(U,Q_0\).

Partition \(p\) into disjoint relative \(L^{-K}\) boxes,
with representative \(P\) in each. Freeze \(p\) to
\(P\) in these tests only, never in the physical divisibility
or in the \(\Lambda,\mu\) labels or the real additive equation.
This makes every test into a \(G\)-only condition on the
given box. If an actual term's inclusion changes, then
a true divisor \(b\mid m\) lies within relative \(O(L^{-K})\)
of one of \(T=U,Q_0,B\).
For each \(T\) the count of candidate physical \(m\)'s is
\[
       O\!\left(\sum_{b=T(1+O(L^{-K}))}\frac{x}{b}\right)
                 =O(xL^{-K}+x/T).
\]
All three \(T\)'s are at \(x^{1/2+o(1)}\).
There is no sum over the number of short reflected divisors;
every bad pair is accounted for by the union of those three
physical integer-divisor events.
The original Möbius/prime-power weights and numbers of
possible labels are bounded by divisor moments on \(m,n\).
Hence the **whole** changed true contribution has arbitrary
log reserve by taking \(K\) large enough, including after
multiplication by \(D_f(n/s)\) and arbitrary bounded
\(G\)-only weights. The same holds for the \(p^2\) tail
if one now removes its coupled exclusion in the frozen expression.
Thus, on each \(p\)-box, \(F(pG)\) is replaced by a finite
linear combination of independent \(p\)-log weights times
arbitrary \(G\)-coefficients
\(\ll L^C\tau(G)^C\), with arbitrary-log small total error.
This replacement includes the entire true table (3), and
needs neither squarefree \(G\) nor a squareful-core decomposition.

## 2. Full-scale convolution estimate for the frozen coefficient

For transparency one can use the following elementary
two-slot Bombieri–Vinogradov estimate. For independent
intervals \(p\asymp P_0,\ G\asymp Y\) with \(P_0Y\asymp x\)
and the specified polynomial sizes, let the \(p\)-coefficient
be the prime indicator with ordinary log weights and the
independent unit-on-\(N\) mask, and let \(b(G)\ll
L^C\tau(G)^C\) be arbitrary.
At any fixed \(Q=x^{1/2-\varepsilon}\),
the summed absolute discrepancies of this product
sequence relative to the actual reduced mean are
\(O_A(xL^{-A})\), with maximum over reduced residues.
The fixed short interval endpoints are permitted.

Here is a quick proof of the needed form.
Drop at most \(O(1)\) large \(p\)'s dividing an outer modulus
\(q_0\le Q\) when replacing an imprimitive character by its
primitive character on the \(p\)-slot. This causes summed
error of order
\[
           O(L^C(Y\sqrt Q+Q\sqrt Y))
\]
by character orthogonality at \(q_0\),
Cauchy and \(\sum_{G\asymp Y}|b(G)|^2\ll YL^C\).
Both terms are power smaller than \(x\) for our true \(P_0\)-range.
More explicitly the average over \(\chi\bmod q_0\) of
\(|S_G(\chi)|\) is at most
\(O(L^C\sqrt{Y(Y/q_0+1)})\).
Small nonprincipal conductors \(r\le L^{C_0}\) have arbitrary
log savings from ordinary prime Siegel–Walfisz on \(p\);
the number of such primitive characters and the harmonic
sum over \(q_0/r\) cost only log powers.

For the other conductors put \(q_0=r k\), open the
imprimitive unit mask in the arbitrary \(G\)-slot by
\(\sum_{d_0\mid(k,G)}\mu(d_0)\), and fix \(d_0\).
The progression coefficient becomes a divisor-bounded weight
on length \(Y/d_0\). Since \(\phi(r k)\ge\phi(r)\phi(k)\),
summing over \(k\) with \(d_0\mid k\) costs
\(O(L^C/(\phi(r)\phi(d_0)))\) at fixed \(r,d_0\).
For \(r\asymp R\) use the classical primitive character
large sieve and Cauchy on the two independent sums.
The dyadic contribution before summing \(d_0\), with its
\(1/\phi(d_0)\) factor removed, is at most
\[
 L^C\tau(d_0)^C
  \frac{\sqrt{P_0 Y/d_0}}{R}
               \sqrt{(P_0+R^2)(Y/d_0+R^2)} .
\]
By expansion this is
\[
 \ll L^C\tau(d_0)^C
 \left(\frac{x}{d_0R}
        +P_0\sqrt{Y/d_0}+(Y/d_0)\sqrt{P_0}
        +R\sqrt{x/d_0}\right).
\]
Here \(R\le Q/d_0\), and the factors \(P_0,Y\)
are both polynomial, so all but the \(x/(d_0R)\)
term are power-small after the harmonic \(d_0\)-sum;
that term has arbitrary log reserve from \(R>L^{C_0}\).
This derivation also handles the independent integer masks on the
\(G\)-slot. For the true \(p\)-slot ordinary Siegel–Walfisz on
arbitrary fixed interval endpoints remains valid after removal of
the \(O(L)\) prime factors of \(N\) and after smooth log weights.
Thus no SW assertion is imposed on the arbitrary cofactor.
This is the ordinary full-scale convolution BV argument; see also the [Oxford manuscript of Maynard, Lemma 8.9](https://ora.ox.ac.uk/objects/uuid%3A39a52f47-3770-4ddd-b7a2-b2a4f7300931/files/srj4305733) and [the repo's previous applications](FullScaleConvolutionBV.md).

Use this on the frozen coefficients, by opening \(D_f(q)\)
only in the actual **quotient** divisor \(d\).
The progression at the full product scale is
\[
                           pG\equiv N\pmod {s d}.
\]
The modulus is genuine, since \(d\mid n/s\).
It is coprime to \(N\) on the true support; when not it
contributes zero and is omitted.
There are at most boundedly many \(s\)-representations of a modulus,
because \(s\ge x^{\alpha_0}\) is prime, and \(d\) is determined.
In particular any overlap \(s\mid d\) is allowed in this application.
Condition (1) puts these true moduli below the fixed square-root
reserve; **the full \(G\)-slot is used**, not length \(G/e\)
for any reflected divisor \(e\).
There is no dependence of a frozen coefficient on the
quotient divisor \(d\).

The actual central product \([x,3x/2)\) and
\(W_s(n/s)\) are separated by fine independent relative interval
meshes or the usual initial-product separation.
The log \(s\) enters only as a fixed power after expanding
\(1/\log n\) about \(1/L\); all other factors are smooth in \(m/x\).
A changed product at a central endpoint occupies an
\(O(xL^{-K})\) physical \(m\)-strip with all its divisor costs
paid by moments. The analogous reduced principal strip
is bounded by the harmonic sum of actual moduli times
ordinary divisor moments in \(m\).
Thus all these separations and the \(p\)-cut freezing
use only fixed log-power numbers of boxes and arbitrarily
large log reserves. The exact masking in the principal
then depends on the fixed \(s,p,G\), not on additional
small reflected labels hidden in it.

Fix actual \(p,G,s\) in that principal with \((s,NpG)=1\).
With \(R_0=NpG\), the remaining physical \(d\)-law is
\[
 \sum_{(d,R_0)=1}
       \frac{\mu(d)f(\log d/L)}{\phi(s d)}.
\]
For \(s\nmid d\) take out \(1/(s-1)\); the finite masked
\(\mu/\phi\) moment on polynomial cutoffs has arbitrary log
reserve ([finite masked harmonic identity](TrueRankFiveReflectedTypeI.md)), and \(f\) is an integral of such fixed positive-scale
cutoff layers because it is flat at zero.
For \(s\mid d\), the exact \(\phi(s d)\) ratio and trivial
harmonic divisor sum give \(O(L^C/((s-1)s))\).
The latter is power-small after summing actual \(s\);
no equality of \(\phi(s d)\) with \((s-1)\phi(d)\) is used
there. This shows the whole reduced mean is log-small,
uniformly for any bounded \(G\)-only multiplier.
No matching assumption is introduced and the prime
part of \(F\) cannot have been lost, since the entire
argument froze the literal (3) without alteration.

## 3. True distinct-integer compensation, including the old p scale

For fixed \(p,s\) intervals, dualizing the preceding uniform
\(G\)-mask gives the averaged absolute norm over \(G\).
Use independent fine \(p,s\) meshes to allow the endpoints
to vary with \(G\): in each box use the fixed \(G\)-only
mask selecting the requested rectangles and their signs.
The actual endpoint estimates are elementary:
an unresolved \(p\)-edge for fixed \(G\) has
\(O((x/G)L^{-K}+1)\) integers, whereas an unresolved
\(s\)-edge at \(s_0(G)\) has \(O(s_0L^{-K}+1)\)
candidate short markers and at most \(O(x/(G s_0)+1)\)
\(p\)'s per marker by the **actual** progression
\(pG\equiv N\bmod s\).
Unit support excludes \(s\mid G\). After summing \(G\ll x^{1-\beta_0}\), the \(p\)-edge count is \(O(xL^{1-K}+x^{1-\beta_0})\). Expanding the product of the two \(s\)-edge bounds gives the log-small main \(O(xL^{1-K})\) and total floor costs \(O(x^{1-\alpha_0}L+x^{1-\beta_0+\alpha_1}+x^{1-\beta_0})\), all power-small.
Divisor moments pay the actual weights, proving (2)
with the maxima taken separately at every \(G\).

In particular take
\[
 [\alpha_0,\alpha_1]=[.1388,.1392],\quad
 [\beta_0,\beta_1]=[.429,.432],\quad
             f=1\text{ through }.346,\quad
             f=0\text{ from }.348 .
\]
Then \(s d\le x^{.4872}\) with fixed margin and all
five near-equal true \(q\)-prime exponents near .1722
give exactly \(D_f(q)=6\).
This includes the literal adverse support of the earlier
balanced favorable-rank-six reflected rows, though
the detector on the unclassified complement is now
the shorter \(f\). It is not an assertion for their
old much longer near-half cutoff.
On a \(G\)-only favorable profile (the five true factors
for \(G\) in the earlier rank-six row, for example),
choose the \(p\)-window so the actual \(F(pG)<0\).
Define \(A_G\) as adverse composite mass with weight \((-F)W_sD_f\) on \(D_f>0\), and \(B_G\) as favorable composite mass with weight \((-F)W_s(-D_f)\) on \(D_f<0\). Let \(P_G\) be the actual positive \((-F)W_s\) mass on true prime \(q\); for such a prime \(D_f(q)=1\) since \(q>x^u\).
Then on any selected rectangles
\[
               \sum_G \sup |B_G-A_G-P_G|
                                     \ll_A xL^{-A}.
\]
This is a genuine fixed-target balance across **different
physical \(n\)** in each cofactor line, in averaged
absolute norm across the cofactors; no same-\(n\) marker
reversal is required. In particular the adverse part is
paid by favorable composite terms up to the displayed
small error on these rows. In the explicit near-equal five-factor chamber only \(s\) itself lies in the short-marker band, so no same-\(n\) alternative marker contributes for those adverse terms. The strict reserve remains
precisely the actual prime-\(q\) contribution \(P_G\).
A nontrivial uniform positive lower for that reserve,
or a bound closing all the other Goldbach rows, is not
proved by this arithmetic transfer.

## Comparison

The [previous same-integer orientation rigidity](CompleteNearHalfOrientationRigidity.md)
concerns a canonical near-half sum and compares only markers of one integer.
The [previous full-scale convolution applications](FullScaleConvolutionBV.md)
do not freeze and retain the whole original reflected coefficient against an
arbitrary cofactor mask. [Pham, October 2026 v1, Appendix D](https://www.preprints.org/manuscript/202610.3061)
instead treats overlapping-row rough benchmarks; his [November 2026 restricted
Chen sieve](https://www.preprints.org/manuscript/202611.0694) uses different
coefficient supports. [Arneth's October 2026 signed architecture](https://zenodo.org/records/23504447)
likewise does not provide a strict surplus for the balance here. The
result uses ordinary distribution only below the square-root level and
makes no claim of priority or of an unconditional prime lower bound.
