# A genuine positive signed cohort inside the wide no-high covariance

Use the exact notation of
[WideLowNoHighRemainder](WideLowNoHighRemainder.md). In particular
\(J\Subset(0,1)\) is fixed, \(N\) is any sufficiently large even
target, \(M=|J|N\mathfrak S(N)\), and all pairs \(x+y=N\) retained
have \(x\in NJ\), \((x,N)=1\). The unaltered profile is
\(F(t)=(1+kt)C(t)\), \(k=1/(1-\lambda)\), \(\lambda=.006\);
\(C=1\) through .486 and \(C=0\) from .490. Keep \(v=.498\),
\(w=.499\), \(\rho=.518\), and the smooth choice of \(B\) from
that theorem: the cutoff \(\chi(\log(rd)/L)\) equals 1 through
.4985, 0 from .499, and lies in \([0,1]\). The actual remainder
\(T=\mathcal L-B=P+E-B\) uses this same cutoff, not a
different comparison profile. Let
\[
       H_\chi=.4985+\int_{.4985}^{.499}\chi(t)\,dt,\qquad
       \beta_\chi=1-k(H_\chi-v)>.9989.                           \tag{1}
\]

**Theorem.** Fix sufficiently short nondegenerate intervals
\(\mathcal I_1,\mathcal I_2\) in \((.001,.006)\), separated by
a positive gap, with their upper endpoints summing to less than
\(.012\). They specify actual prime banks
\(\mathcal P_i=\{p:\log p/L\in\mathcal I_i,\ p\ {\rm prime}\}\).
Put
\[
 \nu_i(n)=\#\{p\mid n:p\in\mathcal P_i\},\qquad
 W(n)=\nu_1(n)\nu_2(n),\qquad
 V_i=\int_{\mathcal I_i}\frac{dt}{t}.
\]
Then the actual weighted signed block satisfies
\[
 \sum_{\substack{x\in NJ\\(x,N)=1}}W(x)W(y)T(x)T(y)
       =\beta_\chi^2 V_1^2 V_2^2 M+o(M).                         \tag{2}
\]
For banks of sufficiently small fixed reciprocal widths around
any two distinct fixed points of \((.001,.006)\), with widths
then held fixed as \(N\to\infty\), there is a literal unweighted
cohort of the same score:
\[
 \sum_{\substack{x\in NJ,\,(x,N)=1\\
           \nu_1(x),\nu_2(x),\nu_1(y),\nu_2(y)\ge1}}T(x)T(y)
       \ \ge\ \tfrac12\beta_\chi^2 V_1^2V_2^2 M                 \tag{3}
\]
for all sufficiently large even \(N\).
The entire signed score on the displayed physical cohort is used.
Every nonzero summand belongs to the original no-high-by-no-high
remainder, because \(T\) is zero on a high-containing integer.
These estimates do not sign the complement and do not by
themselves control \(\langle T,T\rangle_J\).
The derivative of the **actual product cap** is essential to
the order-one coefficient in (1).

## 1. Exact tagged regrouping

Open \(W(x),W(y)\) by the true labels \(h_1=p_1 p_2\mid x\)
and \(h_2=q_1 q_2\mid y\), one prime in each bank on each side.
All labels are actual distinct primes on a given side; \((h_1,h_2)=1\)
and all labels are target units on a contributing row. Each size
is \(\le N^{.012}\). The at most fixed number of labels per integer
comes from the fixed positive left endpoints of the banks.
If any selected prime has valuation at least two in its own
integer, the physical row is lost at power-small cost even
with all score weights: it is among \(O(N^{1-\epsilon})\)
integer multiples of squares of primes \(>N^\epsilon\), and
divisor weights are \(N^{o(1)}\). Here \(\epsilon>0\) is any
fixed lower bound on the banks' exponents.

Since the row has two different such prime factors on each arm,
\(\Pi(x)=\Pi(y)=E(x)=E(y)=0\) exactly. For \(E\), an actual
high prime \(>N^\rho\) is distinct from both tags, so its
cofactor cannot be a prime power. With \(A=A_F\) from
WideLowNoHighRemainder, \(T=A-B\) on these rows up to the
proper-power exceptions of that theorem. They remain power-small
with the tag weights by the same divisor bound.

At fixed \(h=p_1p_2\) write \(n=hm\) on its own arm. Each
old divisor \(d\) of \(n\), or of \(n/r\) in \(B\), is
\(a d'\), \(a\mid h\), \((d',h)=1\), with \(\mu(d)=\mu(a)\mu(d')\).
All selected primes satisfy \(p_i<U\), and \(r>U\) for \(B\),
so \(r\) is never a selected prime. In \(A\), the braces
\(\log(n/d)-\sum_{j\mid n/d,\,j\le U}\Lambda(j)\) are unchanged
by the remaining once-occurring selected factors \(h/a\):
their free log exactly equals their short prime mark.
Thus the left/right exact shifted \(A\)-profile is
\[
 F_h(t)=\sum_{a\mid h}\mu(a)F(t+\log a/L)
\]
multiplying the original log-minus-short-mark braces on \(m/d'\).
The latter short \(j\)'s can be restricted by \((j,h)=1\).
In \(B\) the \(a\)-summand is
\[
  (\log r)\mu(a)\mu(d')F(t_{d'}(n)+\log a/L)
            \chi(\log(rd')/L+\log a/L),
 \qquad rd'\mid m.
\]
Both descriptions can be extended artificially to \(m\) not
coprime to \(h\), *retaining* the displayed \((d',h)=1\) and
\((j,h)=1\) masks. Artificial and physical scores then differ
only on the already paid tag-square rows, and their bounded
divisor-weight envelopes also pay the artificial values there.
In particular no inclusion of \(p_i^2\) in a modulus is necessary.

## 2. True product-modulus comparison and exact first moments

On each arm group the **entire** physical product modulus before
Poisson, as in [WideGroupedMarkCovariance](WideGroupedMarkCovariance.md).
For \(A\) it is \(h d'\) or \(h d'j\), at most
\(N^{.012+.490+.006}=N^{.508}\); the upper bound follows already
from the support before opening the shifted profiles.
For \(B\) it is \(h r d'\), at most \(N^{.012+.499}=N^{.511}\)
from the genuine cap, whether or not \(a\mid h\) is present in
the old divisor. Do not use \(ha rd'\). The tag is part of
the actual modulus, not a new outer count. Its choices,
subsets and genuine mark representations for a fixed modulus
have divisor-power multiplicity. The shifted profile Fourier
factors for \(d'\) and \(a\) attach to the coefficient, while
the spatial phase in \(n/N\) is common. The cutoff factors
independent of the spatial parameter attach to the same
coefficient. Free logs split into their common spatial log
and their independent divisor log. All coefficients satisfy
the corresponding \(L^{O(1)}\tau(q)^{O(1)}\) bound. The exact
same grouped Poisson/Bettin--Chandee calculation in the
cited proof, whose two actual moduli may be as large as
\(N^{.515}\), makes all nonzero terms power-small. In particular
this is valid for the global sum over the actual four tags
as well as the smaller power rails just specified. The true
target-unit CRT principal is averaged with the same
\(\varphi(N)/N\) and with \((q_1,q_2)=1\).
The real spatial interval is handled by the fixed-scale
Mellin smoothing of that proof.

Only in the principal, fix both tag products and the two
actual mark labels (or unmarked free-log terms). Complete
the signed \(d',e'\) tails successively at
\(S=\exp((\log L)^4)\), with true polynomial opposite masks
times the own tag factors, by the masked \(\mu(d')/d'\)
harmonic. The cutoff \(\chi\) has bounded fixed variation,
so causes no extra difficulty. This is the calculation in
[JointGiantEndpointDerivative, §2](JointGiantEndpointDerivative.md);
higher signed moments on the resulting box are
\((\log L)^{O(1)}\). The model zeroth moments vanish whenever
either coordinate's log-moment degree is zero, including
opposite tag masks. In the first/first coefficient the CRT
density is
\[
  \frac{\mathfrak S(N)}{h_1h_2}\,
      \prod_{p\mid h_1h_2}\frac{p}{p-2}
\]
before mark denominators and their appropriate further local
\(c(\cdot)\) factors at unshared primes. Each tag is omitted
from both Möbius variables, by an own unit mask and the
opposite modulus; hence it has ratio \(p/(p-2)\), not
\((p-1)/(p-2)\). This tag ratio is \(1+o(1)\) uniformly.
The \(B\)-marks \(r>U\) never equal any tag and their
\(c(r)=1+O(1/r)\). Compatible repeated labels on the
same arm impose no extra mask beyond those displayed.
An opposite common mark in \(B\times B\) is incompatible
and has a power-small reciprocal model. The tag diagonals
between the arms are already excluded by true units; after
completion their omission costs at most a fixed log power
times \(\sum_{p>N^\epsilon}1/p^2\). Absolute tag harmonics
are bounded, so all these estimates aggregate directly.

On \(d'\le S\) the \(A\)-profile \(F_h(t_{d'}(n))\) is
identically zero, because all four shifts are in the affine
region and it is a second difference. The entire CRT
model of any \(A\) leg therefore vanishes to arbitrary
log accuracy. On a \(B\)-leg, for \(s=\log r/L\) and
\(u=\log a/L\), the first-log coefficient before its
positive mark and the sign \(\mu(a)\) is \(1/L\) times
\[
        k\chi(s+u)+(1+ku)\chi'(s+u)+O_J(1/L).                   \tag{4}
\]
Here the derivative of the cap arises from the exact
\(rd'\)-dependence, and its argument has no extra
\(n/N\) shift. The true bounded spatial shift of \(F\)
accounts for only the stated error. Higher terms after
Taylor expansion are \(o(M)\), using the zeta zeros, the
fixed Schwartz seminorms, the signed higher harmonic
bounds, and two external \(\log r\)-harmonics \(O(L)\).

The true prime harmonic in \(r\), with \((r,N)=1\) and
any extra nonshared mark masks, integrates (4) on
\(s\in(\lambda,v]\), by PNT and partial summation.
For \(u=0\) its integral times \(L\) before the \(1/L\)
prefactor is \(k\Delta L\). For every nonempty selected
subset one has \(u>.001\), \(\lambda+u<.4985\) and
\(v+u>.499\). Consequently the normalized integrated
coefficient for that shift is exactly
\[
        k(H_\chi-\lambda-u)-(1+ku).
\]
This is affine in \(u\) on the nonempty shifts.
The signed sum over the four shifts is
\(k(v-\lambda)-[k(H_\chi-\lambda)-1]=\beta_\chi\).
For \(A-B\) it is \(-\beta_\chi\) on each side; the two
signs multiply positively. Finally the actual two-label
prime harmonic on one arm is \(V_1 V_2+o(1)\); omitting
target primes and the cross-arm collisions costs a power.
This proves (2) on the genuine fixed target. The same
calculation would give the same \(\beta_\chi\) for any
fixed tag cardinality at least two, all tags in \((.001,.006)\)
and total tag exponent at most .012: the affine function
of the nonempty shifts is annihilated by the full
higher finite difference as well.

## 3. Literal unweighted cohort

Let \(I(n)=1_{\nu_1(n),\nu_2(n)\ge1}\).
For actual nonnegative integer counts,
\(0\le W-I\le \binom{\nu_1}{2}\nu_2+
                 \nu_1\binom{\nu_2}{2}\).
(The inequality for two positive counts follows from
\(a b-1\le a b(a+b-2)/2\); a zero count is immediate.)
Thus \(0\le W(x)W(y)-I(x)I(y)\) is at most the sum of
four positive types of **five true distinct tags**:
three on one arm, two on the other. On actual target
units their prime sets between arms are disjoint.
For each fixed such pair of tag products \(h_1,h_2\),
\[
 \sum_{\substack{x\in NJ,\,(x,N)=1\\h_1\mid x,\ h_2\mid y}}
       |T(x)T(y)|\ll_{F,\chi,J} \frac{M}{h_1 h_2}.              \tag{5}
\]
Indeed, the smooth-cap Fourier envelope in
[WideNoHighPrimeRankPressure, §3](WideNoHighPrimeRankPressure.md)
and its unconditional two-composite counterpart
[WideJointGiantFiniteAngles, §2](WideJointGiantFiniteAngles.md)
apply after the true tag extraction. Parametrize the
CRT solutions by \(x=h_1(a+h_2 t)\),
\(y=h_2(b-h_1 t)\) with \(h_1a+h_2b=N\).
The interval for \(t\) has size \(\asymp_J N/(h_1h_2)\),
a fixed polynomial in \(N\); take its parameter centered
at a positive dyadic scale of that size, by a translation.
The two remaining forms are primitive since \((N,h_1h_2)=1\).
Their determinant has absolute value \(N\).
At a tag \(p\mid h_1\) or \(p\mid h_2\), only one form
has a root and the other is a nonzero constant. Restore
each original extracted Fourier weight once, replacing
the corresponding residual prime-power weight by 1
on the tagged arm, even when the tag divides twice.
These weights are at most 3, and the local change is
bounded uniformly for this fixed number of macro tags.
At \(p\mid N\) both roots coincide and the target units
exclude that root; all other primes have the two
distinct roots used in that proof. The norm of the
product polynomial in the translated parameter is a
fixed power of \(N\), so the corrected Henriot hypotheses
hold by a fixed small coefficient-size exponent.
This gives the same exact local bound
\(\mathfrak S(N)/L^2\) times polynomial Fourier weights
as for the single-tag proof, uniformly in the true tags.
Schwartz integration absorbs these powers and the two
outer logs in the \(T\) envelopes, proving (5).

Sum (5) over the actual five-tag configurations,
using their genuine positive reciprocal harmonics. It
costs at most
\[
 C_{F,\chi,J}\,V_1^2V_2^2(V_1+V_2)M+o(M).
\]
The constant is independent of the small bank widths
in fixed compact neighborhoods of the chosen two
exponents. Choose the two positive fixed widths small
enough to make this cost strictly less than
\(\frac12\beta_\chi^2 V_1^2 V_2^2 M\) in the limit.
Then (2) yields (3). No estimates on actual four-prime
binary representations, or cancellation between this
cohort and any other, are asserted.
