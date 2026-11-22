# The whole signed bank-covered part of the polynomial native identity

Use the literal even target, fixed-gap interval \(I\), cutoffs
\(U_x,W_x,U_r,W_r\), and physical score of [PolynomialNative.md](PolynomialNative.md).
In addition suppose \(\operatorname{rad}(N)\le L^{B_0}\) for a fixed \(B_0>0\).
No such assumption is needed in that file's underlying calibration.

For every requested fixed \(D>0\), choose a sufficiently large fixed
\(K\ge2\), and \(s_0\asymp_K\log L\) disjoint admissible \(K\)-color banks
of subpower primes as in [the reflected comparison](../small_radical_reflected_chowla/Proof.md).
They may be chosen so that each color has reciprocal mass bounded above
and away from zero and every prime lies between \(\exp(cL^{.1})\) and
\(\exp(2L^{.2})\), with the independent ranges and within-family separation
of that comparison. Choose \(s_0\le \lfloor\log L\rfloor\) explicitly, still
with \(s_0\gg_K\log L\), by taking only the indicated number of
families in the separated construction. Write \(A_j(A)\) for avoidance by \(A\) of the entire
bank \(j\), and \(C_j(C)\) for the event that \(C\) has a prime divisor
in **each** color of bank \(j\). Define the literal covered condition
\[
 \mathcal E(A,C)=1-\prod_{1\le j\le s_0}(1-A_j(A)C_j(C)).
\]

**Theorem.** Multiplying the signed native sum (2) of
[PolynomialNative.md](PolynomialNative.md) by \(\mathcal E(A,C)\) makes
it \(O_D(NL^{-D})\), with the fixed cutoff exponents and \(B_0,J_0\) as
additional dependencies. This holds on the **entire** physical fixed-gap
domain, including polynomial \(m\), with no condition on the relative
sizes of \(A(mC)\) or \(fh\). The signed native sum on
\(\mathcal E(A,C)=0\) remains. In particular a genuine prime \(C>U_r\)
has \(H_{U_r}(C)=1\) and cannot meet \(K\) disjoint required colors; all
such rows are missed. There is no binary-prime lower bound.

## 1. The exact polynomial native character slot

Let \(U=N^\eta\) with fixed \(\eta>0\). On any actual dyad of scale
\(X\gg U\), allowing a dyad meeting \(U\) as well, take the \(z\)-rough,
target-unit coefficient \(H_U(A)\), with independent avoidance of a
prescribed union of banks. Uniformly on that dyad and in real prefixes,
\[
   \sum_A H_U(A)\,\chi(A)\,1_{P^-(A)>z}
                 1_{\text{prescribed bank avoidance}}
             = O_E(XL^{-E})                                       \tag{1}
\]
for every fixed \(E>0\), for all characters modulo \(M=N b\), \(b\le L^F\)
with \(F\) fixed. The target unit is already imposed by \(\chi\).
Fixed polylogarithmic archimedean twists follow by partial summation.
We retain \(A>U\), since the omitted values are exactly zero.

Fix a small constant \(\delta_0>0\), e.g. \(\eta/4\). When
\(X\ge U N^{\delta_0}\), open the actual \(d\le U\), \(d\mid A\), with
\(\mu(d)\). Both \(d\) and the free factor \(A/d\) must avoid all
specified primes; these primes are \(\le \exp(2L^{.2})\) for large \(N\).
On the free factor open the roughness and all bank omissions with
successive Bonferroni degrees \(\lfloor L^{.1}\rfloor\), omitting
primes of \(M\) already enforced by the character. The total reciprocal
mass of the alphabet is \(O(\log L)\); hence its factorial tails are
arbitrarily log-small. Each opened squarefree \(e\) and the number of
opened terms are \(\exp(O(L^{.3}))\). Counting the positive omitted
degree by \(X/(de)+O(1)\) is permissible: the total floors are
\(U\exp(O(L^{.3}))=X N^{-\delta_0+o(1)}\).
All remaining free intervals have length *scale*
\(X/(de)\ge N^{\delta_0/2}\); the actual prefix inside them may be short.

For a nonprincipal character, use the elementary large-conductor
short-sum input in [the small-radical major proof, §1](../small_radical_projection/Proof.md):
the inducing conductor divides \(M\), has polylogarithmic radical,
and its \(\log\)-size divided by \(\log(X/(de))\) stays bounded.
Short conductors use full periods; for the others Iwaniec's Lemma 6
gives a power saving on the indicated polynomial scale, including
real prefixes. The imprimitive prime mask involves only the
polylogarithmic radical. Sum over \(d,e\) with their reciprocal weights.
For the principal character the ordinary unit-density main factors
as the \(e\)-model times
\[
 \sum_{\substack{d\le U\\ d\ \text{avoids the specified primes}}}
            \frac{\mu(d)}d .
\]
Include primes of \(M\) in the specified primes. This signed harmonic
is \(O_E(L^{-E})\) uniformly. Indeed the series of the coefficients
before division by \(d\) is \(1/\zeta(s)\) times the local inverses
\((1-p^{-s})^{-1}\) at the excluded primes. At
\(\sigma=1-c_1 L^{-.2}\), \(c_1>0\) small and fixed, their absolute
Euler norm is \(L^{O(1)}\), because
\(p^{1-\sigma}\) is bounded throughout the alphabet and
\(\sum_{p\le\exp(2L^{.2})}1/p=O(\log L)\). Split the convolution at
\(\sqrt U\), use true zeta Mertens for the first part and Rankin
for the absolute tail. Partial summation gives the arbitrary-log
tail from \(U\) to infinity and the complete harmonic has value zero.
This proves (1) in the first regime, including all true widths
shorter than a dyad by using the same maximal-prefix bound.

When \(X<U N^{\delta_0}\) instead use the exact complementary identity
\[
        H_U(A)=-\sum_{\substack{d g=A\\d>U}}\mu(d)\qquad(A>1).
\]
At fixed admissible \(g\), the signed factor \(d>U\) now has
polynomial length scale \(X/g\). All avoidance and unit masks split
between \(d,g\). Use the uniform log-saving long \(\mu\)-character
estimate of [the same major proof](../small_radical_projection/Proof.md),
with these extra omitted primes up to \(\exp(2L^{.2})\), and sum only
the reciprocal \(g\)-harmonic. In particular the principal inducing
character is handled there by true Mertens and the same excluded-prime
convolution. This proves (1) also near \(U\); it does not require
intervals of scale \(X/U\) to be polynomial in this regime.

## 2. Actual extraction with a moving short divisor

Freeze the literal \(m\)-interval \(y/m\in I\) and the strict \(d<T_y\)
in \(Q_y(m)\) on a relative central \(y\)-mesh \(L^{-G}\), with \(G\)
large and fixed. For a changed \(m\)-endpoint \(y=mE\) use its actual
multiples \(m\mid y\): for fixed \(m\) the changed strip has at most
\(O(NL^{-G}/m+1)\) values. Summing over \(m\le N^\gamma\) gives
\(O(NL^{1-G}+N^\gamma)\). For \(d<T_y\) use \(y=Bd\) and
\(d\mid m\mid y\) in the same way, \(d\ll S\). The remaining central
cutoff can be smoothed in equally small collars. These errors are
arbitrary-log small by Cauchy and fixed crossed divisor moments on
\(x,y=N-x\). No floor is multiplied by the number of mesh cells in
these global boundary counts. On each cell the residual now sees
fixed \(m\)-interval(s), real smooth product tests, and literal
\(Q_T(m)\) at fixed \(T\).

Discard actual bank-square incidences \(p^2\mid y\) by counting
multiples and fixed crossed divisor moments. This costs arbitrary
log powers since the least bank prime is huge. Use first active
bank \(j\), expanding earlier failures into a log-power number of
separable masks in \(A\) and \(C\). On the left this leaves bank
avoidance only, including avoidance of the entire chosen bank.
On the right extract one actual prime per color from \(C=w C'\).
Use the exact reciprocal hit allocation
\(\prod_\nu(1+\omega_{j,\nu}(C'))^{-1}\), where \(\omega_{j,\nu}\)
counts the distinct prime factors in that color. It multiplies
the sum over all allowable choices of the one tag in that color;
their weights sum to one on each covered row. Earlier hit masks
are unchanged on \(C'\) because the banks are disjoint.
On the retained physical rows square removal ensures
\((w,C')=(w,m)=1\). These restrictions will not be imposed
on the analytic residual after opening the coefficient.

Here the tag primes are **below** the polynomial cutoff \(U_r\).
Consequently the actual remaining coefficient is
\[
   H_{U_r}(w C')=\sum_{s\mid w}\mu(s)
                \sum_{\substack{d\mid C'\\ds\le U_r}}\mu(d),
                                                                    \tag{2}
\]
not \(H_{U_r}(C')\). One may drop the redundant \(C>U_r\) gate
*before* opening (2), because the original \(H\) is zero there.
Approximate just the inequality \(ds\le U_r\) by a smooth
function of \(ds/U_r\), equal to the sharp cutoff outside
\(|\log(ds/U_r)|\le L^{-G}\). Every changed row has the actual
divisor \(ds\mid C\mid y\), within this single fixed vicinity
of \(U_r\). Summing actual multiples over that interval of
integer divisors gives \(O(N(L^{-G}+1/U_r))\); there is no
per-tag boundary charge. All additional absolute multiplicities
are bounded by fixed divisor powers of \(x,y\), with reciprocal
tag allocations summing to one. The boundary error is again
arbitrary-log small by crossed moments.

On the line \(\Re v=1/L\), the Mellin kernel of this short
smooth step has a fixed log-power integral norm, with an
arbitrary-log tail at a sufficiently large fixed power of \(L\).
For example one integration by parts gives
\(\ll |v|^{-1}(1+|\Im v|L^{-G})^{-j}\) for any fixed \(j\),
using further derivatives of the single transition.
After inserting it, \(d^{-v}\) belongs only to the actual
residual divisor coefficient, with \(d\le U_r e^{L^{-G}}\),
and \(U_r^{1/L}\le e^{\eta_r}\) is bounded. The factor \(s^{-v}\)
is a product of bounded prime multipliers
on the selected subset of colors. There are \(2^K\) choices
of that subset, a constant for fixed \(K\). This separation
uses **one** smooth dimension, not a \(K\)-dimensional mesh
whose log powers grow with the required color count.

After this opening restore the removed bank-square rows in
the expanded sum, without any \(w\)-dependent gcd or square
exclusion in the residual. On an artificially restored row
one still has the actual divisor \(w\mid C\mid y\) and
\(p^2\mid y\) for some bank prime. Whether or not the
opened formula equals the unexpanded score there, its absolute
assignments and weights are bounded by fixed divisor powers
of the physical \(x,y\): \(w,s,d\) are all actual divisor
labels and the allocation factors are at most one. The same
actual-multiples and crossed-moment argument makes this restoration
arbitrarily log-small. In particular neither \((w,C')=1\) nor
\((w,m)=1\) is a hidden condition in the separated coefficient.

## 3. The signed covered estimate

On a shell \(w\asymp Y\), the physical equation is
\[
        A f+w n=N,\qquad n=m C'h .
\]
Here \(f\) is a genuine polynomial-sized prime, \(A\) has
the exact signed native weight and avoids the whole chosen
bank, and both are target units. The residual retains the
actual \(h\)-prime weight, all fixed \(m\)-gates and
\(Q_T(m)\), the hit allocation, masks and (2) Mellin
divisor factors. For each Mellin frequency and selected
subset, it is one divisor-bounded coefficient of \(n\):
its absolute value is \(\ll L^C\tau(n)^C\), and its square
norm is \(O((N/Y)L^{O(1)})\). In particular the polynomial
range of \(m\) creates no cardinality loss; these are
literal factorizations of \(n\).

Use the [one-prime comparison, §1](../small_radical_reflected_chowla/Proof.md).
In the projected minor the two physical endpoint gcds
divide the nonzero quotient determinant \(k/N\), of size
\(O(Y)\), since the factors are target units; each gcd has
a genuine \(f\) or \(f'\) argument of polynomial size.
Nonzero determinant follows from complete chosen-bank
avoidance. Thus the same primitive lattice frames apply
without an assumed \(Y\)-roughness condition on \(A\).
The Mellin factor on selected colors is admissible:
[Jiang–Lau–Lü v2, Lemma 6.11 and (6.10)–(6.11)](https://arxiv.org/html/2611.12467v2)
allows those bounded independent entering-label multipliers
in either orientation, also obtainable by assigning them
to the fibre-constant endpoint. Tag product and sign
choices only change those bounded multipliers.

In the full projected major, both original source factors
are \(z\)-rough and target units. At rational arc denominators
\(\le L^F\) the split into literal residue and target-ring
factors is therefore in unit classes (all primes of the
small denominator are below \(z\)). The relevant
character conductors divide \(N b\), \(b\le L^F\) after
increasing the fixed \(F\); their full signed \(A\)-slot
estimate is (1). Off the exceptional tag-character set
use the same full-product Parseval; on it use (1) and
the restricted Bessel estimate on the other true prime
slot. Before the minor clip \(H_{U_x}(A)\) by cutting
at \(\tau(A)\le L^M\) for a sufficiently large fixed
\(M\). The removed physical rows cost arbitrary logs
because \(A\mid x\) and the absolute envelope has fixed
crossed divisor moments. The same clip costs \(XL^{-E}\)
in the linear character estimate by ordinary divisor
moments, so (1) still suffices. Usual smooth packets
retain the genuine \(A f\) products strictly below \(N\).

Use the squared projected comparison and Cauchy against
the stated residual square norm. This gives the required
arbitrary-log bound after summing the log-power number
of physical packets, mesh cells, tag shells, Boolean
earlier-failure patterns and the Mellin norm. All log
exponents in this last budget are fixed independently
of \(K\): the earlier-failure count is at most \(2^{s_0}\le L\),
there are \(O_K(1+L^{.2})\) fixed-ratio tag shells since
\(\log w=O_K(L^{.2})\), and the subset choices cost only the
fixed constant \(2^K\).
Choose all required precision and boundary exponents
first, and then choose the fixed number of colors
for that projected comparison. The omitted bank-square
and cutoff errors have already been paid globally.
This proves the signed cancellation on the full
covered domain, without treating the remaining missed
mass as small.
