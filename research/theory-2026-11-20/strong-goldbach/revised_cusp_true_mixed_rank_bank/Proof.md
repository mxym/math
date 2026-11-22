# A genuine rank-five by higher-rank signed bank in the revised cusp

Let \(N=2x\) be even, \(L=\log x\), \(w=1/\log L\),
\(W=x^w\), \(J=xJ_0\) with fixed nonempty \(J_0\subset[1,4/3]\),
and \(M=|J|\mathfrak S(N)\). The sum
\(\langle U,V\rangle=\sum_{n\in J}U(n)V(N-n)\) is **ordered**,
so its two roles are not interchangeable without also reflecting
the window. Write \(\Pi(n)=(\log n)1_{n\ {\rm prime}}\) and
\(\mathcal G=\langle\Pi,\Pi\rangle\).
All scores below are on the actual arguments of this reflection.

Take exactly the revised single-mark amplitude of
[the overmarked reserve](https://github.com/mxym/math/commit/58c66ac9),
\[
 \phi(u)=2u(w_\beta(u)+\kappa v(u))\chi_\delta(u),\qquad
 0<\kappa\le1 .
\]
Here \(w_\beta=0\) through \(\beta\), \(=1\) from \(2\beta\);
\(v=0\) through .25002, \(=1\) from .25008; \(\chi_\delta=1\)
through \(1/2-\delta\), \(=0\) from \(1/2-\delta/2\); all take
values in \([0,1]\). The common \(g_\epsilon\) is a smooth
nonincreasing cutoff equal to one through \(1/2-2\epsilon\),
zero from \(1/2-\epsilon\), \(0<\epsilon<\delta/5\).
On squarefree \(n\), let
\[
 \begin{split}
 F(n)&=\sum_{d\mid n}\mu(d)
       \left|\log d/L-\tfrac12\log n/L\right|,\\
 Z(n)&=-\sum_{d\mid n}\mu(d)g_\epsilon(\log d/L)
                          \sum_{p\mid d}\phi(\log p/L),\\
 K(n)&=L\,1_{P^-(n)>W}\,[F(n)-Z(n)] .
 \end{split}                                                     \tag{1}
\]
We set \(K=0\) on nonsquarefree inputs; on true primes it is
identically zero. The unit mask may be imposed also on both
legs without changing any result, as proved below.

**Bilateral identity.** For any fixed admissible parameters,
uniformly through the even targets,
\[
                        \langle K,K\rangle=\mathcal G+o(M).     \tag{2}
\]
In particular the marked terms do not introduce an extra
reference for this genuine bilinear version of the revised
ledger. This is not a positivity assertion for a reflection
quadratic form.

**Signed bank and its actual complement.** Fix a desired
tolerance \(\eta>0\). After choosing \(\kappa\), take
\(\beta>0\) sufficiently small for the reserve and
\(2\beta<.0496\). Choose a finite constant \(R\) sufficiently
large in terms of \(\eta\), **before** choosing \(\delta>0\)
sufficiently small. Require \(R\delta<\min(\beta,.0005)\),
take \(\chi_\delta\) nonincreasing, and choose
\(\epsilon/\delta\) sufficiently small last.
These choices can be simultaneous with the strict one-leg
reserve in the cited proof. Let \(\mathcal C\) denote the actual
five-prime source with its five ordered log exponents in the
five distinct intervals of radius .0004 around
\[
                           (.050,.177,.215,.267,.291).
\]
Put \(C(n)=K(n)1_{\mathcal C}(n)\) on \(J\) and
\(m_C=|J|^{-1}\sum_{n\in J} C(n)\). This is nonnegative and
\(m_C\) tends to a fixed strictly positive \(m_*\).
Then for all sufficiently large even targets,
\[
 \sum_{\substack{n\in J,\ n\in\mathcal C\\
             b=N-n,\ b\ {\rm squarefree},\ \omega(b)\ge5\\
             x^{\delta/R}<P^-(b)\le x^{R\delta}}}
      K(n)K(b)>[\,2(1+\kappa)-\eta\,]m_C M .                  \tag{3}
\]
Let \(\mathcal B\) denote exactly the opposite-side
rank and least-factor restriction in (3). With the **same
source** \(C\), one also has
\[
 \langle C,K\rangle
        = 2m_C M-\langle C,\Pi\rangle+o(M),\qquad
 \langle C,K1_{\mathcal B^c}\rangle
        \le -(2\kappa-\eta)m_C M-\langle C,\Pi\rangle+o(M).
                                                               \tag{4}
\]
Thus for \(\eta<2\kappa\), a genuine positive bank is
paired with a genuine negative total on its complement.
There are no true primes on either side of (3); the true
prime test in (4) is kept separately. The complementary
mixed row in (4) includes the true low opposite ranks, not
merely high ones. These comparisons do not price the other
ordered quadrants of (2) or the whole higher-rank prime-leg
sum in the one-leg formulation.

## 1. Literal bilateral moving-rough calibration

For \(n\asymp x\) write \(T_n=\log n/L\), \(u_d=\log d/L\), and
\[
 A(n)=L\,1_{P^-(n)>W}\sum_{d\mid n}\mu(d)(T_n-2u_d)_+,\qquad
 B(n)=L\,1_{P^-(n)>W}Z(n).
\]
Use zero on nonsquarefree \(n\). By complementing true divisors,
\[
                           A=\Pi+L\,1_{P^->W}F,
             \qquad K=A-\Pi-B.                               \tag{5}
\]
Indeed for even squarefree rank the two complementary terms
of the absolute cusp are equal and their short representative
has value \(T_n-2u_d\). For odd rank \(\ge3\), the sum of the
short hinge is half the full alternating linear term, hence
zero. A true prime contributes \(\log n\) at its unit divisor.
All true primes here exceed \(W\).

We first show for \(U,V\in\{A,B\}\)
\[
 \frac{\langle A,A\rangle}{M}=4+o(1),\qquad
 \frac{\langle A,B\rangle}{M}=\frac{\langle B,A\rangle}{M}
                           =\frac{\langle B,B\rangle}{M}=o(1).
                                                               \tag{6}
\]
The joint sieve is for both literal roughness conditions.
We give the near-root arithmetic as it matters for the
mixed and marked tests.

**Squarefreeness and units.** In all expanded weights the
pointwise magnitude is bounded by fixed divisor powers times
a fixed power of \(L\). A squareful \(W\)-rough input has a
prime square \(p^2\mid n\), \(p>W\), so its total number is
\(O(x/W+\sqrt x)\). A \(W\)-rough input sharing a prime
with \(N\) must share a prime \(p>W\); its count is
\(O(x L/W+L)\). Cauchy with the usual fixed divisor moments
on the two affine arguments (or Hölder applied separately
to the two ordinary divisor moments) makes these deletions
smaller than any requested power of \(L\), relative to \(M\).
We can therefore first omit all unit and squarefree
conditions on the physical rough row, and insist instead
on \((de,N)=1\) for the opened divisors \(d,e\); in the
physical rough sum the latter changes only the already paid
nonunits. Then \((d,e)>1\) gives no row, since a common
prime must divide \(N\). We do not drop a true unit restriction
from a truncated rough model without this physical step.

**Joint signed CRT.** After opening each rough divisor let
\(E=x^{.001}\). The joint upper and lower dimension-two
sieve at this level uses the **same** squarefree label \(h\)
for the union of \(p\mid n\) or \(p\mid N-n\) over \(p\le W\).
There are two residues if \(p\nmid N\), one if \(p\mid N\)
(including 2). Since \(d,e\) are \(W\)-rough, no \(p\le W\)
divides them. For each \(h\) assign its primes to their
actual sides; a prime of \(N\) is assigned left only
since its two labels coincide. Thus \(h=h_1h_2\)
and the resulting congruences are
\[
        n=0\bmod b,\quad n=N\bmod c,\qquad
        b=d h_1,\quad c=e h_2,\quad (b,c)=1,\quad(c,N)=1 .
\]
The test \((c,N)=1\) includes the original \((e,N)=1\);
\(b\) may contain the assigned primes of \(N\).
These are the only gcd cases. There are at most
\(2^{\omega(h)}\) allocations. For each actual allocation
the two extended coefficient sequences are independent
and bounded by \(L^C\) times fixed divisor powers; for the
mark even the sum of the nonnegative amplitudes on any
one divisor is bounded, since \(\sum_{p\mid d}u_p\le u_d\).

Here the two original divisor supports may go all the
way to \(\sqrt{C x}\) with a fixed constant \(C\).
In particular neither cutoff is shortened by the sieve
width. With \(b,c\ll x^{.501}\), the phase after Poisson
in a common smooth central window \(V_0(n/x)\) is
\(e(N j\bar b/c)\) and its zero mode is
\(x\widehat V_0(0)/(bc)\). This is the genuine determinant
phase, not separate CRT floors beyond the product level.
We use the [Bettin--Chandee theorem](https://arxiv.org/abs/1502.00769)
in the [signed CRT form for polynomial allocations](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/PanCriticalCompositePolynomialSieve.md),
as also used in the [native Dickman rectangle law](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/QuadraticLeastFactorDickmanLaw.md).
For clarity, on dyadic \(b\asymp B_0,c\asymp C_0\) of
product \(\mathcal Q\ge x\), the effective frequency is
\(F_0=\mathcal Q/x\) up to a tiny fixed power and log losses.
The outer \(x/\mathcal Q\) and the three square-root
coefficient norms give \(x^{1/2+o(1)}\); the theorem's
\((1+|N|F_0/\mathcal Q)^{1/2}\) factor is bounded up to
that same tiny reserve. Its two remaining terms give
total exponents at most
\[
 .5+.7(.501)+.25(.501)=.97595,\qquad
 .5+.6(.501)+.35(.002+.501)=.97665 .
\]
If \(x^{.99}\le\mathcal Q<x\), keep frequency 1 and the
factor \((1+|N|/\mathcal Q)^{1/2}\): the outer normalized
factor is at most \(x^{.510+o(1)}\) and the two remaining
terms are at most \(x^{.47525+o(1)}\) and
\(x^{.47535+o(1)}\). If \(\mathcal Q<x^{.99}\), the
bounded-variation progression discrepancy \(O(1)\)
per pair suffices. Use the same elementary Mellin
separation of \(\widehat V_0(xj/(bc))\) on the frequency
dyads as in that CRT proof: the smooth common weight has
polylogarithmic seminorms, and the terms beyond the
effective range plus a tiny positive power have arbitrary
power decay. Divisor powers are \(x^{o(1)}\); the allocated
\(\sum_{h\le E}2^{\omega(h)}\ll E\log x\) still leaves
a fixed power saving in all ranges above. A smooth
macroscopic \(J\) cutoff with transitions of width
\(x/L^D\) is restored by Hölder and fixed divisor moments,
with \(D\) chosen large. Both shortened \(J\) endpoints
and all dyad errors are inside the same shape and actual
root cut. No absolute treatment of the nonzero modes
one modulus at a time is used at \(\sqrt{x}\times\sqrt{x}\).

This argument can be applied with arbitrary bounded
independent divisor coefficients, including unsigned
ones. The dimension-two fundamental lemma is used first
on each physical rough count, sandwiching its signed
total with the **unsigned** upper-minus-lower error.
Its relative model error is
\(O(\exp[-c\,u\log u])\), \(u=.001/w\); the dimension
condition is uniform, since the local root counts are
at most two, with at most one at 2. The absolute harmonic
budget on each side is \(O(w^{-1})\) even with the
bounded marked weight. Together with \(w^{-2}\) from
the rough products this makes the normalized error
\(O(w^{-4}\exp[-c\,u\log u])=o(1)\), in addition to the
arithmetic power savings just proved. The valid zero
mode is exactly the product of the two harmonic weights
times the joint local product; at target primes the
coincident-root assignment supplies its proper single
root. Mertens gives that product uniformly as
\((1+o(1))e^{-2\gamma}\mathfrak S(N)/(w^2 L^2)\).
The unit masks on \(d,e\) and their coprimality can be
dropped in the principal at arbitrarily small log
error: mark any common prime by its \(1/p^2\) cost
and target prime \(>W\) by \(O(L/W)\), and pay only
fixed powers of \(1/w\) in the remaining harmonic
sums. This also justifies the signed factorization
of the principal.

**Own-half and moving harmonic.** The preceding CRT
argument with bounded unsigned coefficients gives
\[
 \sum_{n\in J}1_{P^-(n),P^-(N-n)>W}
                       \tau(n)\tau(N-n)\ll M/(w^4L^2)
\]
by the ordinary divisor hyperbola on each side, with
both fixed upper ranges \(\sqrt{Cx}\). Therefore in \(A\)
we may replace \(T_n\) by 1 in the hinge at cost
\(O(M/(w^4L))=o(M)\) in its products with \(A\) or \(B\).
This uses the globally one-Lipschitz positive part, so
also controls every literal divisor crossing the own
square root when the coefficient is frozen. It is
not a prime-source absolute shoulder estimated with a
roughness factor in place of primality. The frozen divisor
coefficients are independent, with support \(u_d\le1/2\).

Here is a uniform moving version of the signed harmonic
calculation. On \(w\le t\le C_1\) with \(C_1\) fixed,
prime Mertens with arbitrary log reserve gives
\[
   \sum_{W<p\le x^t}\frac1p
      =\log(t/w)+O_A((wL)^{-A}).
\]
For bounded-variation log tests of a sum of exponents,
compare the prime measure to \(dt/t\) by telescoping
each ordered product factor, then divide by the rank
factorial. The total error costs only a fixed power of
\(1/w\): each unsigned measure has total mass
\(\log(C_1/w)+O(1)\), so the factorial exponential
and its first derivative are \(O(1/w)\) up to fixed
constants. Prime repeats cost another \(O(1/W)\)
by the reciprocal square sum. This proves the
comparison for all relevant ranks at once (on a fixed
support there can be at most \(C_1/w\) factors).
The limiting measure on the scaled coordinate is the
signed convolution exponential with exponent
\(-1_{t\ge1}\,dt/t\), including its unit atom.
Its Laplace transform is
\(\exp(-\int_1^\infty e^{-zt}dt/t)\).
The transform of its cumulative is this expression
divided by \(z\); differentiating it shows the
cumulative satisfies
\(u\rho(u)=\int_{u-1}^u\rho(t)dt\), with \(\rho=0\)
on negative arguments and \(\rho=1\) on \([0,1]\).
These are the Dickman initial data and recurrence.
The same transform at \(z\downarrow0\) gives
\(\int_0^\infty\rho=e^\gamma\), and the recurrence
gives the factorial tail. Thus the divisor harmonic
measure in the original variable is \(d\rho(t/w)\).
For the linear hinge the normalized harmonic is
\[
 \int (1-2t)_+\,d\rho(t/w)
       =2\int_0^{1/2}\rho(t/w)\,dt
       =2e^\gamma w+o(w),
\]
using the standard \(\int_0^\infty\rho=e^\gamma\)
and its factorial tail. For \(Z\), pin the real
mark \(p\) and write \(d=p k\); the sign becomes
\(-\mu(pk)=\mu(k)\) with \((p,k)=1\).
For every supported \(p\), \(u_p\le1/2-\delta/2\),
and \(g_\epsilon(u_p+t)\) as a test in \(t\)
is flat from zero up to at least
\(\delta/2-2\epsilon>0\). Integration by parts
against \(\rho(t/w)\) gives \(O_A(L^{-A})\)
uniformly in this actual \(p\), since
\(\rho(c/w)\ll \exp[-c'(\log L)\log\log L]\).
The PNT comparison is uniform in those shifted tests,
and the outer mark harmonic is bounded. Thus the
\(Z\) harmonic is \(o(w)\).
These calculations and the preceding CRT product
give (6).

For either orientation the prime--\(A\) term equals
\(2M+o(M)\) by the
[true centered cusp theorem](../true_even_cusp_rank_tail/Proof.md),
or directly by its calibration and own-root collar estimate,
because \(A=\Pi+L F\,1_{P^->W}\). The argument there only
uses central \(n\asymp x\) and \(T_n=1+O(1/L)\);
it applies to \(N-J\) as well, preserving the same length.
In either orientation the prime--\(B\) term is \(o(M)\):
open the actual common roughness by the one-dimensional
sieve at \(x^{\epsilon/2}\) on moduli
\(d\le x^{1/2-\epsilon}\); ordinary BV at the literal
residue \(N\) applies to the entire product.
The same shifted flat harmonic just evaluated gives zero
to arbitrary log reserve; \(1/\varphi(d)\) may replace
\(1/d\) with negligible error on the \(W\)-rough unit
divisors. Its sieve ratio tends to infinity like a constant
times \(\log L\), and the unsigned harmonic error costs
only fixed powers of \(1/w\).
Now expand (5) using (6) and these two prime pairings;
\(4M-2M-2M=0\), giving (2).
Compare [the unmasked bilateral linear-cusp identity](https://github.com/mxym/math/commit/0e7e4c952d8f35448108f3af3b4fc60024877e00):
its divisor cusp is the same, but it has no simultaneous
moving \(W\)-gate or this actual mark. Neither an
unmasked identity nor its prime-only shoulder controls
the masked joint product used here.

## 2. Arithmetic on the squarefree true least-factor band

We now prove (3), without assuming any sign for the
complement of that bank. The five actual exponent boxes
are strictly separated. There are exactly two long
pairs at the displayed center, of labels \((3,5),(4,5)\),
and all subset walls have fixed positive distance from
the half (the smallest such distance at the center is
.006). This persists over the boxes even with the
\(O(1/L)\) own-log difference. For sufficiently small
\(\epsilon,\delta\), the full unweighted mark equals
\(-2T_n\) by the odd-rank sharp formula, while the two
eligible high labels \(4,5\) each have cofactor
short alternating sum \(-1\). For label 4 its eligible
other singles are \(1,2,3\), with the additional pair
\((1,2)\); for label 5 they are just \(1,2\).
No other label gets the excess \(\kappa v\).
Hence this is the literal \(K\) on the source:
\[
          C(n)=2\log n+2\kappa\log(p_4p_5)>0 .
\]
The log weights separate over the genuine short prime
\(p_1\) and the grouped true remaining four-prime
coefficient. PNT in the fifth label, after fixing
the first four, gives a positive ordinary limiting
source mean \(m_*\): for example vary each of the
first four exponents within .00005 of its center,
so the fifth retains a strict band and its central
position interval is proportional. No PNT is
assumed for the reflected partner.

Write \(b=\ell m\) on the actual band
\(x^{\delta/R}<\ell=P^-(b)\le x^{R\delta}\); put
\(s=\log\ell/L\). For the fixed parameters,
\(w<\delta/R\) eventually, so these inputs are already
\(W\)-rough, and are nonprime. Their nonsquarefree
rows cost \(x^{1-\delta/R+o(1)}\) with divisor weights.
Thus \(\ell\) is a genuine distinct bit, and is never
a marked prime in \(Z\), since \(R\delta<\beta\).
Replacing \(T_b\) by 1 in \(A\) here is harmless:
the pointwise score error is \(O_\delta(1)\),
and the genuine source is polynomially rough.
The elementary dimension-two upper sieve on the two
integers at a fixed sufficiently small exponent
depending on \(\delta\) counts \(O_\delta(M/L^2)\)
such pairs. Times \(C(n)\ll L\) the error is \(o(M)\).
No arbitrary-log estimate on a sharp cusp is needed here.

Now \(f(u)=(1-2u)_+\). The actual \(\ell\)-bit difference
in \(A\) is
\[
 L\sum_{d\mid m}\mu(d)[f(u_d)-f(u_d+s)] .
\]
In \(B\) the mark is \(p\mid m\), \(p\ne\ell\), and
its actual difference is
\[
 L\sum_{p\mid m}\phi(u_p)
       \sum_{d\mid m/p}\mu(d)
          [g_\epsilon(u_p+u_d)-g_\epsilon(u_p+u_d+s)] .
                                                               \tag{7}
\]
All \(d\) in these formulas may be restricted to have
least prime \(>\ell\), exactly. To express the least
label condition, sieve \(m\) at primes \(\le\ell\)
on the actual progression, omitting \(p\mid N\) and
\(\ell\). The latter omission only adds the paid
\(\ell^2\mid b\) rows; use their divisor-weighted
absolute power loss. The complete moduli are exactly
\(\ell d j\) and \(\ell p d j\) with \(j\) the
quotient sieve label. The four components are pairwise
coprime: the first three are squarefree with the
coprime bits specified, tests in \(j\) exclude \(\ell\)
and are below the remaining factor sizes. When
bounds are applied before squarefree restoration,
\(p\mid d\) would force \(p^2\mid b\), which is
again power-small, since \(p\ge x^\beta\).
Target nonunits are either genuinely impossible or
removed before the estimates; primes of the source
cannot divide \(\ell\) or \(j\).
Preserve \(\ell,p,d\) in the true moduli, not approximated
size labels.

Take the one-dimensional upper and lower fundamental
lemma at \(j\le x^{.008}\) and apply
[Fouvry, Autour du théorème de Bombieri--Vinogradov II,
Corollary 1, pp. 619--620](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf)
to each sign choice of the resulting divisor-bounded
modulus coefficient. The literal \(\ell p d j\)
is \(\le x^{.508+R\delta+o(1)}\), since the nonzero
marked test has \(p d\le x^{.5-\epsilon}\).
The unmarked \(d\le\sqrt x\) satisfies the same bound.
Recall \(R\delta<.0005\).
In Fouvry's source notation the short \(U_1\) is
the **genuine source prime \(p_1\)** in
\([x^{.0496},x^{.0504}]\).
The level conditions (with a fixed small margin)
are
\[
 QX^\eta<
   \min(X^{1/2}U_1^{1/2},X^{4/7}U_1^{-6/7}),
                    \qquad X=4U_1 U_2,\quad |a|\le X .
\]
Here \(\eta>0\) is a sufficiently small fixed power reserve and \(U_2\) is the actual length of the grouped
four-prime source. The exponents on the right are
at least .5248 and \(4/7-6(.0504)/7>.5282\).
Split the two source slots into independent relative
log-fine boxes with \(U_1U_2=(1+o(1))n\) on the
retained boxes in \(J\). Thus \(X>2x=N\) and
the actual residue \(a=N\) is legal, not presumed
fixed as a small integer. Fouvry requires (1.3) on
the short coefficient. Standard prime-prefix
Siegel--Walfisz, the trivial \(O(U_1/q+1)\)
bound beyond a chosen log-power conductor and
deleting prime factors from an auxiliary unit mask
give (1.3) for the actual prime slot, with partial
summation for its log weight; this is the same
check as in
[the true quadratic least-factor bank](../QuadraticLeastFactorReserve.md).
The long coefficient is a fixed-order genuine prime
convolution, with no SW condition needed on it.
Fine product boxes for the central endpoint only
lose \(O(xL^{-D}+x^{.051})\) integer pairs before
divisor weights (first fix the true short slot);
ordinary divisor moments and an arbitrarily fine
log mesh pay both actual and principal endpoint
terms. All other outer coefficients, including
the signed sieve and marked log weights, are
arbitrary fixed-order coefficients of the modulus
for each sign split, with reconstruction cost
at most \(\tau(Q)^{O(1)}\).
The theorem is applied once for the whole aggregate
in the relevant source box, not separately with
a new error for every \(\ell,p,d\).
These hypotheses give arbitrary log accuracy in the
centered progressions at the actual target.

For precision, sandwich each signed physical sum by
the model with the **absolute** upper-minus-lower
sieve bill. The dimension-one product at
\(\ell=x^s\) is
\[
       V_N(\ell)=(1+o(1))e^{-\gamma}\mathfrak S(N)/(sL).
\]
Deleting target primes or the single marked \(\ell\)
changes its model only as described; source primes
exceed the presieve cutoff. The remaining model
denominators are \(\varphi(\ell)\varphi(d)\)
and \(\varphi(\ell)\varphi(p)\varphi(d)\).
If a prime of the true source or of \(N\) shares
a \(d,p\) factor, the exact reduced-class model
omits that row. The omission in the normalized
harmonics costs \(o(1)\) uniformly on the current
polynomial rough profiles by the large reciprocal
prime bound; in the target case there are only
\(O(L)\) possible target primes, and in the source
case just five. The signed \(d\) measures converge
to \(d\rho(u_d/s)\) uniformly over the fixed interval
\(s\in[\delta/R,R\delta]\), by the same prime-factor
expansion as in §1 (here only finitely many
ranks are involved at each fixed \(\delta\)).
The unsigned \(d\) harmonic is \(O(1/s)\), and the
unsigned \(p\) harmonic needs only \(O_\beta(1)\).
The normalized model bill from using the rough
sieve with ratio \(u=.008/s\) is consequently
\[
                  O_\beta(s^{-2}\exp[-c u\log u])
\]
per unit harmonic weight of \(\ell\), plus
\(o_{N;\beta,\delta,\epsilon}(1)\) after the
arithmetic errors. This explicitly pays both
(7) and the unmarked contribution; a qualitative
ordinary density of least factors is not substituted.

## 3. The actual favorable signed main and exclusion of low ranks

In the tested \(\ell\) band the true prime is absent,
so \(K=A-B\). The preceding calculation shows that,
in units \(m_C M/\varphi(\ell)\), its multiplier is
the following difference, with the signed sieve
error just bounded:
\[
 \begin{split}
 {\sf A}(s)&=\frac{e^{-\gamma}}{s}
       \int [f(t)-f(t+s)]\,d\rho(t/s),\\
 {\sf B}(s)&=\frac{e^{-\gamma}}{s}\int_\beta^{1/2}
        \frac{\phi(v)}v
           \int[g_\epsilon(v+t)-g_\epsilon(v+t+s)]
                  \,d\rho(t/s)\,dv .
 \end{split}                                                    \tag{8}
\]
This is an aggregate formula: the \(o(1)\) progression
error is summed over all \(\ell\) by Fouvry, rather than
claimed uniformly for individual prime moduli.
The exact \(\ell\) harmonic multiplier is
\(1/\varphi(\ell)\), from its actual prime tag.
Mertens over the true band gives
\(\sum_\ell1/\varphi(\ell)=2\log R+o(1)\).
For the bounded-variation functions of \(s\) at fixed
parameters in the ensuing model, the same prime
Mertens step integrates them against \(ds/s\).
Partial integration shows \({\sf A}(s)\ge0\):
it equals
\((2e^{-\gamma}/s)\int_{1/2-s}^{1/2}\rho(t/s)\,dt\).

For \({\sf B}\), first take the sharp global half cutoff.
Put \(h=1/2-v\) and
\(D_s(h)=\rho(h/s)-\rho(h/s-1)\), with negative-argument
values zero. This is the exact inner difference,
including its positive unit-atom window \(0<h<s\).
The uncut integral of \(D_s\) over \(h\ge0\) is zero by
translation, and the part with \(h\) at least .24
has total absolute integral \(O(s\,\mathcal E(s))\),
where \(\mathcal E(s)\to0\) faster than powers of \(s\),
by Dickman decay. For \(v\ge .251\),
\(\phi(v)/v=2(1+\kappa)\chi_\delta(v)\);
the other amplitudes are bounded and lie in that
exponentially small tail. The missing part of the monotone top taper is a probability
mixture of indicators \(1_{0<h<t_0}\) with
\(t_0\in[\delta/2,\delta]\). Write \(d\nu(t_0)\) for this
mixture. For the extended Dickman function,
\[
 \int_0^{t_0}D_s(h)\,dh
        =s\int_{t_0/s-1}^{t_0/s}\rho(v)\,dv
        =t_0\rho(t_0/s).                                    \tag{9}
\]
This includes \(t_0/s<1\): the lower endpoint lies
below zero, and the integral is then just \(t_0/s\).
Since the full uncut integral of \(D_s\) is zero,
the sharp value of the **negative** mark multiplier is
\[
 -{\sf B}(s)
     = 2(1+\kappa)e^{-\gamma}
          \int \frac{t_0}{s}\rho(t_0/s)\,d\nu(t_0)
             +O(\mathcal E(s)).
                                                               \tag{10}
\]
Restore the actual \(g_\epsilon\) by its positive mixture
of sharp half-shifts \(c\in[\epsilon,2\epsilon]\).
These translate \(D_s(h)\) to \(D_s(h-c)\), and
\(\|D_s(\cdot-c)-D_s\|_1\le4|c|\) since the
extended Dickman cumulative has variation two.
This costs \(O(\epsilon/s)\) in (10).
The unmarked hinge multiplier is nonnegative, in fact
\(O(\rho(1/(2s)-1))\), so contributes no negative
debit. The error in (10), including the actual sieve
error, is \(o_{\delta\downarrow0;R,\beta}(1)+O_R(\epsilon/\delta)\)
after integration over \(s\in[\delta/R,R\delta]\)
in the \(ds/s\) harmonic measure.

The main for a fixed mixture endpoint \(t_0\), before
multiplying by \(2(1+\kappa)e^{-\gamma}\), is exactly
\[
 \int_{\delta/R}^{R\delta}\frac{t_0}{s}\rho(t_0/s)\frac{ds}{s}
       =\int_{t_0/(R\delta)}^{R t_0/\delta}\rho(v)\,dv
       \ \ge \int_{1/R}^{R/2}\rho(v)\,dv .                      \tag{11}
\]
The last integral tends to \(e^\gamma\) as \(R\to\infty\),
uniformly in every \(t_0/\delta\in[1/2,1]\);
the part below \(1/R\) is exactly \(1/R\), and the
upper missing tail is factorial. Thus the main in the
actual signed bank can be made greater than
\([2(1+\kappa)-\eta/3]m_C M\) by taking \(R\) first,
then fixing sufficiently small \(\delta\) and
\(\epsilon/\delta\), then \(N\) large. No sum over a
growing number of independent sieve calibrations is used:
the complete marked \(s\) range is evaluated in the same
Fouvry modulus sum.

Finally, restricting to the literal opposite rank
\(\ge5\) must remove its lower-rank *positive* terms,
not just assume every row is composite high rank.
Rank three is nonpositive for the revised \(K\),
as in the one-mark rank check, which uses only
nonnegative amplitudes. On rank two with this
least label neither it nor the giant is marked,
and \(0<K/L=2s=O_R(\delta)\).
For this true source \(C\), the same elementary upper
is available: fix the actual short factor of the
opposite rank-two input, and sieve in its other
prime and the reflected \(C\)-argument, which is
necessarily \(x^{.049}\)-rough. A fixed two-form
upper sieve in the free prime and affine form gives
\(O(M/(\ell L^2))\) per \(\ell\), with the true
singular factor and bounded slope correction.
This costs \(O_R(\delta M)\) over the full bank,
by the genuine prime harmonic and \(s\le R\delta\).
On rank four the old rank-four sign and the
extra high-mark sign of the overmarked reserve
apply pointwise away from their top and root
fringes. The resulting positive-part wall error
is \(O_\beta((\delta(1+|\log\delta|)^2+
\epsilon(1+|\log\epsilon|)^2)M)\) also
**against this actual source**, not just against
primes: in the fixed-rank marked-wall proof
fix all but the largest opposite prime and
use the two-form upper in that prime and
the \(x^{.049}\)-rough \(C\)-argument. Every
conditional upper is \(O(M/(H L^2))\)
for the fixed product \(H\) of at most three
actual primes, since the largest prime has
polynomial length and both tests can use fixed
positive rough exponent below .01. The local
slope changes multiply by at most
\(\prod_{p\mid H,\ p>2}(p-1)/(p-2)\le 2^3\);
target primes give the same one-root corrections.
The harmonic wall summations and the least-label
difference of the old rank-four proof are
then unchanged. There is no invocation of a
prime-only estimate for the source \(C\).
These removed positive amounts are \(o_\beta(M)\)
as the fixed parameters shrink, so choose them
with fixed \(R,\beta\) to be smaller than
\((\eta/3)m_* M\), with room for the other errors, to obtain (3).

## 4. The counterbalancing same-source identity

Keep exactly the same true \(C\) and no restriction on the
opposite least prime except the **moving** \(W\)-rough gate
in (1). The actual source geometry of §2 permits Fouvry
on the full short weights \(A,B\): now open just
\(d j\) with \(d\le\sqrt x\) after freezing \(T_b=1\),
and \(j\le x^{.008}\) for the \(W\) presieve.
For \(B\) the mark is inside the coefficient of \(d\le
x^{1/2-\epsilon}\), so no additional modulus factor is
inserted. The same \(p_1\) SW slot gives the old
arbitrary-log discrepancy at actual \(N\);
the total \(.508\) exponent has strict room in its rails.
The normalized sieve error \(O(w^{-2}\exp[-c(.008/w)
\log(.008/w)])\) tends to zero using the unsigned
rough harmonic bound. The squarefree/target-unit
exceptions are negligible by the same physical
rough divisor-moment deletion in §1. We can freeze
\(T_b\) using the positive two-leg \(\tau\times\tau\)
rough upper from §1, since the real source \(C\)
is \(W\)-rough and \(C\ll L\), leaving \(o(M)\).

For the exact reduced-class model exclude the real
unit primes of \(n,N\); their differences in the
\(W\)-rough harmonic are negligible after the sum
over source profiles just as before. The other
argument's density is \(V_N(W)\sim
e^{-\gamma}\mathfrak S(N)/(wL)\). The linear
harmonic is \(2e^\gamma w+o(w)\), and the mark
harmonic is \(o(w)\), from the moving-calibration
proof in §1. Hence \(\langle C,A-B\rangle
=2m_C M+o(M)\) at the actual fixed target. By
(5), \(K=A-B-\Pi\), giving the first assertion
of (4) without evaluating the genuine
\(\langle C,\Pi\rangle\).
Subtract (3) on the **same** row to get the
second assertion. In particular the resulting
negative complement is not an independently
spendable negative term in a different
normalization.

## Scope

The positive sign in (3) depends on the actual upper
mark taper: its positive \(\ell\)-conditional strip
is absent, leaving the other pieces in (9).
It is not a rank-five count with a randomized prime
leg, and it is not a lower bound for whole high by high.
It is one ordered subregion of the revised bilinear
identity (2). The other high-by-high profiles,
the rank-\(\le4\) by high and high by rank-\(\le4\)
rectangles, and the total of all remaining terms
retain their true signs; none is bounded below here.
The original one-leg signed sum against \(\Pi\) is
likewise not bounded by (3). Compare
[the older native quadratic least-factor bank](../QuadraticLeastFactorReserve.md), which uses its
quadratic finite-difference slope against a different
actual source. Here the linear hinge difference is
negligible and the margin comes from the **literal
one-mark top taper** against a true rank-five source
of the revised score.

The [older five-prime counted bank](../native_counted_bank/Proof.md) also keeps a literal rank-five source, but for the original quadratic score and a medium-factor occupancy split, not the present linear taper and its actual complement.

The [exact checker](check.py) checks the box, bit identities,
Fouvry and bilateral CRT power margins, and numerical signed margin.
