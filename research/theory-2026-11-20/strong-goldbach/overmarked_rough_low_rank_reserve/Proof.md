# A true fixed-target reserve on the combined rank-two and rank-three cusp rows

Put \(N=2x\), \(L=\log x\), \(J=xJ_0\) for a fixed nondegenerate
\(J_0\subset[1,4/3]\), \(P=N-y\), and \(M_N=|J|\mathfrak S(N)\)
with the usual Goldbach singular series. Write \(\mathcal G=\mathcal
G_J(N)=\sum_{P+y=N,\ P,y\ {\rm prime},\ y\in J}\log P\log y\).
This note only uses the actual prime \(P=N-y\) on the reflected leg.
Set
\[
 r=.223,\qquad \rho=.2501,\qquad d_0=.555,\qquad
 c_0=\frac{2}{d_0}\log(d_0/r-1)>1.434 .
\]
For squarefree \(y\) use the same linear cusp \(F\) and mark
\(Z_{\phi,g}\) as in the
[true one-mark theorem](https://github.com/mxym/math/commit/45b7095c):
\[
 F(y)=\sum_{d\mid y}\mu(d)\left|\frac{\log d}{L}
                    -\frac{\log y}{2L}\right|,\qquad
 Z_{\phi,g}(y)=-\sum_{d\mid y}\mu(d)g(\log d/L)
                       \sum_{p\mid d}\phi(\log p/L).
\]
Fix \(0<\kappa\le1\). Choose a smooth nondecreasing \(v\in[0,1]\)
zero through .25002 and one from .25008. In the old definition of
the amplitude replace it by
\[
 \phi_\kappa(u)=2u\big(w_\beta(u)+\kappa v(u)\big)\chi_\delta(u).
                                                              \tag{1}
\]
Here \(w_\beta,\chi_\delta,g_\epsilon\) have precisely the old support
and plateau conditions: \(w_\beta=0\) through \(\beta\), \(=1\)
from \(2\beta\); \(\chi_\delta=1\) through \(1/2-\delta\), \(=0\)
from \(1/2-\delta/2\); \(g_\epsilon=1\) through \(1/2-2\epsilon\),
\(=0\) from \(1/2-\epsilon\), and \(0<\epsilon<\delta/5\).
All take values in \([0,1]\), with \(g_\epsilon\) nonincreasing.
After fixing \(\kappa\), one can fix \(\beta,\delta,\epsilon\) so
small that the actual score \(\widetilde F_\kappa=F-Z_{\phi_\kappa,g}\)
satisfies, for all sufficiently large even \(N\),
\[
 \sum_{\substack{y\in J,\ P\ {\rm prime}\\
                 y\ {\rm squarefree},\ P^-(y)>x^{1/\log L}\\
                 2\le\omega(y)\le4}}
       \log P\,L\,\widetilde F_\kappa(y)
 \ \le -.380\kappa M_N + 2\rho\kappa\,\mathcal G .              \tag{2}
\]
Thus at a target with no binary pairs there is a strict negative
reserve in these actual combined low ranks. No lower bound on
rank three separately is needed. The term \(\kappa v\) does not
create a new rank-four charge of natural size. In the full adjusted
identity the precise implication is
\[
 (1+2\rho\kappa)\mathcal G
 \ \ge (2+.380\kappa)M_N
          -\sum_{\substack{y\in J,\ P\ {\rm prime}\\
                 y\ {\rm squarefree},\ P^-(y)>x^{1/\log L}\\
                 \omega(y)\ge5}}
                    \log P\,L\,\widetilde F_\kappa(y)
          -o(M_N).                                            \tag{3}
\]
The rank-\(\ge5\) sum here has the **new amplitude (1)** and is not
bounded by this theorem. In particular it cannot be combined with
the old high-rank costs as if the reserve were free. Section 4
quantifies an adverse marginal change in the angular model.

## 1. A lower sieve on the true shifted-prime source

We first establish the literal lower bound
\[
 \liminf_{\substack{N\to\infty\\2\mid N}}\frac1{M_N}
   \sum_{\substack{y\in J,\ P=N-y\ {\rm prime},\ (y,N)=1\\
                   P^-(y)>x^r}}\log P\,L\ \ge c_0 .         \tag{4}
\]
The source is the genuine prime in \(N-J\), not a product-prime
lower bound. The construction is the classical **lower** Rosser
tree with a small prime bank. We give its sign and distribution
checks because a positive upper weight is not a valid lower
majorant.

Choose a fixed tiny exponent \(b>0\), and a much smaller \(\xi>0\).
On primes \(\le x^\xi\) not dividing \(N\), take lower and upper
fundamental-lemma weights of level \(x^b\), with resulting divisor
sums \(L_s\le U_s\le H_s\), where \(U_s\) is the exact bank-avoidance
indicator. On primes \(x^\xi<p\le z=x^r\) not dividing \(N\),
take classical Rosser lower and upper divisor sums
\(L_b\le U_b\le H_b\) of level \(D=x^{d_0}\).
The honest combined lower is
\[
                  L_sH_b+H_sL_b-H_sH_b .                     \tag{5}
\]
Indeed \(H_s,H_b\ge0\) and replacing the two \(L\)'s by their
indicators leaves a difference from \(U_sU_b\) exactly
\((H_s-U_s)(H_b-U_b)\ge0\). In particular no product of two
possibly negative lower sums has been asserted to be a lower.

We use [Lichtman, arXiv:2309.08522v1](https://arxiv.org/html/2309.08522v1),
§6.1 for the support of both classical weights. For the lower,
the decreasing distinct labels obey \(p_1^2<D\) and
\(p_1\cdots p_{j-1}p_j^3<D\) at each even \(j\).
The first-square test is automatic since \(2r=.446<d_0\).
At an odd index \(j\ge3\), the preceding even cubic condition
implies the all-prefix square condition at \(j\), since
\(p_j\le p_{j-1}\). At the even indices it is immediate.
Thus both actual Rosser supports lie in the all-prefix square
support of Proposition 6.1. Round exponents up on a fixed fine
mesh in the even (respectively odd) cubic tests. This is a
pointwise lower (respectively upper) as before: every branch
cut first at an even prefix has subtree total nonnegative
(the divisibility indicator of the prefix times the exact
avoidance indicator for its smaller primes); at an odd
prefix the sign is reversed. The first-square test is still
automatic with the fine mesh. The principal difference from
the unrounded coefficient is \(o_\Delta(1)\) in its large-bank
harmonic model at fixed \(\xi\) by the finite union of
\(O_\xi(\Delta)\)-wide prefix walls. On the actual progression
side the rounded coefficients are used exactly.

At every dyadic prime-source scale \(X\asymp x\) use notional
sieve level \(\Theta=.55525\), spectral exponent \(7/32\) and
upper residue exponent \(\alpha=1.001\); the residue is \(N\)
itself, with \(N\le X^\alpha\) for all large \(N\).
Use \(t_i=\log p_i/\log X\); the numerical ceiling may be
taken \(t_1\le .2231\). For \(t_1\ge .1107\) the three
terms of Lichtman (6.2) are bounded below respectively by
\((1+.1107)/2=.55535\), \((1-(3/2-2\theta).2231)/(1+\theta)>.62\),
and \(1-(\alpha\theta+3\cdot.2231)/2>.5558\).
Each is strictly above \(\Theta\). For \(t_1<.1107\) and at
least three labels we have \(t_1<\mu\) of Proposition 6.1;
the three interior upper entries of \(w(t_1,t_2,t_3)\) in (6.9)
exceed \(.581,.5561,.778\), while the lower gate is at most .55535.
This covers \(\Theta\) through (6.4). The branch with
at most two such labels, including the unit, is ordinary
BV, as its full modulus after the small-bank merge is
\(\le X^{.2214+b+o(1)}\).
All these comparisons have fixed strict margins.

For the medium source branch take the actual short HB
length \(Q_s\) with exponent in \([2\tau,1/3+\tau/4]\)
and put \(A=Q_sX^{-\tau}\) in Proposition 6.1.
Here \(\tau>0\) is a sufficiently small fixed constant,
in particular \(2\tau<\Theta-d_0\).
Assign the three groups on one feasible representative in
each rounded bin vector, retain the groups throughout the
box, and merge the independent small-bank factor in group
three. The exact margin and coefficient arguments in
[AngularPrimeDomination](../AngularPrimeDomination.md), §1,
apply: before rounding losses, changing \(A\) to \(Q_s\)
spends \(2\tau,\tau,(1+2\theta)\tau\) from the three respective
\(3\tau,3\tau,2\tau\) margins in (6.3); the small bank costs
at most \((2+2\theta)b\). Take \(b\ll\tau\), \(\xi\ll b\)
and the rounding mesh sufficiently fine afterward.
This verifies the actual (5.2) inequalities, including
the factor \(|a|^\theta\), for each independent group.
Fixed factorial-normalization factors for repeated rounded
bins and the power-small repeated-prime errors are the
same as there. This verifies packing of the **lower** as
well as upper support, rather than invoking a theorem for
arbitrary lower weights or for any triply well-factorable
sequence.

For completeness, the prime-source argument uses order-three
Heath--Brown at scale \(X\), inserting roughness
\(z_0=X^{1/(\log\log X)^3}\) before opening \(\Lambda\).
It is exact on every true prime under consideration; proper
prime powers cost \(X^{1/2+o(1)}\) even with a divisor-power
coefficient on their reflected partner. All resulting slots
inherit the roughness, and the same individual medium
\(1,\log,\mu\) slot satisfies the auxiliary-mask
Siegel--Walfisz hypothesis of Proposition 5.2 as in §2 of
[AngularPrimeDomination](../AngularPrimeDomination.md).
The complementary divisor-bounded coefficient can be
trimmed by divisor moments with the same log reserve.
No sharp moving coefficient is introduced on the selected
slot: the whole-product interval \(N-J\) is handled by the
same interval separation, or by two fixed prefix endpoints.

If there is no medium source slot, there are at most two
long unweighted integer variables (with the permitted log
weight on one) above \(X^{1/3+\tau/4}\); the other factors
have product \(K\le X^{12\tau+o(1)}\).
There is at least one long variable, since all six small
slots could not produce a number \(\asymp X\).
For two long variables use uniform-residue Lichtman
Proposition 3.2 at scale \(X/K\), exactly as in the
two-free case of the original upper proof.
Our enlarged modulus is \(X^{.555+b+o(1)}\), within its
fixed \(2/3\) power reserve. Both free variables have the
honest \(z_0\)-roughness and the balanced-from-below
ranges needed there. The residue after freezing \(K\)
is \(N\overline K\bmod q\) if \((K,q)=1\), with no
restriction on the representative because this branch is
uniform in the reduced residue. The complementary interval
and any log factor are as in that two-free argument.

In the one-long-variable case, for each fixed \(K\) and
reduced residue modulo \(q\) the free length is \(Y\asymp X/K\).
Sieve its \(z_0\)-roughness by the dimension-one fundamental
lemma at auxiliary level \(X^{.04}\), using just the primes
not dividing \(q\), since the residue is reduced. CRT gives
the main \(Y_0 V_{z_0}(q)/q\), with \(Y_0\ll Y\) the free
interval length and \(V_{z_0}(q)=\prod_{p\le z_0,p\nmid q}(1-1/p)\),
and absolute error
\[
 O\!\left((Y/q)e^{-c(\log\log X)^3\log\log\log X}
                      +X^{.04+o(1)}\right)
\]
uniformly on subintervals. Partial summation for a log
factor costs only a log. The exact unit principal is the
average of these same counts over reduced residues, so
the main cancels and the same error bounds the centered
discrepancy. If \((K,q)>1\), both terms are zero on our
actual unit residue. Summing the harmonic error over moduli
and all fixed short products costs logs only; floor errors
are \(O(X^{.595+b+12\tau+o(1)})\), with the divisor
multiplicities absorbed. This proves the needed arbitrary-log
progression error for each of the three terms of (5).

After reassembling the prime source, its total weighted mass
is \((1+o(1))|J|\) by PNT. A source prime \(P\asymp X\)
is larger than the moduli, so its counted coprime model
is exactly the expected one. Cases \(P\mid N\) are
negligible, and when \((y,N)=1\) the omitted primes dividing
\(N\) do not change the physical roughness event.
The principal density is \(g_p=1/(p-1)\) for \(p\nmid N\).
Let the rounding mesh tend to zero at fixed \(\xi\),
then send \(\xi\) to zero with \(b\) fixed, all after the
large-target limit. The small-bank ratio tends to one in
both directions, so (5) has lower main at least the product
dimension-one lower \(f(d_0/r)\) and the full local
product. Now
\[
 f(s)=\frac{2e^\gamma}{s}\log(s-1)
       \quad (2\le s\le4),\qquad
 V(z)=(1+o(1))\,\frac{e^{-\gamma}\mathfrak S(N)}{r L}.
\]
These are the ordinary lower linear-sieve function and
Mertens factor in the correct target-unit model, so their
product times \(L\) is \(c_0(1+o(1))\mathfrak S(N)\).
This proves (4). The strict numerical lower \(c_0>1.434\)
follows by the elementary positive series for \(\log u\)
in the power \((u-1)/(u+1)\), as in the exact checker.

## 2. Which physical rows receive the reserve

The rough rows in (4) with a repeated prime factor are
\(O(x^{1-r+o(1)})\) after checking multiples of each square,
and so negligible with \(\log P\,L\) weights.
Since \(5r>1\), the only remaining ranks are \(1,2,3,4\).
On prime rows the mass \(\sum\log P\,L\) is at most
\(\mathcal G\) (here \(y\ge x\)); they are not negative composites.

On the same central \(J\), remove the following three disjoint
neutral sets from this rough mass: rank two with smaller label
\(<\rho\); rank three containing a giant (a label \(>T/2\),
\(T=\log y/L\)); and the whole rough rank four. Their total
actual mass in the \(\log P\,L\) normalization, divided by
\(M_N\), is less than \(.661+o(1)\), as follows.
Apply the
[level .555 angular prime upper](../angular_prime_level_555/Proof.md)
with factor \(400/111\) separately to these positive product
sources. For the first the ordinary ordered measure is
\[
 A_2=\int_r^\rho\frac{du}{u(1-u)}
       =\log\left(\frac{\rho(1-r)}{r(1-\rho)}\right).
\]
For the giant rank three the giant is unique, and the two
other labels \(a,b\ge r\) satisfy \(a+b<1/2\).
In the unordered pair of smaller variables the density is
\(1/[2ab(1-a-b)]\le r^{-2}\) in the full triangle.
Consequently
\(A_{3,{\rm giant}}\le(1/2-2r)^2/(2r^2)\).
For the full rank four the simplex volume is
\((1-4r)^3/3!\) and the reciprocal product is \(\le r^{-4}\);
including \(1/4!\) gives
\(A_4\le(1-4r)^3/(144r^4)\).
The exact rational numerical check gives
\[
    \frac{400}{111}(A_2+A_{3,{\rm giant}}+A_4)<.661.             \tag{6}
\]
All these are upper bounds for literal positive sets. Each
angular support is compact since \(r>0\). For the cited upper,
replace \(\log x\) by \(\log N\) or \(\log y\) only in forming
a fixed smooth upper envelope, paying the \(O(1/L)\)
angle shifts by fixed wider neighborhoods of the finitely
many threshold hyperplanes, then letting these shrink
after the large-target limit. Their ordinary measures tend
to zero by bounded density on the compact support.
Likewise the position weight is the fixed window
\(J/N=J_0/2\); its ordinary profile mean in the full central
interval includes the ratio \(|J|/(N/3)\).
The actual \(\log P\,L\) evaluation differs from
\((\log N)^2\) by \(1+O(1/L)\) here. Thus (6) indeed
charges the same \(M_N\) as (4), never compares model
ranks against a different prime density, and makes no
signed use of the positive angular upper.

In the remaining rank-two set, also remove the near-half
collar \(y=st\), \(s\le t\) actual primes and
\(s>x^{1/2-\delta}\). Precisely
\(s\in(x^{1/2-\delta},\sqrt{4x/3}]\).
For each actual \(s\) the two-form upper sieve in
\(t,N-st\) gives \(\ll x\mathfrak S(N)/(sL^2)\) rows,
with a bounded correction \((s-1)/(s-2)\).
Its harmonic mass is \(O(\delta)+o(1)\) by PNT and
partial summation (literal exponent width \(\delta+O(L^{-1})\)).
Hence the excised \(\log P\,L\) mass is
\(O(\delta M_N)+o(M_N)\). The remaining actual rank-two
rows have \(u_s\ge\rho>.25008>.25002\), so both
the old and the extra mark are fully activated at \(s\).
The smaller prime is below the top cutoff,
\(2\beta<r\), and \(g_\epsilon(u_s)=1\).
There are no other short marked subsets, and so
\[
               \widetilde F_\kappa=-2\kappa u_s
                           \le -2\rho\kappa .
\]
On each remaining rank-three row there is no giant,
so all pairs are above the **own** half and the shorter
\(g\) cutoff. At most one singleton can exceed
\(1/2-\delta\) since every label is \(\ge r\).
The other two are fully activated by the original mark,
even if the extra \(v\) is zero there. Thus
\(\widetilde F_\kappa=-Z_{\phi_\kappa,g}\le-4r
\le-2\rho\kappa\) for \(0<\kappa\le1\).
Once again no lower bound for the individual rank-three
population has been used.

Consequently on these genuine rank-two and rank-three
subsets the combined score is at most
\[
 -2\rho\kappa
 \big((c_0-.661)M_N-\mathcal G-O(\delta M_N)-o(M_N)\big).        \tag{7}
\]
This inequality holds even if the parenthesis is not
positive. It is the unconditional reserve tradeoff; only
its no-binary interpretation sets \(\mathcal G=0\).
Outside the counted subsets all rank-three scores are
still nonpositive by the singleton/pair check of the
old one-mark theorem, which uses nonnegative amplitudes
only. Rank-two scores outside can be positive only on
the two original fringes \(u_s<2\beta\) and \(u_s>1/2-\delta\).
The old actual two-form bounds give \(O((\beta+\delta)M_N)+o(M_N)\)
there since the extra \(\kappa v\) is nonnegative.

## 3. Rank four and unchanged zero calibration

Compare first to the sharp own-half cutoff, with the top
taper on the **extra** mark temporarily removed. At rank
four the nongiant short-pair graph is the star or triangle
of the old theorem. Its star contribution to \(Z\) for
the extra mark is \(-2\phi_{\rm extra}(a)\) where \(a\)
is its least label. The least label is at most
\(T/4=.25+O(1/L)<.25002\), so this is zero.
On the triangle with sorted labels \(a<b<c<d\), at most
one among \(a,b,c\) exceeds .25002, since the sum of
every lower two is below the own half. The extra contribution
\(\phi_{\rm extra}(d)-\phi_{\rm extra}(a)-\phi_{\rm extra}(b)-
\phi_{\rm extra}(c)\) is nonnegative by monotonicity of
\(2u v(u)\). On a giant rank-four row the sharp extra
contribution vanishes: for a marked cofactor label the
remaining cofactor has two unrestricted bits in its
sharp short-set sum, while the giant is not short.
This proves the rank-four sign for the sharp extra mark
without consuming any rank-four positive budget.

The top taper and shorter \(g_\epsilon\) cost only
\(O_\kappa([\delta(1+|\log\delta|)^2+
\epsilon(1+|\log\epsilon|)^2]M_N)+o(M_N)\) on rank
four, by the real fixed-rank marked-wall estimates of
[the finite-rank follow-up](../marked_cusp_finite_rank/Proof.md).
Those estimates use only the uniform amplitude bound
and the two near-half cutoffs; the midrange profile \(v\)
is unchanged. Add the original rank-four fringe bound
where applicable. Since \(2\rho(c_0-.661)>.386\), choose
\(\beta,\delta,\epsilon\) **after** \(\kappa>0\) to
make the total fringe errors smaller than
\(\left(2\rho(c_0-.661)-.380\right)\kappa M_N\). This proves (2).

The zero calibration of the old \(Z\) proof still holds
for (1), without change of reference. Its actual \([d,e^2]\)
moduli, unit masks, largest supported label, and positive
length of the flat region for the residual \(m=d/p\)
are exactly unchanged. The amplitude is fixed and
bounded, which is all the inverse-Mertens argument or
the fixed-parameter absolute small-factor/rank tails
use. Thus the marked sum is still \(o(M_N)\) after
restriction to rough \(\log\log x\)-scale minimum as in
the original cusp formula. The actual primes have
\(Z=0\). Insert (2) in that exact reference identity to
obtain (3), with all terms using one ledger.

## 4. The new higher-rank sensitivity is not priced by the reserve

A useful check is the ordinary signed rank-five marginal
of the extra mark, not a fixed-target asymptotic.
Let \(I_5\) be the normalized angular integral of the
[finite-rank follow-up](../marked_cusp_finite_rank/Proof.md).
For the sharp own-half extra mark with amplitude \(2u v(u)\)
(before multiplying by \(\kappa\)), the pinned-mark
sine law gives
\[
 I_5(-Z_{\rm extra})=
  \int_0^\infty
       v\big((1-e^{-t})/2\big)\,
       \frac{t(\pi^2-t^2)}{3(1+e^t)}\,dt .                    \tag{8}
\]
The full integral without \(v\) is \(\pi^4/120\).
Our onset is below \(\rho=.2501\), so the deleted portion
is at most the integral on \(0<t<-\log(1-2\rho)<.694\),
where the integrand is positive. The logistic satisfies
\((1+e^t)^{-1}\le\tfrac12-\tfrac14t+\tfrac1{48}t^3\)
for \(t\ge0\), since \(\tanh z\ge z-z^3/3\) follows by
integrating \(1-\tanh^2z\ge1-z^2\).
Using this polynomial up to .694 gives an explicit upper
\(<.29964\) for the deleted integral, and hence
\(I_5(-Z_{\rm extra})>.5121\). For verification, at
\(a=.694\) the polynomial integral is
\[
 \frac13\left[\pi^2\left(\frac{a^2}4-\frac{a^3}{12}
                          +\frac{a^5}{240}\right)
        -\left(\frac{a^4}8-\frac{a^5}{20}+\frac{a^7}{336}\right)
          \right].
\]
Use elementary rational enclosures for \(\pi\) and \(\log 2\).
A sufficiently small top taper only removes a part
where \(t>\pi\) (negative in (8)), and the \(g\)-wall
error goes to zero in the ordinary fixed-rank absolute
integral. Thus the new rank-five ordinary signed debit
increases by at least \(.51\kappa\) for sufficiently
small collars. This is much larger than the proved
\(.380\kappa\) receiver, before multiplying a positive
angular cap by any sieve factor. In particular the
generic positive-only angular recipe for the full
near-sharp mark cannot turn (2) into closure without
an independent improvement controlling the actual
higher signed rows. No lower bound on the actual
reflected rank-five mass is inferred from (8).

This is a true combined low-rank reserve, complementary
to (not a second count of) the previous rank-six cusp
estimate. It is not a proof of Goldbach or an assertion
that all accompanying costs have been paid.

By comparison, [Li--Liu, arXiv:2606.05224v2, Theorem 1.1](https://arxiv.org/html/2606.05224v2)
counts representations with one true prime and a prime or suitably
unbalanced semiprime. It is not a lower for true rank three, nor a
lower with the present roughness and fixed central window.
The lower (4) permits up to four factors and our signed inequality
uses the pair or its rank-two/three alternatives after precise
positive caps on the neutral sectors.
No asserted refinement of Chen's relative-size theorem is needed.

[Marshall Ratliff's May 2026 v2 preprint](https://doi.org/10.5281/zenodo.20377091)
claims a rougher Chen-type theorem, with roughness exponent
\(0.2665-\varepsilon\) and at most two prime factors at
every sufficiently large even target. That preprint's
marked progression levels are not used or certified
here. Our increment is instead an actual fixed-central-window
signed reserve for **this calibrated cusp**, protecting
rank four and charging the correct remaining higher
ranks; it is not a priority or record claim about a
roughness exponent. As a fallback, the same elementary
lower Rosser construction works with \((d_0,r)=(.514,.2501)\)
without using the angular cap (6): there are then only
ranks \(1,2,3\), giving a weaker strict \(.100\kappa M_N\)
receiver after the collars.
