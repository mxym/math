# The full zero-tag self-pair by a signed affine sieve

Keep the exact sextic \(F(t)=44(1/2-t)_+^4-112(1/2-t)_+^6\),
the original score \(S=G_b+W,\ b=.003\), and the fixed even \(N\),
central interval \(J\), \(L=\log N\) and \(M=|J|N\mathfrak S(N)\)
of [the full medium comparison](FullMediumCohort.md). All pair sums
use \(x+y=N,\ x\in NJ,\ (x,N)=1\); the opposite orientation uses
\(1-J\). Put \(a=.080\), \(z=N^a\), and let \(\mathcal Z_a\)
be the **whole** actual zero-tag self-pair:
\(P^-(x),P^-(y)>z\).

**Proposition.** Uniformly through individual even targets,
\[
             \sum_{\mathcal Z_a} S(x)S(y)>(1.633+o(1))M.              \tag{1}
\]
There is no sign on the exterior. This replaces the entire
[.110 self-pair and its low mixed strip](WiderZeroTagPairCredit.md)
and costs at most \(.000176 M+o(M)\) on the part of the old complete
two-tag chamber not subsumed. Relative to those two older comparisons,
the net gain is \(>.4518M+o(M)\), with every zero-by-zero row
now absent from the exterior. None of the old overlapping credits
is added to (1).

## 1. The physical expansion and its cap

Write \(I_z(n)=1_{P^-(n)>z}\),
\(\Pi(n)=1_{n\ {\rm prime}}\log n\), and
\[
 V_0(n)=I_z(n)\mu^2(n)(\log n)\sum_{d\mid n}\mu(d)F(\log d/\log n),
 \qquad H_0=V_0-\Pi.
\]
Here and below the identity defining \(H_0\) is used only on central
arguments, where every prime passes \(I_z\). The old gate passes on
\(\mathcal Z_a\), and \(W=0\) there since its first two tags have
sum at most .065. The original \(Q=[-H]_+1_{P^->N^{.1251}}\)
is supported on the \(I_z\) arm. It follows exactly that
\[
 \sum_{\mathcal Z_a}S(x)S(y)
 =\langle V_0,V_0\rangle-\langle\Pi,V_0\rangle-\langle V_0,\Pi\rangle
   +R_J+\langle Q,H_0\rangle+\langle H_0,Q\rangle+\langle Q,Q\rangle.
                                                                    \tag{2}
\]
Both \(R_J=\langle\Pi,\Pi\rangle\) and the last term are
nonnegative and are discarded in (1). In particular the prime-pair
term is not used a second time in the ledger.

Every integer on an \(I_z\) arm has at most 12 distinct prime factors;
its divisor Möbius sum has at most \(2^{12}\) nonzero terms.
Change its logarithms in the weights to \(L\), at error \(O_J(1/L)\)
per normalized term. Indeed the actual \(\log n=L+O_J(1)\)
and \(F\) is Lipschitz on the fixed compact angular domain.
The genuine pair ambient bound (4) of
[the rough positive block](RoughPositiveCredit.md#1-one-genuine-common-rough-ambient-set),
now with \(a=.080\) and support exponent .499, is
\[
       \#\mathcal Z_a\le(C_0+o(1))M/L^2,\qquad
       C_0=\bigg(a^2\mathcal G(.499/a)\bigg)^{-1}<49.353,
       \quad \mathcal G(u)=\int_0^u\rho_2(t)\,dt .                   \tag{3}
\]
Thus the normalized replacement gives \(o(M)\) for every pair
on this support. When expanding the raw double in (2), retain only
\(d\le N^{.4999}\) in each factor. The actual omitted terms
\(s=\log d/L>.4999\) have \(0\le F(s)\le44(10^{-4})^4\);
both sums have amplitude at most \(2^{12}L\). The true
raw double error is at most
\(2\cdot44\cdot 2^{24}(10^{-4})^4 C_0 M+o(M)<.00000729M+o(M)\).
Likewise removing either squarefree indicator inside that
expanded double costs \(O(N^{1-a}L^C+N^{1/2}L^C)=o(M)\):
a square \(p^2\mid x\) or \(p^2\mid y\) has \(p>z\);
sum \(O(N/p^2+1)\) over \(p\le\sqrt N\) and use the same
bounded physical divisor multiplicity. We restore all squarefree
indicators at that cost. No hard cap is imposed on \(\Pi,V_0\).

## 2. The genuine dimension-two lower and upper on the same fibre

Fix actual supported squarefree \(d,e\) with \((de,N)=(d,e)=1\).
There are no other labels with nonzero physical count on the
target-unit rows. For \((d,e)=1\), the two actual integers
\(x/d,y/e\) are the affine coordinates of the primitive line
\(d r+e v=N\), with \(r\) varying by \(e\) in its reduced
class and \(v\) by \(d\). Its free interval has length
\(X=|J|N/(de)\) up to an absolute endpoint floor. Since the
named factors of \(d,e\) exceed \(z\), the roughness of both
original arguments is exactly that of \(r,v\). At each \(p\le z\)
there are \(\nu_N(p)=1\) forbidden free residue classes if \(p\mid N\)
and 2 otherwise. In particular there is one at 2. Each squarefree
sieving modulus \(\ell\) therefore has actual remainder
\(O(2^{\omega(\ell)})\) relative to \(X\prod_{p\mid\ell}\nu_N(p)/p\).
To restore the true unit condition after sifting, remove multiples
of any \(p\mid N\) with \(p>z\): the two roots again coincide
and each costs \(O(X/p+1)\), since \(p\nmid de\).
The summed error is \(O(X L/z+L)=o(X/L^2)\), uniformly even
on the shortest length here.

For a fixed pair of angular cells with upper endpoints totaling
\(\sigma\le .9998\), use the unweighted dimension-two DHR lower
sieve at level \(D=N^{.999(1-\sigma)}\). Apply Diamond–Halberstam,
[*A Higher-Dimensional Sieve Method*, Theorem 9.1](https://www.cambridge.org/core/books/abs/higherdimensional-sieve-method/sieve-method-for-1/5A00D3EA4C00B3B10D3CB8521D68D10C),
as explicitly stated by
[Franze–Kao, §4, equations (20) and (22)](https://arxiv.org/pdf/1812.11280).
This is the DHR \(f_2\) bound, not an identification with the
Rosser–Iwaniec upper or lower function.
The sieve hypothesis
\[
 \prod_{w\le p<t}(1-\nu_N(p)/p)^{-1}
 \le (\log t/\log w)^2(1+O(1/\log w))
\]
has a uniform constant: odd target coincidences only decrease it,
the factor at 2 is fixed, and otherwise the comparison with
Mertens squared uses a uniformly convergent \(O(\sum_{p\ge w}p^{-2})\).
The bound on summed absolute remainders holds with power reserve
even with the extra factor \(4^{\omega(\ell)}\), by
\(\sum_{\ell\le D}8^{\omega(\ell)}\ll D(\log D)^7\) and
\(D/X\ll_J N^{-.001(1-\sigma)}\). Thus, for
\(s=.999(1-\sigma)/a>\beta_2\), the lower coefficient for the
actual fibre is \(a^{-2}e^{-2\gamma}f_2(s)\), in the scale
\(X\mathfrak S(N)/L^2\). We use zero when the lower sieve is not
invoked. The local sifting product is uniformly
\((1+o(1))e^{-2\gamma}\mathfrak S(N)/(a^2 L^2)\) by the
same physical root calculation as (3); the omitted large
target factors have reciprocal sum \(O(L/z)\).

For the upper use the genuine Selberg square on the **same**
fibre with coefficient support \(D'=N^{.499(1-\sigma)}\).
Its actual floor \(O(D'^2 L^{10})\) is again a power saving.
Exactly the positive-denominator argument of (3), at real ratio
\(.499(1-\sigma)/a\), gives the upper coefficient
\[
                       U_2(\sigma)=
        \frac{1}{a^2\mathcal G(.499(1-\sigma)/a)}.                  \tag{4}
\]
There is no lower cut on this ratio; it stays strictly positive
by the hard cap. In particular the calculation does not use an
upper DHR formula outside its permitted sifting range.
These fibre errors are uniform at the fixed cells, and regrouping
them over actual labels costs at most their bounded reciprocal
mass. The actual square errors and hard cap have already been
accounted for in §1.

For clarity, the only DHR numerical input needed is
\(4.266<\beta_2<4.267\), certified by the
[Booker–Browning interval table](https://arxiv.org/src/1511.00601v2/anc/dhr.html).
Their [Theorem 3.1 and §5.2.6](https://arxiv.org/pdf/1511.00601)
give \(\alpha_2>\beta_2+1\),
\(F_2(u)=1/\sigma_2(u)\) for \(0<u\le\alpha_2\),
\(F_2(u)\ge1\), and \((s^2 f_2(s))'=2s F_2(s-1)\)
for \(s>\beta_2\). In their normalization
\(\sigma_2(u)=e^{-2\gamma}\mathcal G(u/2)\). This follows
also from their delay equation (7): (3) of the rough positive
block gives \(u\rho_2(u)-2\mathcal G(u)=-2\mathcal G(u-1)\),
and the initial values for \(u\le1\) give the same solution.
For \(s>4.267\) we therefore use only the lower bound
\[
 e^{-2\gamma}s^2 f_2(s)\ge
    \int_{4.267}^{\min(s,6.266)}
       \frac{2v}{\mathcal G((v-1)/2)}\,dv
    +.3152\,(s^2-6.266^2)_+ .                                     \tag{5}
\]
Indeed \(6.266-1<\alpha_2\), and for the remaining integrand
\(e^{-2\gamma}F_2(v-1)\ge e^{-2\gamma}>.3152\).
The integral is taken as zero for \(s\le4.267\).

Here is the ordinary (not jointly modeled) measure of the actual
sieving labels \(d,e\). For \(t=\log d/L>0\) let \(E(t),O(t)\)
be the genuine reciprocal densities of their even and odd
Möbius classes at floor \(a\). These are the even/odd
convolution sums of \(\kappa(dt)=1_{t\ge a}\,dt/t\), with
\(1/j!\) on the \(j\)-fold term; there is the even unit atom at
zero. This follows from prime Mertens on the fixed positive
angular ranges. Distinctness within a label and coprimality
between two labels, and target-unit exclusions, lose \(o(1)\)
in the reciprocal product model: a common large prime costs
\(\sum_{p>z}1/p^2\), and large target primes cost \(O(L/z)\).
All other density factors are bounded because the maximum ranks
of the labels are fixed. The non-atomic \(B_\pm=E\pm O\)
satisfy
\[
       t B_\pm(t)=\pm\left(1+\int_a^{t-a}B_\pm(w)\,dw\right),
\]
where the integral is zero below \(2a\). In particular \(B_+\ge0\)
and \(B_-(t)=-\rho(t/a-1)/t\le0\) by the ordinary Dickman
delay equation. Values at finitely many endpoints are irrelevant.

At a pair of cells use (5) on each actual positive-sign pair
of labels and (4) on each actual negative-sign pair; now their
coefficient of \(F(t)F(u)\), before the separate face integrals,
is bounded below by
\[
  L_2(\sigma)\{E(t)E(u)+O(t)O(u)\}
  -U_2(\sigma)\{E(t)O(u)+O(t)E(u)\}.                               \tag{6}
\]
Here \(L_2\) denotes the lower coefficient from (5) divided by
\(s^2a^2\), with zero for the missing range. The same formula with
the even unit atom handles either or both zero labels. Equations
(4)–(6) are bounds on actual affine rough rows for each fixed
pair of labels prior to summation. In particular (6) does not
suppose the prime factor partitions of \(x\) and \(y\) are independent.

Use the 4199 angular cells of width \(10^{-4}\) from .080 to .4999,
and the even unit atom. The checker bounds (6) using uniform
enclosures on each cell, so no infinitesimal mesh assumption
enters the numerical inequality. After the physical cap error
in §1 its raw signed lower is
\[
                          \langle V_0,V_0\rangle
                       > 9.585 M+o(M).                            \tag{7}
\]

## 3. The prime terms and the original Q correction

We use the actual product-BV transfer of
[MediumSemiprimeAdverse, §2](MediumSemiprimeAdverse.md#2-both-signs-in-the-ordinary-subroot-transfer)
with no mandatory tag. For a fixed \(d\)-angle cell with upper
endpoint \(s_+\), put \(\Delta=.499-s_+\). When \(\Delta>0\),
the original receiver \(y=d r\) is genuinely rough precisely
when \(r\) is rough at \(z\). Apply the one-dimensional
linear sieve at level \(N^\Delta\) after opening \(d\):
all actual joined moduli \(d\ell\le N^{.499}\) are in the
reduced class \(N\). The sources used are the true \(\Pi\)
and the true nonnegative \(Q\).
The former uses ordinary prime BV and the latter uses genuine
product BV on compact bounded-rank angular boxes, with squarefree
prime factors and the true \(Q\) angular weight. Continuity on
the fixed-floor rank simplices (with the hard .1251 floor) lets
one use finite-box inner/outer approximations in the positive
estimates. Errors are first controlled at fixed boxes and then
the box approximation is refined. The modulus aggregation has
the usual divisor weights (in fact the small-prime sieve part
and large-prime label \(d\) have disjoint prime supports).
There is no coprimality assumption on a physical pair beyond
the original target units. For the principal, \(\ell\)'s prime
factors lie at most \(z\) and so cannot divide either source.
The reduction at \(p\mid N\) omits its class by the same target
unit condition as in (2). The remaining source loss at \(p\mid d\)
or \(p\mid N,\ p>z\) is power-small by \(p>z\), the actual bounded
source weight, and the reciprocal sum of the outer labels.
The resulting ordinary coefficient is \(1/d\) times the genuine
linear-sieve constant and the same \(\mathfrak S(N)\):
\(d/\varphi(d)=1+o(1)\) on the actual polynomially rough labels.
This describes the source mask on both the \(V_0\) and prime
receivers, not an independent prime-opposite count.

Let \(U_1(\Delta),k_1(\Delta)\) be the normalized upper and
lower one-dimensional factors used in the preceding signed
transfer. They are monotone bounds from the linear-sieve
formulas: use \(U_1=2/\Delta\) for \(\Delta\le3a\)
(sift fewer primes at the lowest levels), multiply by
\(1+(\Delta/a-3)^2/4\) for \(3a<\Delta<4a\), and
use \(U_1=.575/a\) beyond. Use \(k_1=0\) for \(\Delta\le2a\),
\(2\log(\Delta/a-1)/\Delta\) below \(4a\), and
\(.549/a\) beyond, with outward logarithm enclosures.
The bounds beyond \(4a\) can simply use the level \(4a\).
For the prime receiver alone use its tiny-root upper at
level \(N^{.499}\), giving constant \(2/.499\) against
the actual compact positive \(Q\) source. Each source weighted
mass is \((m(Z)+o(1))|J|N\) for \(Z=\Pi,Q\);
\(m(\Pi)=1\) and \(m(Q)<.01701\) by
[the ordinary rough-mass proof](RoughOrdinaryMassBoxes.md)
including its rank-six/seven bounds.

**Prime cross.** In each non-atomic cell the signed upper
against the genuine \(\Pi\) source is \(F(t)(U_1 E-k_1 O)\)
when \(\Delta>0\), and the atom is bounded by \(U_1(.499)\).
A second valid upper, allowing every cell through .500, discards
the negative part and uses \(F(t)E(t)C_2\). To get \(C_2\),
fix the actual label \(d\). On \(q+dr=N\) require genuine
prime \(q\) and \(z\)-rough \(r\); use a true Selberg upper
at coefficient support exponent
\(\min(4a,.499(1-s_+))\).
Below \(z\) the two affine roots are as in §2. Above \(z\)
sift \(q\) alone up to the coefficient support, which is below
the actual central prime \(q\). In the positive Selberg
denominator retain its original double-root part and, in
addition, terms with exactly one extra tested prime \(p>z\).
Such terms are disjoint from the original part. Their local
factor is \(1/(p-1)\); primes of \(d\) may be omitted there
because they are already excluded by \(q\equiv N\bmod p\).
The reciprocal mass of the omitted large primes of \(dN\) is
\(O(L/z)\). The proof and exact normalization are the augmented
Selberg denominator in
[SmallSemiprimeThreeTagAdverse, §2](SmallSemiprimeThreeTagAdverse.md#2-a-strengthened-true-affine-upper-for-each-layer),
now with free length \(|J|N/d\) and no tags. With
\(u=\min(4,.499(1-s_+)/a)\) it gives
\[
 C_2^{-1}\ge a^2\left(\mathcal G(u)+\int_1^u\mathcal G(u-v)\,\frac{dv}{v}\right).
\]
Both logarithmic weights are paid in this same physical
ambient. The floor has a fixed exponent margin. Taking the
better upper cellwise, the outward signed upper is
\(\langle \Pi,V_0\rangle<3.95872M+o(M)\), and likewise in
the opposite orientation.

**Q cross.** For \(\langle Q,V_0\rangle\), temporarily cap the
receiver labels at .4989. The original pointwise \(Q\le2L\)
follows from the rank-four to seven caps in the sextic base.
By (3) the physical terminal difference costs at most
\(44\cdot2^{13}(.0011)^4 C_0 M+o(M)<.00002605M+o(M)\);
squarefree and own-log errors are as above. With the positive
source \(Q\), use the actual *lower* principal on the even
labels and the actual upper on the odd labels. In each cell
the coefficient, before multiplying by \(m(Q)\), is
\(F(t)(k_1 E-U_1 O)\); the even unit atom is \(k_1(.499)\).
There is strictly positive modulus slack through the final
cell, so this calculation uses only true below-root transfer
and covers all retained terms with their signs. The checker
gives coefficient \(>3.01957\). Hence
\[
  \langle Q,H_0\rangle
       \ge -\left[(2/.499-3.01957)\, .01701+.00002605\right]M+o(M)
       >-.016840M+o(M),                                           \tag{8}
\]
with the actual \(Q,\Pi\) term subtracted using the same source.
The reflected inequality holds as well. Both \(Q,Q\) and
\(R_J\) in (2) are now discarded once. Combining with (7)
and the two prime bounds proves (1).

## 4. Physical replacement and numerical certificate

The old .110 self-pair and the retained low mixed strip both lie
inside \(\mathcal Z_a\): their least angles are strictly above
.080 on both arms. Their \(1.025M\) lower is replaced, not added.
The old \(\mathcal F_{\rm all}\) may overlap \(\mathcal Z_a\);
do not keep its .156 credit. The entire exterior piece
\(\mathcal F_{\rm all}\setminus\mathcal Z_a\) has lower
\(-.000176M+o(M)\) by
[the complete tagged proof](CompleteTaggedCredit.md):
every negative row on any subset of that chamber is contained
in the two actual \(B_9,B\) crossings, whose **gross** upper
price is .000176. This leaves the entire old chamber and
the entire new zero-by-zero pair paid without overlap.
Other current exact small-tag chambers have at least one real
prime \(\le z\); this operation is not an estimate for any new
positive/negative pair there. The gain against just the
superseded credits is \(1.633-.000176-1.025-.156>.4518\).
It is a change in bounds on a different actual outside support,
not a resolved fraction or a binary lower.

Run:

    python3 -OB check_full_zero_tag_affine_self.py

The [checker](check_full_zero_tag_affine_self.py) locks the
already audited one-dimensional angular density and mixed Selberg
routines by hash. It uses outward binary64 interval arithmetic
with a widening larger than round-to-nearest error after each
basic operation and verifies the strict displayed constants.
For the Dickman-2 function put \(g(u)=\rho_2(u)/u\).
The delay equation gives \(g=1\) on \([0,1]\) and
\(g'(u)=-2(u-1)g(u-1)/u^2\) beyond. Its monotonicity
gives lower/upper endpoint rectangles and then lower/upper
integrals of \(u g(u)\) on a grid of spacing \(10^{-4}\),
using scaled integer \(g\)-bounds. Use the lower CDF at the
downward-rounded argument for (4), and in (5) integrate the
lower numerator at each left endpoint over the upper
denominator at the right endpoint. The downward rounding of
\(s\) is safe since \(f_2\) increases. The Euler constant
inequality in (5) is also checked using exact rational
Euler–Maclaurin and exponential tails. Ignoring only
asymptotic \(o(M)\) terms, the replay gives 9.585117997500
for the raw double lower, 3.958716659118 for each prime upper,
.016839362238 for each Q-cross cost, and 1.634005954787
for the complete lower. No projected angular sample appears
in the joint comparison.
