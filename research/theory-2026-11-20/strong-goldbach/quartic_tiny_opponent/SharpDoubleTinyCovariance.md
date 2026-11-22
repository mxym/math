# Both actual tiny arms for the original compensated quartic

Retain the actual fixed even target \(N\), the fixed interval
\(J\Subset(1/3,2/3)\), its true reflection, \(L=\log N\),
\(x+y=N\), \((x,N)=1\), and \(M=|J|N\mathfrak S(N)\).
The score is the **original** squarefree own-root quartic
\(H\) and its unchanged physical compensation
\(\widetilde H=H+Q\), as in
[the original signed tiny-factor cross](Proof.md). No
replacement of the physical score by the affine companion
is made. Write \(I_b(n)=1_{P^-(n)\le N^b}\), and set
\[
 m(b)=-22b+108b^2-136b^3,qquad \sigma=.03.
\]
For \(R\ge 8\) define
\[
 E(R)=\inf_{s\ge0}
    \exp\!\left(-s R+2\int_0^1\frac{e^{sv}-1}{v}\,dv\right).
\]
The simpler upper \(E(R)\le \exp(-R\log(R/2)+R-2)\)
suffices here.

**Theorem.** There is a fixed \(\nu>0\) such that for every
sufficiently small fixed pair \(0<b,b'\le\sigma/8\),
uniformly in the even target limit,
\[
 \left\langle I_b\widetilde H,I_{b'}\widetilde H\right\rangle
   =m(b)m(b')M
    +O_J\left(\{E(\sigma/b)+E(\sigma/b')\}^{\nu}M\right)
    +o_{J,b,b'}(M).                                              \tag{1}
\]
Here both tiny arms are genuine, all physical ranks and both
signs are included, and \(Q=0\) on the marked arms
since \(b,b'<.005\). In particular on the original equal-cut
region with both least factors \(\le N^b\) the signed
contribution is \((484+O(b))b^2 M+o_{J,b}(M)\), with the
\(O(b)\) uniform as the fixed cut \(b\) tends to zero.

This joint calculation does not estimate the mixed no-hit
region with only one tiny arm. A disjoint combination with the
earlier geometric banks is stated in §3.

## 1. Two actual marked products, with their total angles ordered

First use a fixed smooth taper \(f_\delta\) of the sharp quartic
profile \(f_*=P1_{[0,1/2)}\) as in
[the quartic detector, §2](../halfzero_detector/Proof.md).
It agrees with \(P\) at all displacements used below.
Let \(H_\delta\) denote its genuinely squarefree own-log score.
Fix a positive artificial tag floor \(a\), smaller than both
cuts. All current marks are actual squarefree divisors of the
corresponding integer, with primes in \((N^a,N^b]\) or
\((N^a,N^{b'}]\). Their total product on each arm is capped at
\(N^\sigma\), and for now at least one mark is present on each
arm. Set
\[
             u(h)=\log h/L,\qquad
 g_h(t)=\sum_{e\mid h}\mu(e)f_\delta(t+u(e)).
\]
We claim genuine marked-pair factorization for **any** bounded
weights of the mark products, independent between the arms,
which are fixed piecewise continuous functions of the constituent
angles and the mark rank. In particular their product cap
\(u(h)\le\sigma\) is allowed. The ordinary signed coefficient
on one arm, with mark weight \(w(h)\), is
\[
                    -\sum_h \frac{w(h) g_h'(0)}{\varphi(h)} .
                                                                  \tag{2}
\]
Use the literal target-unit omissions in (2). For every fixed
\(a,b,b',\delta\), the actual paired sum is \(M\) times the
product of the two coefficients (2), plus \(o(M)\).
Both sums still see each actual selected subset once.

To see this, first work on separated rectangles of the two
total angles, say \(u(h)>u(h')+\eta\) with fixed positive
slack. Use the first arm as source and **group its actual
marked primes into the short source slot** \(h\). The other
true factors of that source form the long slot. All selected
prime factors exceed \(N^a\), so their own number is bounded
even before a finite source rank cutoff. For the whole source
impose an auxiliary positive least-factor floor and finite
rank, then remove them at the end by the genuine absolute
tails. The actual mark multiplicity on each arm is bounded
at fixed \(a\), so these limits are justified by the original
envelopes, in the positive errors only.

Partition genuine prime factors in each source group into
log-fine multiplicative boxes. The physical signed angular
weight is separable to arbitrary log accuracy on them, and
the real interval test is independent inside each box away
from a spatial boundary. The boundary and repeated slot costs
are those in [the original over-root rail, §1](Proof.md).
The short group, which may have more than one genuine prime,
has the needed Siegel--Walfisz property: fix all but one of
its true prime slots. The final prime lies in a real prefix
or interval of a polynomially large dyadic scale, and its
class is the actual inverse class at the test modulus
provided the already fixed product is coprime to it.
Do the same with any auxiliary forbidden-prime mask.
Removing a forbidden prime from the last slot costs at
most the number of forbidden primes times the count of
the other frozen tuples, a fixed power saving in that
last scale with the allowed auxiliary divisor factor.
Maximal prime Siegel--Walfisz therefore gives arbitrary
log savings after summing the frozen tuples.
For test moduli above any chosen high log power, use the
trivial reduced-class integer count: each short product
has at most a fixed factorial number of ordered genuine
representations. The reduced source main is the actual
short coefficient on units at both moduli. The other,
long coefficient need only be divisor-bounded. These
arguments are valid on each fine box regardless of the
sign of its angular multiplier.

For the receiving arm the actual tested modulus is \(h'd\),
\(d\le N^{.5-\delta}\). Fourier inversion on
\(f_\delta\) separates the \(h'\) weight from the \(d\) weight
exactly, with the \(d\) cap kept on its own slot. Relaxing
\((h',d)=1\) in this product tests only genuine physical
\(p^2\mid y\) with \(p>N^a\); its actual contribution and
the reduced harmonic are power-small, as in the original
rail. Keep \((h'd,N)=1\). Apply
[Fouvry's true large-residue Theorem (1.4), C.1](https://www.numdam.org/article/ASENS_1987_4_20_4_617_0.pdf).
Here the source short slot has exponent \(\beta=u(h)\),
the second modulus slot has exponent \(\alpha=u(h')\), and
the first modulus slot is \(d\). Its two required exponents
are bounded by
\[
       -\beta+1+\alpha\le1-\eta,qquad
       \tfrac32\beta+\tfrac78+2\alpha
                                \le .875+3.5\sigma=.980 .
\]
The primary theorem's scale \(4UV\) is
\((4+o(1))x>N\) on the actual central source boxes.
Thus the literal residue \(N\) is in range.
Fixed dyadic and log-fine subdivisions lose only log powers;
they preserve the strict margins. The same proof uses the
reflected interval when the other actual total angle is
larger.

For each true source integer the reduced \(d\)-harmonic
has the literal mask \(Nxh'\) and exact first-log
\(\mu(d)/\varphi(d)\) moment. Its zeroth moment vanishes
and the local first factor is \(-\mathfrak S(Nxh')\), equal
to \(-(1+o(1))\mathfrak S(N)\) at the current genuine
positive source floor. Dropping the mark products sharing
a prime of \(x\) in the resulting principal costs
\(O(N^{-a+o(1)})\) in the positive reciprocal harmonic,
with only finitely many physical labels on that source.
Those sharing \(N\) are already excluded and cost the same
if dropped after the main evaluation. This gives (2) on
the receiving arm. The ordinary signed source moment on
its mark subinterval has precisely the other (2):
direct integer CRT opens \(hd\le N^{.5+\sigma}\), with
target-unit density \(\varphi(N)/(Nhd)\);
the first \(\mu(d)/d\) moment at mask \(Nh\) is
\(-Nh/\varphi(Nh)\), reducing the outside coefficient
to \(1/\varphi(h)\). Signed completions with the actual masks,
real spatial logs, and the own-log and squarefree limits
are the same as in the earlier one-arm rail. The arbitrary
log remainders pay the ordinary reciprocal sum of these
products at fixed \(a\). We have retained a literal
prime-product source and not assumed a joint model of
the two composites.

The angular diagonal omitted in this evaluation is small
**on the true pair**. For fixed compatible \(h,h'\), the
actual primitive quotient forms in the true lattice
\(h m+h'n=N\) have free length \(\asymp_J N/(hh')\).
Their two-affine Fourier upper, by
[the product-stopped companion, §2](AffineCompanionProductStop.md),
is \(O_{J,a}(M/(hh'))\) at this fixed floor and fixed
mark rank bound. Any shared target-unit mark is impossible.
For \(|u(h)-u(h')|\le O(\eta)\), fix all actual prime
angles but one of the nonempty products' true prime slots;
its available interval has width \(O(\eta)\) and positive
floor \(a\). True reciprocal primes therefore give
\(O_{J,a}(\eta M)+o_\eta(M)\), uniformly at fixed
\(b,b',\delta\). Cross-gcd conditions are dropped only in
this positive harmonic, not in the physical fiber.
The same positive harmonic upper pays the diagonal of
the ordinary signed principal. To reconstruct the full
pair, cover the angles by a fixed fine mesh of separated
rectangles, discard this collar, and then let its width
go to zero after the large-target limit.
This proves the claimed actual factorization of the
short tested marked products.

## 2. Removing the product stop on the original sharp profiles

Use the true stopped Boolean expansion (2) of
[the product-stopped companion](AffineCompanionProductStop.md)
on each arm, through product \(N^\sigma\), starting at
floor \(a\). Write \(P_{a,b}\) for its stopped active
sum with the unit term, so the small-factor **hit**
has approximate factor \(1-P_{a,b}\), containing only
the nonempty marked products. Apply §1 to its two factors.
The signs of the active terms are exactly
\((-1)^{s+1}\) for a subset of rank \(s\).

On a first crossing the true extra cost at the Fourier
frequency of its own marked arm is bounded by
\(E(\sigma/b)(2+b|\xi|)^{c_0}\) in limsup,
with any fixed \(c_0>4/\pi\), by the actual extracted
prime-phase Rankin proof (3) of the companion note.
It depends only on the positive crossing bound and not
on affinity of the profile. Keep its genuine quotient
fiber and extraction, with \(h\le N^{\sigma+b}\).
Use the same argument in both orientations and for
the two crossing factors on one compatible physical pair.
The positivity bounds for the product of the two hit
errors use \(|1-P_{a,b}|\le 1+|\mathcal E_{a,b}|\),
so cost only the two single crossings and their
double product. There is no unbounded Markov loss from
the number of actual eligible labels.

Here one must actually pay the shrinking taper norms.
Choose fixed \(4/\pi<c,c_0<2\) so that the positive
two-affine frequency bound holds with exponent \(c\)
and \(d=c+c_0>2\). Put \(e=d-2>0\).
The tapered quartic satisfies
\[
 \int |\widehat f_\delta(\xi)|(2+|\xi|)^d,d\xi
                              \ll_d \delta^{-e}.
\]
Indeed up to \(1/\delta\) the third derivative has
uniform \(L^1\) norm, and beyond that split the
\(j\)-th derivative has norm \(O_j(\delta^{3-j})\)
for any fixed \(j>d+1\). These follow from the
quadratic half-zero and the rescaled taper.
The original positive comparison loses
\(O_J(\delta^\kappa M)\) for one fixed \(\kappa>0\),
also after either of the two physical hit restrictions:
it is an absolute whole paired error for the actual
sharp and smooth scores. On the other hand the
true one-crossing loss for the *tapered* scores is at
most \(O_J(\delta^{-e} E_* M)\), and their two-crossing
loss at most \(O_J(\delta^{-2e}E_*^2 M)\),
where \(E_* = E(\sigma/b)+E(\sigma/b')\).
All constants are independent of the artificial floor.
Choose \(\delta=E_*^{1/(e+\kappa)}\) once the fixed cuts
are sufficiently small, and fix this \(\delta\) before
the even-target limit. The three losses sum to
\(O_J(E_*^\nu M)\), \(\nu=\kappa/(e+\kappa)>0\).
Thus no high-frequency estimate was applied directly
to the sharp profile with two incompatible powers.

It remains to identify the ordinary coefficients.
Since \(u(e)\le\sigma\), the derivative in (2) is
the finite difference of the cubic \(P'\), exactly
zero at mark rank \(\ge4\).
The product cap at ranks 1,2,3 is automatic because
\(3b,3b'<\sigma\). Their signed ordinary sums at
floor \(a\) are those in
[the original occupancy calculation, §3](Proof.md):
for \(w=b-a\) they are
\[
 -22w+36(b^2-a^2)-16(b^3-a^3),\quad
 -72w^2(1-a-b),\quad -48w^3
]
before multiplication by \((-1)^{s+1}\).
Send \(N\) large at fixed floor and cut, and then
\(a\downarrow0\). The small true prime exception lost
when replacing a band hit by \(I_b\) is
\(O_J(a^\gamma M)\) by the genuine paired Fourier
test on the marked arm. This introduces no extra
ordinary factor in (2). The alternating sum becomes
\(-22b+108b^2-136b^3=m(b)\).
Together with the controlled taper and crossing errors,
this proves (1) for the original sharp score.

## 3. Exact disjoint use with the geometric hits

Use the old cuts \(b_0=.004/k\), \(b_1=.018/k\) from
[the full signed geometric-bank comparison](WholeGeometricBanks.md).
Its base \(I_0\) source can be narrowed to true least-factor
floor \(b_1\) in place of \(b_0\) without changing its
proved \(14b_0M\) threshold: its ordinary signed mass
comparison loses only \(O_J(b_1^\gamma)M\) in that
source's normalization, and its proof uses the
same actual short source prime in \(I_0\).
The annular \(I_1\) source already has floor \(b_1\).
Use these base and annular signed comparisons, and
their reflections, **in place** of the original wider
base and its reflection. They now all have exactly
one arm with least factor \(\le N^{b_1}\).
Consequently (1) at equal cut \(b=b'=b_1\) pays the
entire literal doubly-tiny block disjointly.
For all sufficiently large fixed \(k\), that block
alone exceeds \(480 b_1^2 M\) for all sufficiently
large even targets: the positive slack follows from
\(m(b)^2=(484+O(b))b^2\) and the superexponential
error as \(b\downarrow0\).
The true one-sided tiny region where the respective
geometric hit fails, and the region with neither tiny
arm, are still not priced. No binary inference is made.
