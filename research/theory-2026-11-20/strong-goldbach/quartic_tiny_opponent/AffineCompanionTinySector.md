# Removing the entire tiny-factor sector in an equal-covariance quartic companion

Retain the physical paired interval, target units, \(N,L,J,M,\Pi,R_J\)
and the original squarefree quartic \(H\) and \(Q=R+W_1+W_2\) in
[the compensated comparison](../halfzero_detector/CompensatedDebit.md).
In particular \(Q\) is always the correction defined from the
**original** score, on those same literal prime products, and
\(Q(n)=0\) for \(P^-(n)\le N^{.005}\). Put
\(\widetilde H=H+Q\). No old negative bank is reselected.

Fix \(0<\sigma<.04\). Let \(f_\sigma\) be a fixed smooth profile on
the nonnegative real line satisfying
\[
 f_\sigma(t)=1-t\quad(0\le t\le\sigma),\qquad
  f_\sigma(t)=0\quad(t\ge .5-2\sigma).
\]
It can be chosen to agree with the original quartic \(P\) on
\([2\sigma,.5-3\sigma]\), by smooth matching over the two intervening
intervals. Extend it smoothly to a fixed compact interval on the
real line. Use its literal own-log score
\[
  H_\sigma(n)=1_{n\ {\rm squarefree}}
       \left((\log n)\sum_{d\mid n}\mu(d)
                      f_\sigma(\log d/\log n)-\Pi(n)\right),
 \qquad S_\sigma=H_\sigma+Q.
\]
Thus \(S_\sigma\) is not pointwise the original compensated score.
Write \(D_b(n)=1_{P^-(n)>N^b}\).

**Theorem.** For every sufficiently small fixed
\(0<b<\min(.005,\sigma/10)\), after the even target goes to infinity,
there is an absolute constant \(c>0\) such that
\[
\begin{split}
 \langle\widetilde H,\widetilde H\rangle
   &=\langle D_b S_\sigma,\widetilde H\rangle
         +O_{J,f_\sigma}(e^{-c\sigma/b}M)+o_{J,f_\sigma,b}(M),\\
   &=\langle D_b S_\sigma,D_b S_\sigma\rangle
         +O_{J,f_\sigma}(e^{-c\sigma/b}M)+o_{J,f_\sigma,b}(M).
                                                               \tag{1}
\end{split}
\]
The first line preserves the literal original opponent. In the
second line no physical prime factor of either remaining score
is at or below \(N^b\). In particular its remaining physical
ranks are at most \(\lfloor1/b\rfloor\), without a rank tail.
The loss is for the **signed** full tiny-factor union, not an
absolute bound on its score. The claim is not that the original
sharp score vanished on the deleted region, or that its paid
geometric-hit subregions can also be added to (1).

## 1. Exact total calibration with the original physical compensation

The fixed smooth profile \(f_\sigma\) has the same values
\(f_\sigma(0)=1\) and \(f_\sigma'(0)=-1\) as the sharp profile.
For the unmarked composite--composite calculation, open the two
literal short moduli and use the exact signed joint CRT principal
of [the original detector, §3](../halfzero_detector/Proof.md).
The coefficient is the product of the first derivatives after the
two vanishing zeroth moments. If one profile is the sharp quartic,
first smooth just that profile at a fixed subroot cutoff, keeping
its derivative. The absolute true-pair taper estimate of the
same proof returns it to the sharp score as the width tends to
zero; the other fixed smooth profile has a finite weighted
Fourier norm in that estimate. Each true prime cross has the
coefficient minus the derivative of the other profile, by actual
prime BV. The literal binary atom is unaltered. The squarefree and
own-log limits are as in that proof: first remove actual tiny
factors by the weighted Fourier bounds, then drop the large
prime squares and switch logarithms on finitely many rough
ranks. This gives
\[
 \langle H_\sigma,H_\sigma\rangle
 =\langle H_\sigma,H\rangle
 =\langle H,H\rangle+o(M).
\]
The signs here refer to the actual detector with its true prime
subtraction, not the isolated divisor profile.

The fixed original correction \(Q\) is a genuine compact
finite-rank prime-product source, with positive factor floor
at least \(.005\) and fixed piecewise continuous weights on
actual angular boxes. For either profile \(H_f\) its signed
cross is
\[
 \langle H_f,Q\rangle
     = -f'(0)\,\mathfrak S(N)\sum_{y\in N(1-J),(y,N)=1}Q(y)
           -\langle\Pi,Q\rangle+o(M),
                                                               \tag{2}
\]
and likewise with the spatial interval reflected. This is the
[same product-BV transfer](../halfzero_detector/OneArmRoughDebit.md)
with genuine reduced mask \(Ny\), the exact first signed
\(\mu/\varphi\) moment, and a strict short cutoff before taking
the sharp seam limit. The true prime piece is exactly the same
on both profiles. Thus keeping all physical \(Q\)-pairs,
including \(\langle Q,Q\rangle\), gives
\[
 \langle \widetilde H,\widetilde H\rangle
   =\langle S_\sigma,\widetilde H\rangle+o(M)
   =\langle S_\sigma,S_\sigma\rangle+o(M).                         \tag{3}
\]

## 2. Fixed true marked products: all opposite rows

Fix \(k=\lfloor\sigma/b\rfloor\), \(a=b e^{-k/100}\), and put
\(\mathcal B=\{p\ {\rm prime}:N^a<p\le N^b\}\).
Write \(j(n)=\#\{p\in\mathcal B:p\mid n\}\).
A product \(h\) of \(s\) distinct true marks, \(1\le s<k\),
satisfies \(h\le N^\sigma\). It is a genuine divisor of the
first physical arm \(x\), and the first arm has no \(Q\) or
\(\Pi\) contribution. Its divisor coefficient when \(x=hm\) is
\[
 g_h(v)=\sum_{e\mid h}\mu(e)f_\sigma(v+\log e/L),\qquad
  g_h'(0)=0,qquad
  g_h(v)=0\quad(v\ge .5-2\sigma).
                                                               \tag{4}
\]
Indeed at each individual displacement \(\log e/L\le\sigma\)
the derivative is \(-1\). The zeroth value need not vanish.
The displayed analytic coefficients use target-log angles
for the opening; the literal own-log score is restored below.

Here are the exact summations for every fixed \(s\).
For the opposite divisor score on \(y\), with divisor \(d'\)
and smooth profile cut at or below half, open the actual
divisors \(d\mid m\) and \(d'\mid y\). The genuine coprimalities
are \((d,h)=1\) on squarefree rows and \((hd,d')=1\) because
of the target units. All primes dividing \(N\) are excluded
from both moduli. The product modulus is
\(h d d'\le N^{1-\sigma}\) even when the opposite cutoff
is approached arbitrarily closely. Summed floors after
opening the target-unit mask cost \(N^{1-\sigma+o(1)}\):
the number of choices is bounded by the product of these
three size bounds times a fixed divisor power, or by grouping
at the true combined moduli. For the ordinary count on a
compatible progression the density is
\((\varphi(N)/N)/(h d d')\).

For the signed main, complete the marked \(d\)-sum with its
actual coprimality mask \(N h d'\) to the subpower
\(\exp((\log L)^4)\) interval, and complete \(d'\) with the
corresponding actual mask. This is the same masked
\(\mu/d\) calculation as in the short CRT proof: one can
complete the two variables successively against arbitrary
logarithmic powers since the other absolute harmonic is
only polynomial in \(L\).
The product of signed first-log moments is multiplied by
\(g_h'(0)\), so the main is zero by (4).
In particular there is no surviving constant term from
\(g_h(0)\): the genuine zeroth moment is zero. The model
errors are uniform in the polynomial mask and sum with
\(\sum_h \tau(h)^C/h\ll_{a,s,C}1\) for fixed \(s\):
\(h\) has exactly \(s\) genuine prime factors in a bank of
fixed reciprocal mass. Real spatial log weights are kept
until signed completion. The usual \(O((\log L)^{C'}/L)\)
Taylor error follows from the same first-order expansion
after both zeroth cancellations. At fixed \(s\) the
derivatives of (4) are uniformly bounded in \(N,h\).

For the actual \(\Pi(y)\) term the tested progression is
\(hd\) and the residue is the literal \(N\); its modulus is
at most \(N^{.5-\sigma}\). Ordinary maximal prime BV
therefore applies with a fixed power reserve and actual
divisor-bounded multiplicities at the joined modulus.
Its reduced principal contains \(1/\varphi(h)\) times
the signed \(\mu(d)/\varphi(d)\) harmonic with mask
\(N h\). Again the zero constant moment and (4) give
\(o(M)\) after summing the genuine \(h\). Proper powers
from a von Mangoldt BV statement have a power-small
total after the fixed divisor weights.

For \(Q(y)\) the product-BV version of that argument uses
the same actual \(hd\) and the literal mask \(Nh y\).
This is within the level of (2) with fixed power slack;
multiplicities are again divisor-bounded, even though the
\(h\) and \(d\) cutoffs appear in the coefficient.
The same signed derivative in (4) gives zero principal.
No sign on \(Q\) is needed to deduce the principal, and
the source remains the same physical \(Q\).

These applications can first use a fixed smooth strict
cut for a sharp opposite profile, as in §1. They also
justify returning from the analytic target-log divisor
profiles to the stated physical ones. In detail, at fixed
\(a,s\) each real row has at most
\(\binom{\lfloor1/a\rfloor}{s}\) actual mark products.
Consequently the ordinary absolute paired estimates
with one smaller actual factor, and the rank tails,
are sufficient before replacing own logs and dropping
nonsquarefree rows. On the remaining polynomially
rough finite ranks, repeated prime squares or a selected
prime also dividing the remaining quotient have
power-small support, while the coordinate change is
\(O_J(L^{-1})\) in the bounded normalized profiles.
For the true prime leg the same paired estimates use
its physical rough-indicator majorization. One can
retain \((d,h)=1\) in the CRT/BV coefficient throughout;
there is no invented product modulus on a repeated mark.
Take the tiny-factor/rank and, where used, taper limits
at fixed \(a,s,b\) **after** the large-target limit.
Thus for \(Y=\widetilde H\) or \(Y=S_\sigma\),
\[
                 \langle \binom{j}{s} S_\sigma,Y\rangle=o(M)
                        \qquad(1\le s<k).                         \tag{5}
\]

The corresponding true double-mark moment against
\(S_\sigma\) also has zero principal:
\[
     \left\langle \binom{j}{s}S_\sigma,
                    \binom{j}{t}S_\sigma\right\rangle=o(M)
                       \quad(1\le s,t<k).                          \tag{6}
\]
In fact the second actual product, say \(h'\mid y\),
kills both its prime and its \(Q\) terms.
On target-unit rows \((h,h')=1\); common marks would
divide \(N\) and are already excluded. The actual
moduli are coprime \(h d,h' d'\), each coprime to
\(N\), and the sum of the four exponent budgets is
at most \(1-2\sigma\). The signed CRT harmonic keeps
both external masks \(h,h'\) on each free divisor,
as well as the other free divisor in its conditional
mask. Its respective marked profiles are \(g_h\) and
\(g_{h'}\). Both derivatives vanish, so the argument
of the first case applies after summing these true
mark products with their reciprocal harmonics.
The total floor reserve \(N^{-2\sigma+o(1)}\) and
squarefree/coordinate errors are as above. One may
apply the same proof on the reflected spatial interval.

## 3. Uniform actual factorial tails and the whole tiny union

Use the exact single-side inclusion--exclusion
\[
 1_{j(n)\ge1}=
   \sum_{s=1}^{k-1}(-1)^{s+1}\binom{j(n)}s+\mathcal E(n),
             \qquad |\mathcal E(n)|\le\binom{j(n)}k .
\]
For the positive excess at depth \(k\) each literal product
\(h\) still satisfies \(h\le N^\sigma\). On that physical
fiber the true two-affine weighted upper of
[the original mark proof](Proof.md) applies at scale
\(N/h\ge N^{1-\sigma}\): extract the actual \(k\) prime
Fourier factors, each at cost at most 2, with the exact
same weighted logarithmic divisor envelope for the
remaining variable. The opponent can be either profile
plus \(Q\), using \(Q\le |H|\). A true prime term is
majorized by its physical polynomially rough indicator,
as in the quartic proof. This gives
\[
    \sum |\mathcal E(x)S_\sigma(x)Y(y)|
      \ll_{J,f_\sigma}
         \frac{2^k M}{k!}
          \left(\sum_{p\in\mathcal B}\frac1p\right)^k
      \ll_{J,f_\sigma} (3e/100)^k M
                                                               \tag{7}
\]
for sufficiently large \(N\) at fixed \(k\).
Here \(\sum_{p\in\mathcal B}1/p=k/100+o(1)\).
The constants other than the displayed factorial/extraction
do not grow with \(k\); at the leading primes the local
product \(\prod_{p\mid h}(1+O(1/p))\) is at most 2
after taking \(N\) large at fixed \(a,k\).

There is also a true double excess bound with two factors
of \((3e/100)^k\). For distinct compatible marked products
\(h\mid x,h'\mid y\), the two literal quotient forms are
\(x/h=m_0+h' v\) and \(y/h'=n_0-h v\) with
\(hm_0+h'n_0=N\), on the real interval of length
\(\asymp_J N/(hh')\ge c_JN^{1-2\sigma}\).
Their primitive roots are distinct off \(Nhh'\);
there is one root at each leading prime and a coincident
root at primes of \(N\), removed by the exact unit mask.
The fixed-power true two-affine envelope is uniform at
this scale. Extracting both sets of genuine marks costs
\(2^{2k}\) and the same locally bounded product, while
the actual pair weight is \(O_{J,f_\sigma}(2^{2k}M/(hh'))\).
Summing unordered actual labels on each side gives the
claimed squared factorial bound. In the positive upper,
discarding compatibility only increases the final
reciprocal sum, not the count in an incompatible fiber.

If \(P_{k-1}\) is the truncated indicator polynomial on
one arm, then \(|P_{k-1}|\le1+|\mathcal E|\) on the
actual row. The product of the two true indicators differs
from the product of the truncated ones by at most
\(|\mathcal E(x)|+|\mathcal E(y)|+
 |\mathcal E(x)\mathcal E(y)|\).
Thus (5)--(7) pay both single cuts and their literal
intersection; no product of signed errors was replaced
by independent arithmetic.

Finally replacing \(1_{j(n)\ge1}\) by
\(1_{P^-(n)\le N^b}\) costs at most an actual factor
\(\le N^a\), whose absolute weighted price is
\(O_{J,f_\sigma}(a^\gamma M)\) by the original
two-affine tiny-factor bound, for one absolute
\(\gamma>0\). This also bounds the discrepancy of
the two-side intersection by the union of these
actual events. The two errors in (7) and here are
\(O_{J,f_\sigma}(e^{-c\sigma/b}M)\) for some
absolute \(c>0\) since \(k\ge\sigma/(2b)\).
The first line of (1) deletes the single tiny sector
from the first identity in (3). The second uses
inclusion--exclusion with (6) on the second identity
in (3). This proves the two scoped statements
without any unproved sign on the remaining rough pair.

## 4. Cubic paired preservation on every fixed rough arm

There is a choice of the preceding smooth family, uniform as
\(\sigma\downarrow0\), for which the following also holds.
Fix \(0<\alpha<1/4\) with \(2\sigma<\alpha\). Then on the same
actual target units,
\[
 \sum_{\substack{x\in NJ\\P^-(x)>N^\alpha}}
  |S_\sigma(x)-\widetilde H(x)|
     \left(|S_\sigma(y)|+|\widetilde H(y)|\right)
       \ll_{\alpha,J}\sigma^3 M+o_{\alpha,J,\sigma}(M).         \tag{8}
\]
This has no uniform assertion as \(\alpha\downarrow0\).
In particular the **physical** rough--rough region
\(P^-(x),P^-(y)>N^{.145}\) contributes at least
\(-O_J(\sigma^3 M)+o(M)\) to the companion covariance:
the original compensated scores on this region are nonnegative,
and (8) can be used in both orientations. This does not estimate
the intermediate least-factor range of (1).

For clarity take a common compact real extension of the sharp
profile, equal to \(P\) on \([-.1,.5)\) and zero for \(t\ge .5\).
Add a fixed smooth multiple of \(1-t-P(t)\) which is all of
that expression at \(|t|\le\sigma\), zero at \(|t|\ge2\sigma\).
On the other end multiply by a fixed smooth cutoff in
\((.5-t)/\sigma\), equal to one from 3 onward and zero up to 2.
These two alterations have disjoint supports. Both differences
are \(O(\sigma^2)\) there, by the shared value and derivative
on the left and the double zero on the right. After scaling
either altered interval to a fixed interval, the difference
is \(\sigma^2\) times a uniformly \(C^1\) function whose
second derivative has uniformly bounded variation.
Thus for any fixed \(c<2\) the weighted \(L^1\) Fourier norm
of the difference with weight \((2+|\xi|)^c\) is
\(O_c(\sigma^{2-c})\), as in the detector seam estimate.
In particular the positive Fourier opponent bound used below
is uniform for this family.

On the actual rough row, no nontrivial divisor touches the
left alteration: \(\log p/\log x>\alpha\) for every genuine
\(p\mid x\); the value at the trivial divisor is unchanged.
The correction \(Q\) and prime atom cancel in the difference.
It can be nonzero only at actual squarefree composite \(x\)
with a proper divisor \(d\mid x\) in the own-log collar
\([.5-3\sigma,.5]\). Each such contribution to the weight
is at most \(O(\sigma^2 L)\). A necessary target-log collar is
\[
          .5-3\sigma-O_J(1/L)\le\log d/L\le .5.
\]
For each such actual divisor take a genuine prime
\(r\mid x/d\) and put \(m=x/r\). The collar is now a
condition on \(d\mid m\), independent of the unfrozen \(r\).
There is always such a prime, and allowing all its possible
choices in the positive upper only enlarges the bound.
The other factors, with \(d\mid m\), are frozen true primes
all above \(N^\alpha\), and \(m\le N^{1-\alpha}\).

At each fixed genuine \(m\) occupying this range, the prime
variable \(r\) lies in the true central interval \((N/m)J\);
the parameter scale is \(N/m\ge N^\alpha\). Apply the
corrected two-affine envelope of
[the finite-angle proof, §2](../nearfull_high_vaughan/WideJointGiantFiniteAngles.md)
to \(r,N-mr\), keeping their true target units.
Here the first weight may be the indicator of
\(N^{\alpha/2}\)-rough integers, which majorizes the
actual prime \(r\); the opposing divisor weight is given
by Fourier inversion as in the quartic proof. The possible
true \(\Pi(y)\) is covered by the same rough-indicator upper.
For \(Q(y)\) use its domination by \(|H(y)|\).
The actual forms are primitive since \((m,N)=1\);
their roots have resultant \(N\) and a single root instead
of two at each leading prime of \(m\). The latter
change costs \(\prod_{p\mid m}(1+O(1/p))\ll1\):
there are at most \(1/\alpha\) of them and all are
polynomially large. The degree, coefficient/length conditions
and initial Mertens root product have fixed slack depending
only on \(\alpha,J\), since the primitive form has size
\(O(N)\) and the free interval is polynomially long.
For the first affine weight the remaining Euler transport
above \(N^{\alpha/2}\) is \(O_\alpha(1)\); for the second
it is bounded in frequency by \((2+|\xi|)^c\) with some
fixed \(c<2\), using the true prime harmonic.
After multiplying by the log weights and the Fourier norms,
the actual upper for each fixed \((m,d)\) is therefore
\(O_{\alpha,J}(\sigma^2 M/m)\).

Finally sum that bound over actual tuples of at most
\(\lfloor1/\alpha\rfloor-1\) remaining prime factors.
For any nonempty subset of them giving \(d\), distinguish
one of its genuine primes. After the others are fixed,
its target-angle range has width at most
\(3\sigma+O_J(1/L)\) and floor \(\alpha\), so its true
reciprocal harmonic is \(O_\alpha(\sigma)+o_{\alpha,J}(1)\)
uniformly over the other factors. This follows directly
from the uniform reciprocal prime estimate on endpoints
\(\ge N^\alpha\). The other polynomially rough harmonic
slots are \(O_\alpha(1)\), and the number of subsets is
bounded at fixed \(\alpha\). This proves (8) with the
cubic dependence. For the rough--rough application,
expand the difference of the two paired products, use
(8) on each altered arm, and use the literal original
rough nonnegativity from the compensated proof.
