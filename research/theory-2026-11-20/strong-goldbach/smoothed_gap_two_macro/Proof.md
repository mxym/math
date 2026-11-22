# True fixed-target deletion of the full at-most-two-macro score in a smoothed gap

Let \(N=2x\) be even, \(L=\log x\), \(\ell=\log L\),
\(J=xJ_0\) for fixed \(J_0\subset[1,3/2]\), and \(P=N-y\).
All weighted sums use the **actual prime** \(P\) and its weight
\(\log P\). Use the entire all-small completion as in the
[wide reciprocal-gap score](../wide_gap_all_terminal/Proof.md), but
with the following fixed-at-\(x\) parameters:
\[
 U=\ell^{-1/4},\qquad
 w=\frac{U}{100\log\ell},\qquad W=x^w,\qquad
 \epsilon^2=\frac{U}{\sqrt{\log\ell}},\qquad
 C_y=\frac{y}{x^{1-\epsilon}}.                            \tag{1}
\]
A divisor prime is small if it is strictly below the **actual**
\(C_y\), and macro otherwise. Choose once an even \(C^\infty\)
function \(\psi\) equal to 1 on \([-1,1]\), zero outside \((-2,2)\),
and nonincreasing on \([0,\infty)\). Let \(d\nu(g)\) be the
probability on \([U,2U]\) with survival function
\(\Pr(g>t)=\psi(t/U)\) for \(t\ge0\).

For each \(g\), denote the actual completed score by
\[
 H_g(y)=1_{P^-(y)>W}\left\{
   \sum_{\substack{d\mid y\\d>\sqrt y x^{-g}}}
                           \mu(d)\log(y/d)
   +\sum_{\substack{cba=y\\a>\sqrt y x^{g}\\P^+(c)<C_y}}
                           \mu_2(c)\log b
                  \right\},\qquad \mu_2=\mu*\mu.
\tag{2}
\]
Here \(c=1\) is always admitted. Write \(\overline H=\int H_g\,d\nu(g)\),
\(Q_\epsilon(t)\) for the cumulative of
\(\exp^*(2\,1_{u>\epsilon}du/u)\), including its unit atom, and
\(\mathcal G_J(N)=\sum_{P+y=N,\ y\in J,\ P,y\ {\rm prime}}\log P\log y\).

**Theorem.** Both the following hold uniformly in the even target.
First the actual calibration is
\[
 \sum_{\substack{y\in J\\P=N-y\ {\rm prime}}}\log P\,\overline H(y)
 =\mathcal G_J(N)+|J|\mathfrak S(N)
       \left(\int Q_\epsilon(\tfrac12-g)\,d\nu(g)-1\right)
 +O_{\psi,J_0}\!\left(
 x\mathfrak S(N)\left(\frac{w}{\epsilon^2}
                       +\frac{\epsilon^{-3}}{L}
                       +\ell^{-1}\right)\right).          \tag{3}
\]
In particular the reference in (3) is the average at
\(\tfrac12-g\), not its replacement by \(\tfrac12\).
Second, on the complete genuine factor cohort with at most two macro
primes, the entire score (including **all signed** safe and raw
orientations) has the actual bound
\[
 \sum_{\substack{y\in J,\ P=N-y\ {\rm prime}\\y\ {\rm squarefree},\
                     P^-(y)>W,\ \#\{p\mid y:p\ge C_y\}\le 2}}
           \log P\,|\overline H(y)|
 \ll_{\psi,J_0} x\mathfrak S(N)
             \left(\frac{\epsilon^2}{U}
                       +\epsilon\log(2/\epsilon)+\ell^{-1}\right)
 =o(x\mathfrak S(N)).                                    \tag{4}
\]
This is a whole surviving-row bound, not a payment by a selected
positive subset of orientations or a thin-shoulder transfer. Do not
spend other receivers or terms on this same cohort after applying
(4). The at-least-three-macro cohort is not controlled by this theorem.

## 1. The reference at the actual gap

Here is the calibration argument with the parameter difference
made explicit. For squarefree \(W\)-rough \(y\), the free term
of (2) for \(d=y/a<\sqrt y x^{-g}\) is exactly
\[
 C(d;y)=\mu(S_d)(\log d-2\log S_d),\qquad
 S_d=\prod_{\substack{r\mid d\\r<C_y}}r.
\tag{5}
\]
This follows by expanding over \(c\mid S_d\): the constant subset
sum is \(\mu(S_d)\) and each marked logarithm has the opposite sign.
By the full Möbius logarithm identity, (2) is therefore
\(\Lambda(y)\) minus the short raw term \(\mu(d)\log(y/d)\) plus
(5), both on the literal short cutoff \(d<\sqrt y x^{-g}\);
any equality has measure zero in \(g\) (or for a fixed \(g\), at most one \(y\) per \(d\), hence power-small). Proper prime powers and
non-squarefree \(W\)-rough rows may be dropped with errors smaller
than any fixed log power. For example the latter occur at most
\(O(x/W)\) times, and fixed divisor moments with Cauchy give this
saving for the fixed divisor-power log score. The \(O(1)\) genuine
prime \(P\mid N\) cases likewise cost \(x^{o(1)}\); at other primes
\((y,N)=1\). The rough mask leaves the genuine prime atom unchanged.

Apply the dimension-one fundamental lemma to \(y/d\), per sign,
with level \(x^{g/2}\). Its density is \(1/(r-1)\) for \(r\le W\),
\(r\nmid N\), as follows by the actual prime class \(P\equiv N\)
modulo the opening divisor. The exact moduli are
\(dh\le \sqrt{1.5x}\,x^{-g/2}\), in the usual maximal weighted
Bombieri--Vinogradov range with arbitrary log reserve.
The squarefree rough \(d\) and squarefree \(W\)-smooth \(h\)
are uniquely recovered from \(dh\). Any jumps of (5) as a
function of \(y\) are at \(r x^{1-\epsilon}\) for actual \(r\mid d\);
the other log factor uses partial summation. These are at most
divisor-power prefix costs. The two absolute main terms before
signed cancellation are \(O(x\mathfrak S(N)w^{-C})\) for a fixed
\(C\), by positive Euler bounds (in fact \(C=2\) suffices).
The *actual* fundamental-lemma parameter \(g/(2w)\ge50\log\ell\)
therefore permits \(O_A(x\mathfrak S(N)\ell^{-A})\), since the
relative remainder decays as \(\exp(-c s\log s)\).
No hypothesis \(U/\epsilon^2\to0\) is used at this stage.

We use the identical prime harmonic comparison as in
[the two signed sectors, §2](../completed_gap_two_true_sectors/Proof.md):
replace the harmonic prime measure at exponents \(u=\log r/L>w\)
by \(du/u\) in any such fixed monotone interval, with arbitrary-log
error. Its Stieltjes convolution comparison, including one
log-marked slot and the squarefree repeat errors, is unchanged
here. In particular its error is uniform in the threshold
\(\epsilon_y=\log C_y/L=\epsilon+O(L^{-1})\) and in
\(D_y=\tfrac12\log y/L-g\): the signs of the prime measure have
one moving endpoint, the total absolute prime harmonic is
\(O(\log(1/w))\), and a fixed bounded exponent weight on each
prime has convolution exponential of total mass \(w^{-O(1)}\).
Prime Mertens errors at \(W\), also after multiplication by
any powers of \(1/w,1/\epsilon\), save all powers of \(L\).
The errors from \(1/\phi(d)\) instead of \(1/d\), and target
primes \(r\mid N,\ r>W\), have the same savings.
The actual local normalization is
\(V_N(W)L=\mathfrak S(N)e^{-\gamma}/w\) to this accuracy.

For clarity let \(\rho_w(u)=\rho(u/w)\) be the Dickman function
extended by zero below 0. The signed raw harmonic cumulative
is \(\rho_w\) (the unit atom is retained). Its integral is
\(e^\gamma w\), its first moment \(O(w^2)\), and it has factorial
tails on any fixed positive log-exponent interval. The short
raw term thus gives \(1+O_A(\ell^{-A})\) after normalization by
\(|J|\mathfrak S(N)\). On the short free term (5) the signed
harmonic is \(\exp^*(-\nu_w+2\nu_{\epsilon_y})\), with
\(\nu_b=1_{u>b}du/u\); marking the logarithm flips the same
sign and gives the Lebesgue slot \(1_{u>w}du\). Its normalized
free factor at physical \(y\) is, to arbitrary-log errors,
\[
 \frac{e^{-\gamma}}{w}
       \int_0^{D_y-w}\rho_w(u)\,
                  Q_{\epsilon_y}(D_y-w-u)\,du.            \tag{6}
\]
On a compact interval around \(1/2\),
\(Q_\epsilon\ll\epsilon^{-2}\) and its density is
\(O(\epsilon^{-2})\): marking in the positive convolution
exponential gives \(tQ_\epsilon'(t)=2Q_\epsilon(t-\epsilon)\)
where the density is defined, and the elementary mass bound is
\(O(\epsilon^{-2})\). Moving \(\epsilon_y\) to \(\epsilon\)
costs \(O(L^{-1}\epsilon^{-3})\), by the mass of the short
changed prime interval and convolution telescoping.
The first moment and tail of \(\rho_w\) give (6) equal to
\(Q_\epsilon(1/2-g)+O(w/\epsilon^2+L^{-1}\epsilon^{-3}
+\ell^{-A})\). The small moving \(y\)-endpoint of \(D_y\)
is already included. This proves (3), uniformly for \(g\) in
the support of \(\nu\), then for its actual probability average.
Here \(w/\epsilon^2=1/(100\sqrt{\log\ell})\), whereas the larger
replacement error \(U/\epsilon^2=\sqrt{\log\ell}\) would not
tend to zero.

## 2. All orientations with at most two genuine macros

Write \(S\) for the complete actual small part, \(k=\omega(S)\).
First we may omit the **whole-row** contribution from
\(S>x^{.05}\) in absolute value. Indeed (1) and the exact paired
weights bound \(|\overline H(y)|\ll L2^k\) on this cohort.
Use [Henriot, Theorem 5 and Corollary 2](https://arxiv.org/pdf/1102.1643)
with the [published erratum](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B0BD208D979495FE06B8192209E710EA/S0305004114000280a.pdf/nairtenenbaum-uniform_with_respect_to_the_discriminanterratum.pdf)
on the two *fixed-slope* forms \(Y,N-Y\) with free interval
length comparable to \(x\) at height \(x\).
On \(Y\) use the multiplicative \(W\)-rough and \(N\)-unit mask
and weights \(2r^{a/(\epsilon L)}\) at each allowed prime power
\(r^a\) with \(r\le1.5x^\epsilon\), weight 1 at the other allowed
prime powers. On \(N-Y\) use an \(x^{.01}\)-rough and \(N\)-unit
majorant of the actual prime. The first weight is at most
\(2e^{2a}\) at each allowed prime power and at most \(Y^\eta\)
for any fixed theorem-admissible \(\eta>0\) for large \(x\),
since \(r>W\) and \(1/(\epsilon L)\to0\); the fixed
multiplicative class is therefore uniform.
The forms are primitive, their product has polynomial
height, the corrected discriminant support is just \(r\mid N\),
and its nontrivial terms vanish under the two unit masks.
The ordinary root corrections give the single
\(\mathfrak S(N)/L^2\) factor, with 2 omitted and a constant
factor at 2. The prime rough leg's extra Euler product is
bounded by an absolute constant. The other Euler factor is
\(O(w^{-C})\) with fixed \(C\) (use
\(\sum_{r\le1.5x^\epsilon}(r^{1/(\epsilon L)}-1)/r=O(1)\)).
The Rankin tilt on this event is at least \(e^{.05/\epsilon}\)
and includes the actual moving small product. Consequently this
whole exceptional contribution, including both logarithms, is
\[
          O\big(x\mathfrak S(N)w^{-C}e^{-.05/\epsilon}\big)
           =O_A(x\mathfrak S(N)\ell^{-A}).                 \tag{7}
\]
No difficulty from a possibly very short remaining macro
prime is inferred away on these omitted rows.

Now let \(s=\log S/L\le .05\). A zero-macro row is impossible
because \(y\ge x\). If there is exactly one macro \(p=y/S\ge x^{.95}\),
the short side of each complementary pair is some \(A\mid S\).
Every one of these sides is safely short. For even total rank its
paired safe weight is zero at each \(A\), since the macro part of
\(A\) is 1. For odd total rank the sum is
\(-2\sum_{A\mid S}\mu(A)\log A\), again zero, since \(k\) is then
even (including \(k=0\)). This vanishes on every such actual row,
including a prime \(y\), without counting its genuine prime pair
in (4)'s score as an independent reserve.

For two macros write \(y=pqS\), with distinct true \(p<q\), and
\(T=\log y/L,\ u=\log p/L\).
All pairs are in one of the unordered macro splits
\(\{pq,1\}\) and \(\{p,q\}\). For the macro split \(\{pq,1\}\), the shorter side always has
only small prime factors, and all \(A\mid S\) appear safely
short since \(s\le .05\) and \(pq\ge x^{.95}\).
Its total is exactly zero for even \(k\).
For odd \(k\) it is \(\sum_{A\mid S}-2\mu(A)\log A\),
which is zero if \(k\ge3\), and equals \(2\log r\) if \(S=r\)
is one actual prime. In that exception fix \(r,p\) and count
the genuine \(q\) and \(N-rp q\) by dimension-two Selberg upper:
for \(Y=x/(pr)\), its count is
\(\ll Y\mathfrak S(N)/L^2+x^{.36}\), as spelled out below.
The upper cutoff on \(p\) follows from \(p<q\) and \(pqr\le1.5x\),
and \(p\ge x^\epsilon\). Thus the log-weighted cost of this
exception is
\[
 \ll x\mathfrak S(N)
          \sum_{r\le1.5x^\epsilon}\frac{\log r}{Lr}
          \sum_{x^\epsilon\le p\le x^{.51}}\frac1p
                 +O(x^{.94})
 \ll x\mathfrak S(N)\epsilon\log(2/\epsilon)+O(x^{.94}).   \tag{8}
\]

For the split \(\{p,q\}\), take the oriented representative
\(p A\), \(A\mid S\), irrespective of which is shorter.
Set \(a=\log A/L\), \(z=u+a-T/2\),
\[
       \Psi(z)=\psi(z/U),\qquad
       F(z)=(1-\Psi(z))1_{z>0}.
\]
The exact normalized raw-only kernel at one such pair is
\(-T\mu(A)\) for even \(k\) and \(2z\mu(A)\) for odd \(k\).
Indeed the shorter leg is \(pA\) if \(z<0\) and \(q S/A\)
if \(z>0\), with their actual small-factor signs. The safe
weight from (5) plus the remaining raw orientation is
\(-2a\mu(A)\) or \(-2(s-a)\mu(A)\) on those two sides for
even \(k\), and \(2u\mu(A)\) or
\(-2(T-s-u)\mu(A)\) for odd \(k\).
The probability of the raw region under \(d\nu\) is exactly
\(\Psi(z)\), and \(F(z)\) is the safe probability on the
positive side. Thus the sum over all \(A\mid S\), divided by \(L\),
is \(\sum_{A\mid S}(-1)^{\omega(A)}\) times the following
kernel, using that its affine baseline subset sum vanishes:
\[
 \begin{cases}
 (2a-T)\Psi(u+a-T/2)+(4a-2s)F(u+a-T/2),
                                                      & k\ \text{even},\\
 2(a-T/2)\Psi(u+a-T/2)-2(T-s)F(u+a-T/2),
                                                      & k\ \text{odd}.
 \end{cases}                                            \tag{9}
\]
For even \(k\) the affine baseline is \(-2a\) (also zero when
\(k=0\)); for odd \(k\) it is \(2u\) and \(k\ge1\).
In the step terms of (9), the constant value of \(F\) to
the far right cancels in the subset sum; this also holds for
\(k=1\) in the odd case. For even \(k=0\) its coefficient is zero.
Consequently the complete physical score (9) is zero unless
\(u\) lies in a fixed interval \([.44,.56]\) for large \(x\).
On the actual \(p<q\) rows we have \(p\le x^{.51}\).
The numeric replacement \(T\mapsto1\) **after naming the
actual small primes** changes (9) by
\(O_\psi(2^k/(UL))\), with the same support. This is just
Lipschitz continuity of the smooth kernels and bounded
linear coefficients. It does not change membership of any
factor in the gate \(C_y\). For the positive upper over \(S\)
below one may allow all genuine small prime labels
\(W<r\le1.5x^\epsilon\), retaining \(s\le .05\) until after
the true-prime count.

For use in (8) and (9), fix \(S,p\) in the physical range of
each applied case and set \(H=Sp,\ Y=x/H\). The true primes are
\(q,N-Hq\) on an interval \(q\asymp Y\) with \(Y\gg x^{.44}\)
(exact constant factors at the endpoints are harmless).
With \((H,N)=1\), both forms have two excluded roots modulo
a prime away from \(HN\); they have one coincident root at
primes of \(N\) and one root from the first form at primes of
\(H\). At 2 the roots coincide. At primes in \(H\), all \(>W\),
the product correction is \(1+o(1)\).
The proof of the elementary
[true two-bank upper, equation (7)](../wide_gap_safe_bank_packet/Proof.md),
with *both* forms sieved to \(z_0=x^{.01}\), and \(R=x^{.06}\),
therefore gives
\(\ll Y\mathfrak S(N)/L^2+x^{.36}\).
It admits both true primes because both exceed \(z_0\) in
the applied boxes. Its fixed bound \(R^6\) is valid regardless
of which prime factors are already fixed in \(S,p\).
When summed over \(S\le x^{.05}\), \(p\le x^{.51}\), the
floors times \(2^k L^2\) cost at most \(x^{.94}\) for large \(x\)
(use the fixed divisor moments for summing \(2^{\omega(S)}\)).
No congruence independence of these actual primes is used.

The main bound just proved is \(x\mathfrak S(N)/(pS)\)
after both log factors. It follows that (9) is bounded by
\(x\mathfrak S(N)\) times the corresponding absolute **angular**
integral in \(u\), summed against \(1/S\), with a negligible
error. In detail, prime Mertens/PNT on the fixed exponent
interval \([.44,.51]\) gives for each \(S\) the harmonic
integral of the absolute value of (9) at \(T=1\), against
\(du/u\), with error
\(O_\psi(e^{-c\sqrt L}2^k/U)\): the sup and the total variation
are \(O_\psi(2^k/U)\). On this interval \(du/u\ll du\).
Summing \(\sum 2^k/S\ll(\epsilon/w)^2\) controls this error and
the separate \(T\)-replacement error \(O_\psi((\epsilon/w)^2/(UL))\).
An upper over all \(u\in\mathbb R\) is now allowed for the
complete subset sums, since we take their absolute value
**after** summing the entire physical macro split.

## 3. Absolute bound for the complete smoothed finite differences

For each genuine prime label \(r\) put \(u_r=\log r/L\).
Write \(\Delta_h f(t)=f(t)-f(t+h)\). A complete unmarked
subset sum of either kernel is \(\prod_{r\mid S}\Delta_{u_r} f\),
up to translation. A logarithm-marked sum obeys
\[
 \sum_{A\mid S}(-1)^{\omega(A)}\frac{\log A}{L}
                 f\left(t+\frac{\log A}{L}\right)
    =-\sum_{r\mid S} u_r
          \left(\prod_{b\mid S/r,\ b\ {\rm prime}}\Delta_{u_b}f\right)
                                      (t+u_r).            \tag{10}
\]
We prove that the harmonic sum over the allowed genuine squarefree
\(S\) of the \(L^1(dt)\) norm of the unmarked subset difference is
\(O_\psi(\epsilon^2/U)\) for \(f=\Psi\), including \(S=1\), and
for \(f=F\) with \(S>1\). Rank and size restrictions may now
be dropped inside this positive harmonic upper.

Use a smooth Littlewood--Paley resolution into one low pass of
frequency \(\ll1/U\) and bands \(\asymp 2^j/U\), \(j\ge1\).
For each band, denote its component by \(f_j\). Its
\(L^1\) norm is \(O_{\psi,m}(U2^{-mj})\) for any fixed \(m\);
this follows by writing its convolution multiplier as a
fixed-dilate smooth kernel times \((U/2^j)^m\partial_t^m f\),
and using \(\|\partial_t^m f\|_1\ll_{\psi,m}U^{1-m}\).
For \(F\) the upper bands are integrable by the same proof,
since every positive derivative is compactly supported.
The low pass of \(\Psi\) has norm \(O_\psi(U)\).
For a band-limited \(g\) at scale \(2^j/U\),
\[
 \|\Delta_h g\|_1\le
       \min(2,C|h|2^j/U)\,\|g\|_1.
\]
The bound 2 is the translation triangle inequality.
For the other bound convolve with a smooth slightly larger
frequency cutoff equal to 1 on the support and differentiate
its kernel; its derivative has \(L^1\) norm \(O(2^j/U)\).
Every successive difference has the same Fourier support,
so the factors multiply with the per-label cap **exactly 2**.
The positive squarefree harmonic Euler product is
\[
 \prod_{W<r\le1.5x^\epsilon}
       \left(1+\frac{\min(2,C\,2^ju_r/U)}r\right)
       \ll_C (1+\epsilon\,2^j/U)^2.                      \tag{11}
\]
Indeed the sum for exponent \(u_r\ll U/2^j\) is \(O(1)\)
by \(\sum_{r\le v}\log r/r\ll\log v\), and the rest is
at most two times its prime harmonic, giving (11).
This bound is uniform also when the small split lies below \(W\).
With fixed \(m>2\), summing all bands proves
\(O_\psi(\epsilon^2/U)\) for the \(\Psi\) differences
and for the upper bands of the \(F\) differences.

The low pass \(F_0\) need not be integrable, but
\(\|F_0'\|_1\ll_\psi1\). On each nonempty \(S\) first use its
least label \(r\): \(\|\Delta_{u_r} F_0\|_1\ll_\psi u_r\).
For \(u_r\le U\) the harmonic sum over this label is \(O(U)\),
then use (11) with \(j=0\) for the other labels. For \(u_r>U\)
use the factor 2 for each of the other primes, all larger
than \(r\), giving an Euler factor \(\ll(\epsilon/u_r)^2\).
On dyadic bins in the exponent \(u_r>U\) their reciprocal prime
mass is \(O(1)\) per bin. Thus the low-step bound is also
\(O_\psi(\epsilon^2/U)\), including all nonempty \(S\).
These estimates justify the entire series of finite differences
in \(L^1\); for the step each required difference removes
its nonintegrable constant limits.

In (10) the \(u_r/r\) marked harmonic has mass \(O(\epsilon)\).
The remaining subset differences are nonempty whenever \(F\)
is marked (even \(k\ge2\)); for marked \(\Psi\) the empty case
was already included. Translation does not change the \(L^1\)
norms. Factors \(s,T\) in (9) are bounded on the physical
cohort. This proves the angular bound for the entire split
\(\{p,q\}\), namely \(O_\psi(x\mathfrak S(N)\epsilon^2/U)\)
using the true-prime counting step of §2.
Combining (7), (8), and (9)--(11) proves (4). The two relevant
small parameters are now \(w/\epsilon^2\) for the calibration and
\(\epsilon^2/U\) for the physical cohort, both tending to zero.

This deletion uses the recalibrated smoothed score, not the
earlier sharp-gap reference with \(Q_\epsilon(1/2)\), nor the
original fixed-payer score. It incorporates the safe negative
weights as well as the positive receivers on the same row.
Actual macro ranks at least three cannot be priced by transferring
these bounds across cohorts; the actual prime-pair conjecture
remains open.

For a separate exact arithmetic check of the parity kernels and the
whole one-macro identity, see [check.py](check.py). Its inputs are
synthetic logarithms, not assumptions on occurrence on the prime leg;
the actual fixed-target count is provided above.
