# A factored-reciprocal cancellation band for the shared-index rough Möbius score

This note considers one signed component of the balanced fixed-target
covariance, not an estimate for the whole covariance. The underlying
common-index geometry is [Pham, Appendix D](https://www.preprints.org/manuscript/202610.3061).
Our estimate uses the classical \(q\)-van der Corput shift
(see, e.g., [Irving's divisor-function application](https://arxiv.org/abs/1403.8031))
and the complete rational-function Weil bound. The new cut below depends
on the two **actual** slope tags through the modulus factorization.

Let \(N=2x\) be even, \(Y=\sqrt x\), \(L=\log x\), \(\ell=\log L\), and
\(z=\exp(L/\ell^2)\). Work with \(k\in I=[Y,1.1Y]\) and
\(e\in E=[.65Y,.8Y]\), both coprime to \(N\). An actual tag tuple of \(e\) is
a pair of primes \(p_2p_3\mid e\) with
\[
 p_2\in[x^{.029},x^{.031}],\qquad p_3\in[x^{.075},x^{.078}].
\]
Write \(\beta(e)\) for its number of tag tuples. For \(y\in[x,3x/2]\) set
\[
 W_-(s)=x^{.674}s^{-1/4},\qquad
 W_+(s)=\min\!\bigl\{x^{.766}s^{-1/2},\,x^{.918}/s\bigr\},\qquad
 \mu_2=\mu*\mu ,
\]
and define the actual component
\[
 B(y)=-1_{P^-(y)>z}
 \sum_{\substack{s\mid y\\x^{.13}\le s\le x^{.32}}}\log s
   \sum_{\substack{a\mid y/s\\ W_-(s)<a\le W_+(s)}}
             \mu_2\!\left(\frac{y}{sa}\right).
 \tag{1}
\]
The variable \(a\) is an unrestricted integer divisor subject to the
displayed conditions, not a prime. The comparison of the two cutoffs
is strict throughout the \(s\)-range. The cap \(a s\le x^{.918}\)
makes this band disjoint from the separate double-free-variable
removal of \(a s>x^{.918}\). The other cap places it below the
original one-free cutoff \(a>x^{.766}s^{-1/2}\).

**Theorem.** For each fixed \(A\),
\[
 \sum_{\substack{k\in I\\(k,N)=1}}
 \left|\sum_{\substack{e\in E\\(e,N)=1}}\beta(e)B(N-ek)\right|
 \ll_A xL^{-A}.                                                    \tag{2}
\]
Consequently pairing this component with any opposite actual row of
uniform magnitude \(O(YL^C)\) costs \(O_A(x^{3/2}L^{-A})\), for each fixed
\(C\). In particular one may take the opposite row
\(\sum_{d\in E,(d,N)=1}u_{d,k}\) for arbitrary true coefficients
\(|u_{d,k}|\ll L^F\tau(N-dk)^F\) and any additional pointwise
bounded tags or masks, with \(F\) fixed, by Shiu's divisor bound. No claim is made for an arbitrary
multiplier on the individual entries **inside** the \(e\)-row.

This is not a null from averaging the target. In (2), \(N\) is fixed and
the absolute value is outside the actual \(e\)-sum at each \(k\).
The component is supported on genuine composites and does not
touch the prime atom. No sign of the surviving covariance is asserted.

## 1. Exact divisor interpretation

The rough long score of the [above-root branch](../overroot_shared_k/Proof.md) is
\[
 K(y)=1_{P^-(y)>z}\sum_{\substack{s\mid y\\y/s>x^{.505}}}
                       \mu(y/s)\log s .
\]
For the \(s\) in (1), its condition \(y/s>x^{.505}\) holds automatically.
Heath-Brown's finite convolution identity with \(U=x^{.24}\) gives, for \(r\le 3x/2\),
\[
 \mu(r)=\sum_{j=1}^{5}(-1)^{j-1}{5\choose j}
               \bigl(\mu_{\le U}^{*j}*{\bf 1}^{*(j-1)}\bigr)(r).
\]
Indeed, \(\delta-\mu_{\le U}*{\bf1}\) vanishes through \(U\), so its
fifth convolution power vanishes through \(U^5\). This proves the
display by expanding and convolving by \(\mu\). A free variable of
size \(a>W_-(s)\ge x^{.594}\) is unique in each convolution tuple.
All other variables have product
\(c=r/a\ll x^{.326}s^{-3/4}\le 2x^{.2285}<U\) for all sufficiently large
\(x\), so their truncated Möbius factors are unrestricted. The
sum over the \(j-1\) choices of the free slot has signed coefficient
\(\sum_{j=2}^5(-1)^{j-1}{5\choose j}(j-1)=-1\), and the convolution
on \(c\) in every term is \(\mu_2(c)\). This proves (1) as the exact
additional free-slot band lying below the larger cutoff \(W_+\).
The gain in the free-variable exponent is \(.092-\frac14\log s/L\),
until the double-free cap is reached, and is then
\(.244-\frac34\log s/L\); it is at least .004 throughout the stated
range. The deletion concerns the displayed divisor-score component,
not an entire physical rank.

## 2. Incomplete reciprocal correlation

For coprime positive integers \(Q_1,Q_2\) with \(Q_2\) squarefree,
\(Q=Q_1Q_2\), let \(J\) be an interval of length at most \(S\) and assume
\(S\ge 2Q_1\) and \(Q_1\le Q_2^{1/2}\).
Uniformly in the integer \(b\),
\[
 \left|\sum_{\substack{s\in J\\(s,Q)=1}}
             e\!\left(\frac{b\bar s}{Q}\right)\right|
 \ll_\varepsilon x^\varepsilon S^{1/2}Q_2^{1/4}
                    (b,Q_2)^{1/4}                                  \tag{3}
\]
in the polynomial-sized parameter ranges used below, with \(S<Q_2\).
Here \(e(t)=e^{2\pi it}\) and bars denote inverses modulo the
displayed modulus.

To prove (3), extend the summand by zero outside \(J\), shift it by
\(hQ_1\) for \(1\le h\le H_0=\lfloor S/Q_1\rfloor\), and apply Cauchy
to the average. The \(Q_1\)-phase cancels on nonzero correlations.
Its unit mask survives as \(1_{(s,Q_1)=1}\), expanded by divisors of
\(Q_1\). On each such progression, completion modulo \(Q_2\) of the
\(Q_2\)-phase costs \(O(\log x)\), since its step is coprime to \(Q_2\)
and the length is at most \(S<Q_2\). The completed phase at each
prime \(p\mid Q_2\), with the two poles omitted, is
\[
 b\overline{Q_1}\big((s+hQ_1)^{-1}-s^{-1}\big)+j s .
\]
Affine reparametrization for a divisor of \(Q_1\) makes no difference
to the pole orders. If \(p\nmid b h\), a genuine simple pole excludes
the additive Artin–Schreier degeneracy, even after adding the linear
term. Weil's bound is \(O(\sqrt p)\). Otherwise use \(p\).
The squarefree CRT bound is therefore
\[
 \ll_\varepsilon x^\varepsilon Q_2^{1/2}(b,Q_2)^{1/2}(h,Q_2)^{1/2}.
\]
Fixed numbers of divisor powers or constant-per-prime factors cost
\(x^\varepsilon\). Summing over \(h\le H_0\) uses
\(\sum_{h\le H_0}(h,Q_2)^{1/2}\le H_0\sum_{d\mid Q_2}d^{-1/2}\),
with no extra \(+\!1\) for multiples of \(d\). The Cauchy diagonal
is \(O(S^2/H_0)\). This proves (3) after a harmless change of
\(\varepsilon\).

## 3. Counting the literal progression

For fixed labels \(k,p_2,p_3\), put \(Q=k p_2p_3\). The actual progression
is \(y=N\bmod Q\) in \(J_k=[N-.8Yk,N-.65Yk]\). Exactly one physical
\(e\) corresponds to each such \(y\), and \((e,N)=1\) is equivalent to
\((y,N)=1\). We may omit the latter mask on the rough values: any
violating \(y\) is divisible by some \(p>z\) dividing \(N\), so there
are \(O(xL/z+L)\) such integers. Their weighted total in all physical
rows is \(O_A(xL^{-A})\). For this use the multiplicity
\(\ll\tau(N-y)^{O(1)}\), the bound \(|B(y)|\ll L\,\tau(y)^{O(1)}\),
Cauchy, and the ordinary divisor moments on both translates. This
pays the residual mask on the original rough expression, before
approximating it by an expanded sieve.

Discard tag tuples with \(p_2p_3\) not coprime to \(k\), or with the
largest squarefull divisor \(k_{\rm pow}\) of \(k\) exceeding
\(x^\delta\), for small fixed \(\delta>0\). Their absolute contribution
to (2) saves a power. In fact each tuple has \(O(Y/(p_2p_3))\)
possible slopes and pointwise divisor weights \(x^{o(1)}\).
Sums over \(k\) divisible by a selected tag have relative cost
\(O(1/p_2+1/p_3)\). If \(k_{\rm pow}>x^\delta\), then \(d^2\mid k\)
for \(d>x^{\delta/3}\), so there are \(O(Y x^{-\delta/3})\) such \(k\).
The sums of \(1/(p_2p_3)\) over the fixed polynomial tag bands
are bounded, by Mertens. The retained factorization is
\[
 Q_1=k_{\rm pow}p_2p_3,\qquad Q_2=k/k_{\rm pow}.
\]
It satisfies (3): \(\log Q_1/L\le .109+\delta+o(1)<.13\),
\(\log Q_2/L\ge .5-\delta+o(1)\), and \(Q_1\le Q_2^{1/2}\).

On the congruence \((N,Q)=1\), the factors \(s,c,a\) are individually
units of \(Q\). The roughness on \(s,c\) is left exact in their
coefficients. For \(a\) open the roughness indicator by Bonferroni
through \(J_0=\lceil C_A\ell\rceil\) factors, with absolute error
bounded by \({\omega_{\le z}(a)\choose J_0+1}\), each opened term
\(a=mv\), \(m\mid\prod_{p\le z}p\), \(m\le z^{J_0+1}=x^{o(1)}\).
Terms with \((m,Q)>1\) vanish. First on an independent box
\(s\sim S,c\sim C,a\sim W\), with \(SCW\asymp x\), the Poisson
formula in \(v\) has zero-frequency length divided by \(Q\), and
nonzero frequencies with phase
\[
 e\!\left(\frac{Nh\overline{s c m}}{Q}\right),\qquad |h|\ll
 H=x^\varepsilon Qm/W.
\]
For a smooth free-variable cutoff the coefficients after factoring
out \(W/(mQ)\) are bounded. Rejecting all nonzero frequencies is
valid when \(x^{\varepsilon}Qm/W<1\): then arbitrarily many
integrations by parts give a power saving. The same argument, with
slightly smaller initial \(\varepsilon\), bounds the tails of all
frequencies beyond the displayed cutoff. The test factors on \(s,c\)
have size at most \(x^\varepsilon\).

By Cauchy in \(s\), the normalized nonzero-frequency contribution,
relative to \(SCW/(mQ)\), is at most \(x^{O(\varepsilon)}\) times
the square root of
\[
 \frac H C+
 \frac{Q_2^{1/4}}{S^{1/2} C^2}
 \sum_{\substack{0<|h|,|h'|\ll H\\c,c'\sim C\\ h c'\ne h'c}}
              (h c'-h'c,Q_2)^{1/4}.                                \tag{4}
\]
For the first term the exact equality \(h c'=h' c\) has
\(O(HC\log(2C))\) solutions: at fixed \(c,c'\), use their gcd
to parametrize the two nonzero frequencies. For the second,
apply (3) with the indicated determinant times a unit modulo \(Q_2\)
and the numerator \(N\), also a unit. No arithmetic cancellation of
\(\mu_2(c)\) or of the outer \(s\)-weight is used in these nonzero terms.

Average (4) over the physical \(k\) for each pair of prime tags,
using concavity of the square root. For any nonzero determinant
\(D=hc'-h'c\), which is polynomially bounded,
\[
 \sum_{k\in I} (D,Q_2)^{1/4}
 \le \sum_{k\in I}(D,k)^{1/4}
 \ll Y\sum_{j\mid D}j^{-3/4}\ll_\varepsilon Yx^\varepsilon .
\]
Indeed the number of multiples of a divisor \(j\le1.1Y\) up to \(1.1Y\)
is at most \(1.1Y/j\); larger divisors contribute zero.
This average is over shared indices \(k\), not targets.
It allows the same determinant over a slightly enlarged common
box and drops all unit restrictions in the positive average.
With \(Q\) at most a constant times \(Yp_2p_3\) and comparable
to it throughout \(I\), the two resulting relative bounds are
\[
 x^{O(\varepsilon)}(QS/x)^{1/2},\qquad
 x^{O(\varepsilon)}(Q/W)\,Q_2^{1/8}S^{-1/4}.
\]
The factors \(m=x^{o(1)}\) have been absorbed in these margins;
the number of all \(m\)'s is likewise \(x^{o(1)}\).
The first bound saves a power since \(.609+.32<1\).
The second saves a power since
\(.609+.5/8-.674=-.0025\) and \(W\gg x^{.674}S^{-1/4}\).
Choose \(\varepsilon,\delta\) smaller than the fixed margins.
Summing over \(k,p_2,p_3\) costs \(O(x)\) before the relative
saving, from \(\sum_{k,p_2,p_3} x/(kp_2p_3)\ll x\).

For completeness the box argument tolerates all physical cutoffs.
Use a log-fine relative mesh of width \(L^{-D}\) in the independent
\(s,c,a\) coordinates, after dyadic subdivision; a fixed log power
of smooth free-variable functions suffices, with derivatives bounded
by fixed powers of \(L\). For each given \(k\), the boxes where
\(sca\in J_k\) and \(W_-(s)<a\le W_+(s)\) hold throughout are interior.
All unresolved boxes are contained in fixed constant enlargements of
relative \(O(L^{-D})\) strips along these faces and may be upper
bounded with nonnegative coefficient magnitudes. To use (4), enlarge
the \(k\)-set of a given box when taking the positive determinant
average; the maximal scales in the box satisfy the same strict
rails, including in the boundary coverings.
For each fixed \(s,c,k\), the free-variable length of all these
strips is \(O(W L^{-D})\), up to a fixed number of boundary
coverings. Their zero-frequency mass is \(O(xL^{-D+O(1)})\) in total
after all modulus labels, by standard harmonic divisor moments.
This bounds both the original sums on faces and their model
replacements. Smooth partitions in \(a\) can be taken with overlap
bounded by an absolute constant. Arithmetic inclusion or exclusion
at an exact endpoint is included in the same narrow strip. Thus no
short-interval prime estimate or uniform SW hypothesis for rough
coefficients is hidden in the cuts.

The Bonferroni absolute error is treated by the same nonnegative
box estimates at degree \(J_0+1\). Its zero-frequency normalized
mass is bounded by
\((\sum_{p\le z}1/p)^{J_0+1}/(J_0+1)!\), which is smaller than
any prescribed power of \(L^{-1}\) on increasing \(C_A\), by
Mertens and the factorial bound. All physical divisor/log losses
in this step are fixed powers, independent of \(C_A\); nonzero
estimates absorb the \(x^{o(1)}\) of all \(m\le z^{J_0+1}\).
The same tail replaces the truncated zero-frequency Euler
product by \(\prod_{p\le z,p\nmid Q}(1-1/p)\).

## 4. Signed principal

For each modulus, rewrite the zero-frequency integral using
\(y=sca\). Apart from the rough factor on the free variable and
the \(1/Q\) factor, its inner sum at fixed \(s,y\) is exactly
\[
 \sum_{\substack{y/(sW_+(s))\le c<y/(sW_-(s))\\
              (c,Q)=1,\ P^-(c)>z}}\frac{\mu_2(c)}{c}.
 \tag{5}
\]
Both endpoints are polynomial, the lower one at least
\(x^{.074+o(1)}\) and the upper one at most \(2x^{.2285}\).
Uniformly in this range the sharp-prefix sum in (5)
is \(O_A(L^{-A})\). Here is an explicit analytic justification.
Its Dirichlet generating function at Mellin variable \(w\) is
\[
 \zeta(1+w)^{-2}
   \prod_{\substack{p\le z\ \text{or}\ p\mid Q}}
                  (1-p^{-1-w})^{-2}.
\]
At heights \(\le L^C\), shift Perron's contour to
\(\Re w=-c_0/\log z\) for fixed sufficiently small \(c_0>0\).
The classical zeta zero-free region and bounds for \(1/\zeta\)
give polylogarithmic control on the shift; the pole of Perron's
\(1/w\) is canceled by the double zero at \(w=0\).
The finite Euler factors are polylogarithmically bounded uniformly
in \(Q\): at \(p\le z\) this follows by
\(p^{c_0/\log z}\le e^{c_0}\), and omitted \(p\mid Q,\ p>z\)
have total reciprocal cost \(O(L/z^{1-o(1)})\).
Consequently the new vertical segment is bounded by a log power
times \(\exp(-c_1\ell^2)\). The two horizontal segments have the
Perron height denominator; one can choose the shifted-line
\(1/\zeta\) and finite-product log-power bounds independently of
the desired Perron power \(C\) at \(|t|\asymp L^C\).
The sharp-endpoint truncation error is arbitrary-log by choosing
\(C\) large: \(|\mu_2(c)|\le \tau(c)\), and near the endpoint
use Shiu's divisor estimate in intervals of length
\(\gg c/L^{C}\), then dyadically sum the standard Perron
truncation kernel. At an exact endpoint the single harmonic
coefficient is \(c^{-1+o(1)}\), negligible. This proves (5).

Finally sum (5) against \(\log s/s\) on the true rough, unit
\(s\)-range, of total \(O(L^2)\) by the integer harmonic bound,
and integrate \(y\) over \(J_k\) with \(1/Q\). The resulting
model is \(O_A((x/Q)L^{-A})\). Its absolute sum over the physical
moduli is \(O_A(xL^{-A})\), as in Section 3. This proves (2).

For the stated application to the opposing row, each fixed
unit \(k\) has an interval of length \(O(x)\) in the reduced
class \(N\bmod k\). Divisor bounds for \(K(y)\) and Shiu's
upper estimate give \(O(YL^C)\) for its absolute sum there;
\(\beta(d)\) is bounded by a constant on the fixed polynomial
tag bands. This supplies the claimed pointwise opposite-row
envelope. The remaining composite score and its covariance are not controlled here.

## Optional quantitative error

In (2) one may in fact take \(O(x\exp(-c\ell^2\log\ell))\) for some
absolute \(c>0\). Here are choices within the same proof, without
altering either physical cutoff. In the rough opening take
\(J_0=\lfloor\eta\ell^2\rfloor\) with fixed \(\eta>0\) sufficiently
small compared with the smallest power-saving margin in (4).
Then \(m\le x^{\eta+o(1)}\) and the number of all \(m\)'s is at most
this. The fixed \(m\)-loss in (4) and summing its nonzero error
still cost only \(x^{O(\eta)}\); the factorial remainder is
\(\exp(-(\eta+o(1))\ell^2\log\ell)\). Use mesh width
\(\exp(-D\ell^2\log\ell)\) with fixed \(D>0\).
Its number of boxes and free-variable derivative constants are
\(x^{o(1)}\), so the minor terms still save a fixed power, while
the zero-frequency boundary bound keeps this mesh-width saving.

In (5) use shifted real part
\(-(\log\ell)/\log z\) and Perron height \(\exp(D\ell^2\log\ell)\).
The shift remains strictly inside the classical zero-free region
and the usual bound for \(1/\zeta\) there is a fixed power of
\(\log(3+|t|)\), with the removable small-\(t\) case handled at
\(w=0\). Mertens and \(p^{(\log\ell)/\log z}\le\ell\) for
\(p\le z\) give a crude but sufficient bound \(\exp(O(\ell^2))\)
on the finite Euler product; for \(p\mid Q,\ p>z\) use
\(O((\ell L)/z)\). The factor \(C_0^{-\log\ell/\log z}\) for
either polynomial endpoint \(C_0\) in (5) saves
\(\exp(-(.074+o(1))\ell^2\log\ell)\). The horizontal segments
and the sharp-prefix Perron truncation have the height saving
up to the same \(\exp(O(\ell^2))\) and log factors. Shiu still
covers the required endpoint intervals, of length
\(C_0^{1-o(1)}\). This establishes the stated stronger rate.

