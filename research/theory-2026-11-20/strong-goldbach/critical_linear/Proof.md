# A moving square-root linear sieve against actual primes

Let \(P\) run through large even integers, \(I=[P/3,2P/3]\), \(X=P/3\),
\(L=\log P\), \(r=P-n\), and \(\langle U,W\rangle=\sum_{n\in I} U(n)W(r)\).
Write \(S(P)=2\prod_{p>2}(1-(p-1)^{-2})\prod_{p\mid P,\ p>2}(p-1)/(p-2)\).
For \(n\in I\) put
\[
 A(n)=\sum_{d\mid n}\mu(d)(\log n-2\log d)_+,\qquad
 V(n)=1_{n\ {\rm prime}}\log n,\qquad O(n)=A(n)-V(n).
\]
Thus \(A(n)=2\Lambda_{\sqrt n}(n)\) in the usual truncated von Mangoldt notation.
All bounds below concern the **specified target**, not a target average.

**Theorem.** (i) At the literal moving square root, with no smoothing of the kink,
\[
 \langle A,V\rangle=(2+o(1))XS(P),\qquad
 \langle A,A\rangle=(4+o(1))XS(P).
 \tag{1}
\]
In particular \(\langle O,O\rangle=\langle V,V\rangle+o(XS(P))\ge-o(XS(P))\).
The left side is signed. On squarefree inputs \(O\) vanishes in odd rank:
the sum over paired complementary divisors of the full linear weight equals
\(2\Lambda(n)\), and the matching odd parity identifies half of it with \(A(n)\).
This assertion does not reassign nonsquarefree inputs.

(ii) Fix \(\eta>0\) and a smooth nonnegative even plateau function \(\chi\), supported in
\([-1,1]\), equal to 1 on a neighborhood of 0, nonincreasing on the positive side.
Let \(z_d(n)=1/2-\log_n d,\ \Delta=(\log L)^2/L\).
For **every** \(|T(r)|\le L1_{P^-(r)>P^\eta}\),
\[
 \sum_{n\in I}|T(r)|
 \left|(\log n)\sum_{d\mid n}\mu(d)(z_d(n))_+\chi(z_d(n)/\Delta)\right|
 \ll_{\eta,\chi} XS(P)L^{-.005}.                                    \tag{2}
\]
Cancellation inside the divisor sum, not inside \(T\), is essential.
The same transfer in (1) gives \(\langle A,H\rangle=(2t+o(1))XS(P)\)
for the following prescribed rough finite-rank sources: a prime or fixed product
of distinct primes \(>P^\eta\), summed over ordered labels with fixed polynomial
windows, with weights given by a bounded polynomial in the normalized prime
logarithms and a single factor \(\log r\). Finite linear combinations are allowed;
\(t=\lim X^{-1}\sum_{r\in I}H(r)\) denotes the ordinary intensity.
Endpoints of windows in this formulation use \(\log p_i/L\); the weights may
use \(\log p_i/\log r\). Examples include true balanced triprimes.
There is no inference of strict positivity of \(\langle V,V\rangle\).

## 1. Low rank and the terminal remainder

Throughout (2) target-nonunit rows can first be removed at \(P^{1-\eta+o(1)}+P^{o(1)}\)
cost: a prime shared by \(P,n\) must divide the rough \(r\), hence exceeds \(P^\eta\);
there are \(O_\eta(1)\) such target primes. Divisor multiplicities are \(P^{o(1)}\).
No removal of small prime squares of \(n\) is needed. Let \(K=1.6\log L\).

On \(\omega(n)\le K\), with \(\omega\) counting distinct primes, open the positive
absolute divisor majorant and insert \(b^{\omega(n)-K}\) with \(b=.8\).
Each opened coefficient has size \(O((\log L)^2)\). The divisors lie in
\(\sqrt P\exp(-O((\log L)^2))\ll d\le\sqrt{2P/3}\), on \(O((\log L)^2)\)
dyads. In \(n=dm\) one has the exact factorization
\(b^{\omega(n)}=b^{\omega(d)}\prod_{p\mid m,\ p\nmid d}b\), squares included.
For \((d,P)=1\) apply corrected [Henriot, Theorem 5](https://doi.org/10.1017/S0305004114000280)
on \(m,P-dm\), over the central interval of length \(X/d=P^{1/2+o(1)}\),
with these multiplicative weights on the first form and the rough indicator on the second.
The coefficient height \(O(P)\) is a fixed power of the interval length, as required;
the sieve prime cutoff in the root prefactor is a fixed positive power of the length.
The largest-prime range between that power and \(P\) costs \(O(1)\) in the
bounded reciprocal prime sums. The resulting bound before \(b^{\omega(d)}\) is
\[
 \ll_\eta \frac{XS(P)}{dL^2}\frac d{\phi(d)} L^b(\log L)^C.           \tag{3}
\]
Indeed the number of roots of the product is two off \(Pd\), and one at its primes
(\(2\mid P,\ d\) is odd). This gives the indicated root-count prefactor:
at \(p\mid d\) the extra ratio \((p-1)/(p-2)\) differs from \(p/(p-1)\) by a
product bounded absolutely. In the raw nonnegative local sum the first single-form
weight is \(b\) for \(p\nmid d\), at most 1 otherwise; the second is zero up to
\(P^\eta\), giving \(O_\eta(1)\) in the reciprocal sum. Their simultaneous positive
valuations are possible only at \(p\mid P\); there their contribution to order \(1/p\)
vanishes unless \(p>P^\eta\). For these remaining primes sum the geometric tails
using \(p^{-\max(i,j)}\). Single-form higher prime powers contribute \(O(p^{-2})\)
summably. In particular the extra cost from marking the *distinct* primes of \(dm\)
instead of marking \(d,m\) independently is at most
\(\exp(O(\sum_{p\mid d}1/p))\ll(\log L)^C\), uniformly for moving \(d\):
split at \(p=L^2\) and use Mertens below and \(\omega(d)\le L/\log 2\) above.
These estimates are also valid after deleting exceptional small primes from the
prefactor with the usual fixed constants in the raw local-sum form of the theorem.

On a dyad \(d\asymp D=P^{1/2+o(1)}\) the one-linear-form case gives
\(\sum b^{\omega(d)}/d\ll_b L^{b-1}\); bound \(d/\phi(d)\ll(\log L)^C\).
Together with \(|T|\le L\) and the number and sizes of the opened boxes, (3) costs
\(XS(P)(\log L)^C L^{2b-2-1.6\log b}\), with exponent less than \(-.042\).
This bounds the entire low-rank part of (2).

On \(\omega(n)>K\) the analogous two-form estimate, now on \(n,P-n\)
with \(B^{\omega(n)}\) and the rough indicator and \(B=1.6\), gives
\[
 \sum_{\omega(n)>K}|T(r)|
 \ll_\eta XS(P)(\log L)^C L^{B-1-1.6\log B}
 \ll XS(P)(\log L)^C L^{-.152}.                                     \tag{4}
\]
There is no \(d\) here. The prefactor is \(S(P)/L^2\), the single-form
Euler factor costs \(O_\eta(L^B)\), and the extra \(L\) is the weight of \(T\).

Write \(\delta_j=2^{-j}\Delta\), stopping at the first \(\delta_J\le L^{-1.005}\).
Telescope \(\chi(z/\Delta)\) as the sum of differences of consecutive cutoffs
and the final \(\chi(z/\delta_J)\). The differences times \(z_+\) are fixed
smooth compact annulus shapes rescaled as \(\delta\psi(z/\delta)\) because the
two cutoffs agree at the cusp. There are \(O(\log L)\) blocks, a log-log rather than a log-power loss in \(P\).
For the final raw piece \(d\asymp\sqrt P,\ n=dm\) and
\(|m-d|\ll\delta_J L\sqrt P\); every coefficient costs \(O(\delta_J L)\).
A dimension-one upper sieve on \(P-dm\), \((d,P)=1\), in this containing
interval of length \(Y\asymp\delta_J L\sqrt P\gg P^{.49}\) counts at most
\(O_\eta(Yd/(\phi(d)L))\) rough values. Sift, for instance, to
\(P^{\min(\eta/2,.005)}\) with integer level \(Y^{1/3}\); the squarefree
residue-count errors \(O(1)\) are negligible. Using
\(\sum_{d\asymp\sqrt P}d/\phi(d)\ll\sqrt P\) and \(|T|\le L\), the total
is \(O_\eta(P(\delta_JL)^2)\ll P L^{-.01}\).

## 2. Actual signed square on an annulus

For each of the smooth annuli just defined denote the inner weighted divisor sum by
\(D_\delta(n)\). We claim the uniform estimate
\[
                \sum_{n\in I}|T(r)|\,|D_\delta(n)|^2
                         \ll_{\eta,\chi} XS(P)(\log L)^C.              \tag{5}
\]
The proof needs a *frequency-uniform upper bound*, not the small-frequency
asymptotic for a fixed smooth profile. Here are the two stages.

Choose a smooth compact \(\rho\) on the real line with \(\rho(0)=1\) and
positive-side support in \([0,\sigma]\), \(0<\sigma<\min(\eta/2,.0005)\).
Majorize \(|T|\) by
\(L(\sum_{c\mid r,(c,P)=1}\mu(c)\rho(\log c/L))^2\). This is exactly
\(L\) on rough \(r\). Freeze \(a=\log n/L\) at an arbitrary central
point of each segment \(J\) of a partition of \(I\) into \(O(L^B)\)
intervals of length \(O(P/L^B)\). Let
\(F(v)=a\delta\psi((1/2-v/a)/\delta)\); \(L\sum_{d\mid n}\mu(d)F(\log d/L)\)
is the frozen first factor. The supremum and total variation of \(F\)
are bounded uniformly, and \(\partial_a F=O(1)\) on its support,
uniformly in these \(\delta\). The per-row freezing loss in \(D_\delta\) is
\(O(L^{-B}\tau(n))\). Fixed divisor moments and Cauchy give \(O_A(PL^{-A})\)
in the energy on choosing \(B\) sufficiently large for \(A\). For example
absolute moments of any fixed product of powers of \(\tau(n),\tau(P-n)\)
cost at most a fixed power of \(L\).

Expand the two frozen squares with \(d,e\) from the annulus and
\(c,c'\) from the sieve. Put \(g=(d,e)\), \(q=[c,c']\). The latter is
squarefree, \(q\le P^{.001}\), \((q,P)=1\); its total coefficient is
\(\ll3^{\omega(q)}\). For \((q,[d,e])=1\) replace the physical count on
\(J\) by \(|J|/([d,e]q)\); otherwise both count and density vanish.
The summed error after the outer \(L^3\) is \(O_A(PL^{-A})\). We give the
argument to clarify every progression length. Both large divisor variables
are \(P^{1/2+o(1)}\). For \(g>P^{.05}\) the \(O(1)\) floor errors cost
\(P^{1-.05+.001+o(1)}\), even after all pairs \(c,c'\) and segments.
For \(g\le P^{.05}\) the physical and model sums are separately negligible.
Let \(d=gu,e=gv,\ (u,v)=1\). Physical rows have \(n=gmuv\), with
\(m\le P^{.05+o(1)},\ u,v\ge P^{.44}\); dyadize lengths \(U,V_0\).
Write the arithmetic coefficient as \(\mu(g)^2\mu(u)\mu(v)\)
with \((u,gv)=1,(v,g)=1\). If \((gmv,q)>1\) no rows occur; otherwise
\(u\equiv P\overline{gmv}\pmod q\). For fixed other labels the interval
of \(u\) is intersected with \(gmuv\in J\); \(F(\log(gu)/L)\) has
bounded variation and supremum independently of \(\delta,J\).
Expand \(1_{(u,gv)=1}=\sum_{b\mid(u,gv)}\mu(b)\). When \(b>L^{C_0}\),
\(b^2\mid n\). All such rows have size \(O(P/L^{C_0}+\sqrt P)\);
every multiplicity is bounded by fixed divisor powers of \(n,r\).
Cauchy handles them with arbitrary log savings for sufficiently large \(C_0\).
For smaller \(b\) let \(u=bu'\); if \((b,q)>1\) the unit progression is
empty. Otherwise \((u',b)=1\) splits into at most \(b\) unit classes mod
\(qb\); the remaining signed variable has coefficient \(\mu(u')\).

Use the ordinary maximal-prefix Bombieri–Vinogradov bound for Möbius at
**length \(U/b\ge P^{.43}\)** and moduli \(qb\le P^{.002}\), far inside
the square-root log rail. See the classical maximal version (3.1) stated in [Lü–Wang–Wu, §3](https://arxiv.org/html/2610.20242v2#S3) (only their quoted Möbius BV input is used)
or the Möbius BV input spelled out in [the fixed-shape proof, §2](../linear_midpoint/Proof.md).
To pass from centered to raw sums the coprime Möbius mean is negligible uniformly:
\(\mu1_{(\cdot,s)=1}=\mu*1_{\{k\mid s^\infty\}}\); classical PNT and
\(\sum_{k\mid s^\infty}k^{-1+1/\log L}\ll(\log L)^C\) for \(s\le P^3\)
give \(O_A(Y L^{-A})\) at \(Y\ge P^{.2}\) (very short prefixes are
trivial on the \(U/b\) scale). The moment follows by splitting primes at
\(L^2\). Absorb \(3^{\omega(q)}\) by Cauchy between the arbitrary
BV saving and the trivial \(O(U/(b^2q)+1)\) per progression, using
\(\sum_{q\le P}9^{\omega(q)}/q\ll L^9\).
Pay all log-power \(b,J\) multiplicities by increasing the saving.
After summing \(v\) trivially, \(UV_0\ll P/(gm)\) on a nonempty
physical dyad; the remaining harmonic \(g,m\) sums and the dyads cost
only powers of \(L\). In the model, no \(m\) or residue occurs and the
\(u\)-sum has coefficient \(\mu(u)/u\), the same bounded-variation
annulus factor and the coprime mask \((u,gvq)=1\); apply the uniform
coprime PNT immediately. The other harmonic sums over \(g,v,q\)
have at most log-power cost. This proves the replacement, without an
estimate for primes in a progression anywhere in this stage.

## 3. The high-frequency pole is integrable at the required scale

In the model for each \(J\) Mellin-invert the two \(F\)'s and two \(\rho\)'s
using \(f(x)=\int \widehat f(t)\exp(-(1+it)x)\,dt\), the transform here
being that of \(e^x f(x)\) with the corresponding Fourier convention.
Put \(s_t=(1+it)/L\) and
\[
 Z(t,u)=\frac{\zeta(1+s_t+s_u)}
                   {\zeta(1+s_t)\zeta(1+s_u)} .
\]
The model Euler product factors as \(Z(t_1,t_2)Z(t_3,t_4)K_P(\mathbf t)\),
where \(|K_P|\ll(\log L)^C\) at **all** real frequencies. Indeed its local
factor before stripping the zetas is \(1+(A_p+B_p)/p\) for \(p\nmid P\),
and \(1+A_p/p\) for \(p\mid P\), with
\(A_p=-p^{-s_1}-p^{-s_2}+p^{-s_1-s_2}\), similarly \(B_p\) on indices
3,4 (here \(s_i=s_{t_i}\)). Since \(|p^{-s_i}|\le1\), the residual local
factor off \(P\) is \(1+O(p^{-2})\) uniformly and at primes of \(P\)
is \(1+O(1/p)\), with the finitely many small factors bounded. Mertens
up to \(L^2\) and the tail over divisors of \(P\) give the claim. The
absolutely majorized unstripped Dirichlet series itself is \(O(L^C)\)
at these real parts by multiplying \(1+O(p^{-1-1/L})\).
For \(|t|,|u|\le L^2\) we have
\[
 |Z(t,u)|\ll(\log L)^C\frac{(1+|t|)(1+|u|)}{L^2}
                 \left(1+\frac L{1+|t+u|}\right).                    \tag{6}
\]
Specifically, in a fixed small disk at 1 use the simple Laurent pole,
including the reciprocal's simple zero. For imaginary parts between
a fixed positive constant and \(2L+2\) and real parts \(1+1/L,1+2/L\),
the classical zeta bounds on \(\Re s\ge1\) are
\(|\zeta(s)|,|1/\zeta(s)|\ll\log^{C}(2+|\Im s|)\), with the compact
subrange away from 1 supplied by nonvanishing there. These are the
classical de la Vallée Poussin zero-free-region estimates (the usual
bounds \(\zeta(1+it),1/\zeta(1+it)\ll\log^C(2+|t|)\) extend to this
right strip). Thus the inverse factors are
\(\ll(\log L)^C\min(1,(1+|t|)/L)\); the summed imaginary part in the
numerator retains the actual possible pole. This includes, without
pole expansion at frequencies tending to infinity, the transition
\(1\lesssim |t|/L\lesssim L^{.02}\) and all the way to \(L\).

Every fixed \(k\) gives \(|\widehat F(t)|\ll_k\delta^2(1+\delta|t|)^{-k}\),
uniformly in the frozen \(a\); \(\widehat\rho\) is rapidly decreasing.
If any frequency exceeds \(L^2\), the preceding absolute Dirichlet
bound and \(\delta L^2\gg L^{.995}\) make the integral \(O_A(L^{-A})\).
Inside the box the integral of the last two test transforms against
\(|Z(t_3,t_4)|\) costs \(O((\log L)^C/L)\) by (6).
For the two sharp annulus transforms let
\(f_\delta(t)=\delta^2(1+|t|)(1+\delta|t|)^{-k}\), \(k\ge5\).
Its \(L^1\) norm is \(O(1)\) and its supremum \(O(\delta)\). Hence
\[
 \iint\frac{f_\delta(t)f_\delta(u)}{1+|t+u|}\,dt\,du
                 \ll \delta\log(2+1/\delta).
\]
Use the sup bound on their convolution for \(|t+u|\le1/\delta\),
its \(L^1\) bound on the rest. Accordingly the first pair costs
\((\log L)^C(L^{-2}+L^{-1}\delta\log(2+1/\delta))\).
Multiplying by \(L^3|J|\) and summing the lengths of \(J\) gives (5):
\(L\delta\le(\log L)^2\), and \(S(P)\gg1\).
Cauchy applied to (4),(5) on the high ranks costs at most
\(XS(P)(\log L)^C L^{-.076}\) per block. Together with §1, summing all
blocks proves (2), e.g. with the stated exponent .005.

## 4. Transfer to the actual prime or a prescribed rough convolution

Give the weight \(w_d(n)=(\log n-2\log d)_+\) a multiplier
\(1-\chi(z_d(n)/\Delta)\). Equation (2) prices the full *physical* change
in pairing with the indicated sources at \(O(XS(P)L^{-.005})\), since
their true weights are bounded by \(O(L)\) on fixed roughness. For nonzero
modified weights \(d\le\sqrt{2P/3}\exp(-c(\log L)^2)\), well inside every
\(\sqrt P/L^D\) with fixed \(D\). At each fixed \(d\) the surviving
nonnegative weight is nondecreasing as a function of \(n\), has supremum
and total variation \(O(L)\) and is reflected as \(n=P-r\). No
prime-distribution assertion at a length depending on the divisor \(d\)
is required: for ordinary BV the **length parameter is \(P\)**, the entire
reflected prime or prime-product variable \(r\), with maximal prefix over
its subinterval endpoints. For the finite products use the ordinary
maximal-prefix convolution theorem of [Motohashi, Theorems 1–2](https://doi.org/10.3792/pja/1195518296)
on the product at this length, not on its individual shorter prime labels;
compare the distinct-prime version in [Thm. 3.2](https://doi.org/10.1007/s40993-017-0089-3).
On ordered products each window and prime logarithm is a single-variable
factor satisfying the requisite Siegel–Walfisz and BV hypotheses by
partial summation and ordinary prime BV. For an individual truncated input at a
scale below its window the sequence is zero, and at or above the window
endpoint the cutoff is a prefix difference, so these assertions are uniform
up to the length parameter with at most log-power losses. The central
denominator \((\log r)^k\) from a given monomial (and any numerator \(\log r\))
is incorporated by one partial summation. Repeated rough prime labels cost
\(P^{1-\eta+o(1)}+P^{1/2+o(1)}\) physically by square counting and in
the expected sum after an additional log-power loss. Nonunit target rows
are negligible as in §1. Restrict to \((d,P)=1\), then restore all rough
\(r\) for the comparison. Thus ordinary BV and partial summation replace
\(1_{r\equiv P\bmod d}\) by \(1_{(r,d)=1}/\phi(d)\), with summed
\(O_A(PL^{-A})\) error at these moduli, for any fixed \(A\).
Constants may depend on the fixed source/windows.

Restore the full \(w_d(n)\) in this **signed reference**, at \(o(1)\)
per source point. For \(s=Pr\le P^2\), the Dirichlet series of
\(1_{(d,s)=1}\mu(d)/\phi(d)\), with extra variable \(d^{-z}\), is
\(K_s(z)/\zeta(1+z)\), where
\[
 (K_s)_p(z)=\frac{1-1_{p\nmid s}\,p^{-z}/(p-1)}{1-p^{-1-z}},
 \qquad K_s(0)=S(s).
\]
The coefficients \(k_s(h)\) obey \(\sum_h |k_s(h)|h^{1/\log L}\ll
(\log L)^C\) by the same prime split: off \(s\) the local correction
starts at \(O(p^{-2+1/\log L})\), and the total on primes of \(s\)
is bounded by the indicated product. Thus \(h>P^{1/8}\) costs arbitrary
log savings even against crude \(O(L^2)\) inner sums.
For \(h\le P^{1/8}\) the removed \(d=hm\) are supported at
\(m=P^{1/2+o(1)}/h\ge P^{.36}\), with weight of bounded log-power
supremum and variation in \(m\) (the cutoff is smooth at fixed \(n\)
on this positive half). Partial summation of \(\mu(m)/m\) gives arbitrary
log savings there. In the full weight the same convolution evaluates to
\[
 \sum_{m\le Z}\frac{2\mu(m)}m\log(Z/m)=2+O_A(L^{-A}),
 \quad Z=\sqrt n/h\gg P^{.36},
\]
by the PNT and the simple zero of \(1/\zeta(1+z)\) with derivative 1.
Hence the reference per source point is \(2S(Pr)+o(1)\) uniformly.
For the given sources \(S(Pr)/S(P)=1+O_{\eta,k}(P^{-\eta})\).
Their physical unshifted total is \((t+o(1))X\), with \(t=1\) for
true primes, by the PNT. On fixed rough prime windows the elementary
product PNT/successive reciprocal prime sums yield this limit, see
[polynomial halves, §1](../midpoint_halves/Proof.md); boundedness
and negligible boundary slices follow on the fixed compact simplex.
The error terms are also valid against the absolute source majorant,
whose total is \(O_{\eta,k}(X)\).
This proves the mixed assertion of (1).

## 5. The self-correlation at the unsmoothed double endpoint

We need a signed physical-to-CRT comparison for
\(\sum_{d,e}\mu(d)\mu(e)w_d(n)w_e(P-n)1_{d\mid n,e\mid P-n}\).
The crude floor bound over *both* square-root variables costs \(O(P)\),
which is insufficient in degree one.

Use a partition into \(O(L^B)\) half-open intervals \(J\) of lengths
\(O(P/L^B)\); the possible original integer endpoints cost \(P^{o(1)}\).
Freeze each weight at a representative \(n_J\) or \(P-n_J\).
Its Lipschitz constant on the interval is \(O(1/P)\) since the positive
part function is 1-Lipschitz. The summed physical error is
\(O(PL^{1-B}\cdot L^3)\) by Cauchy and the usual second divisor moment.
For the density comparison the analogous error is \(O(PL^{1-B}L^3)\)
as \(\sum_{d,e\le\sqrt P}1/[d,e]\ll L^3\) by writing their gcd.
Take \(B\) as large as needed. At compatible pairs let \(g=(d,e)\mid P\);
the desired frozen model is \(|J|/[d,e]\). Incompatible pairs vanish.
If \(\min(d,e)<\sqrt P/L^D\), the \(O(1)\) floor discrepancies are
\(O(PL^{B+2-D})\), choosing \(D\) after \(B\). For the rest,
\(g>L^C\) costs \(O(PL^{B+2-C})\) by summing \((\sqrt P/g)^2\).
It remains to treat \(d=gu,e=gv,\ (u,v)=1,\ g\mid P,\ g\le L^C\);
all ordered \(u,v\) lie on dyads of sizes \(P^{1/2}\) times log powers
above or below. The filters \(\mu(gu)\), \(\mu(gv)\) and frozen weights
separate. In \(n=gu m\) we have
\[
                  m\equiv (P/g)\bar u\pmod v .
\]
For each endpoint \(y\) of \(J\) the sawtooth argument in the floor is
\[
             \xi_{uv}(y)=y/(guv)-(P/g)\bar u/v .
\]
(The choice of a consistent half-open interval or a half-integer endpoint
changes only the conventional value at exact integers.)

Split \(\mu(gu)\) and \(\mu(gv)\) by sign to make four separate
nonnegative product weights bounded by \(O(L^2)\). The sum of any
centered floor sawtooth on the arguments \(\xi_{uv}(y)\) is, by the
weighted Erdős–Turán inequality and integration of interval indicators,
\[
 \ll \mathcal W/H+
 \sum_{1\le h\le H}\frac1h
    \left|\sum_{(u,v)=1}\alpha_u\beta_v e(h\xi_{uv}(y))\right|,
 \qquad e(t)=\exp(2\pi it),                                         \tag{7}
\]
where \(\mathcal W=\sum_{(u,v)=1}\alpha_u\beta_v\), and \(H=L^E\)
with fixed \(E\) chosen after \(B,C,D\). Weighted discrepancies also
bound the possible mass at a single endpoint by passage to one-sided
limits. The constant \(1/2\) cancels between the two endpoints.
The trivial diagonal budget \(\mathcal W/H\) summed over meshes, \(g\)
and dyads is \(O(PL^{-A})\) by taking \(E\) large enough.

For each \(h\) in (7) separate the smooth factor \(e(hy/(guv))\).
Indeed on dyads \(u\asymp U,\ v\asymp V_0\) put
\(t=(U/u)(V_0/v)\in[1/4,1]\). Multiply \(e(hyt/(gUV_0))\)
by a fixed smooth compact bump equal to 1 on that range and Mellin
invert. Its transform has \(L^1\) norm \(O((1+|hy|/(gUV_0))^2)\)
by two integrations by parts, which is a fixed log power here.
The separated pure imaginary powers do not change the coefficient norms.
Apply [Bettin–Chandee, Theorem 1](https://arxiv.org/abs/1502.00769)
to the remaining form with singleton third variable equal to 1 and
nonzero integral \(\theta=-hP/g\). In detail its upper bound, up
to \(P^\epsilon\) and log powers, is
\[
 (UV_0)^{1/2}(1+|\theta|/(UV_0))^{1/2}
 \{(UV_0)^{7/20}(U+V_0)^{1/4}
       +(UV_0)^{3/8}(U+V_0)^{1/8}\}.
\]
Here \(UV_0=P L^{O(1)}\), \(|\theta|/(UV_0)\le L^{O(1)}\),
\(U+V_0=P^{1/2}L^{O(1)}\). The two exponents of \(P\) are
\(39/40,\ 15/16\) respectively, both strictly below one.
This power saving pays every fixed log loss above, for all \(h,J,g\)
and dyads summed. The sign parts in this argument are a device for (7);
there is no replacement of a signed arithmetic main by its absolute value.
This proves physical-to-CRT comparison at the genuine double endpoint
with arbitrary-log savings (taking the mesh powers in order).

It remains to evaluate the CRT reference with the unfrozen weights
as justified above. The Dirichlet series of \(1_{(d,e)\mid P}\mu(d)\mu(e)/[d,e]\)
with extra powers \(d^{-s}e^{-t}\) equals
\(K_P(s,t)/(\zeta(1+s)\zeta(1+t))\), \(K_P(0,0)=S(P)\).
Its local residual quotient is
\(1+(1_{p\mid P}p-1)uv/((1-u)(1-v))\), \(u=p^{-1-s},v=p^{-1-t}\).
Its double coefficients \(c_{i,j}\) satisfy
\(\sum|c_{i,j}|(ij)^{1/\log L}\ll(\log L)^C\) by the prime split above.
Thus high \(i\) or \(j>P^{1/8}\) is negligible, and for both small
indices the one-variable harmonic PNT evaluation in §4 gives \(2\)
plus arbitrary log savings on each side. Integrating over \(I\) gives
\(4XS(P)+o(X)\), proving (1). Subtract the two mixed terms to get the
stated identity for \(O\). Its right side is nonnegative but may a priori
be zero. No lower bound for the prime-prime count is obtained.

## Relation to earlier work

The prime mixed correlation of a truncated divisor-sum approximation is a
classical construction; see [Goldston–Yıldırım I](https://arxiv.org/abs/math/0111212)
and [III](https://arxiv.org/abs/math/0209102). Ordinary prime BV already evaluates
our mixed statistic with a fixed log-power gap in the divisor cutoff. Smooth
divisor-square Euler products are standard (e.g. [D. H. J. Polymath, Lemma 4.1](https://arxiv.org/html/1407.4897v3#S4)).
The additional point here is (2), the absolute estimate **after summing the signed
divisors inside each individual row** for the actual shrinking first-order kink
against arbitrary polynomially rough reflected weights, and the audit of the
unshortened moving double endpoint at a macroscopic prescribed target. The earlier
[fixed-width first-order result](../linear_midpoint/Proof.md) takes the target limit
before the width limit and cannot be substituted for (2).
The inverse-fraction range in §5 is within the published Bettin–Chandee bound;
no withdrawn Kloosterman estimate is required. No novelty of that bound, of
Bombieri–Vinogradov, or of the short-divisor approximation to primes is claimed.

For recent comparison, [Pham October 2026 v1, Appendix D](https://www.preprints.org/manuscript/202610.3061)
treats a rough-pair benchmark in a different reflected-row construction; [Arneth October 2026 v1](https://zenodo.org/records/23477014)
uses a cubic minorant with roughness restrictions; and the [Bahbouhi November 2026 v1 identities](https://www.preprints.org/manuscript/202611.0975)
separate rough prime and semiprime survivors. These are distinct from the
absolute deletion of the linear shoulder and do not enter the proof.
