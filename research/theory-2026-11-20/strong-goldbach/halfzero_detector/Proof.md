# An actual short Goldbach detector with a uniformly removable half seam

Let \(N\) tend to infinity through even integers, \(L=\log N\),
\(J\Subset(0,1)\) a fixed nondegenerate interval, \(x\in NJ\),
\(y=N-x\), and \(M=|J|N\mathfrak S(N)\). Set
\[
 \langle X,Y\rangle
  =\sum_{\substack{x\in NJ\\(x,N)=1}}X(x)Y(y),
 \qquad
 \Pi(n)=(\log n)1_{\{n\ {\rm prime}\}},\qquad
 R_J=\langle\Pi,\Pi\rangle .
\]
Define a symmetric polynomial and its lower-half restriction:
\[
 P(t)=\tfrac14(1-2t)^2\{7-3(1-2t)^2\},
 \qquad f_*(t)=P(t)1_{\{t<1/2\}}\quad(t\ge0).
\]
This polynomial has \(P(0)=1, P'(0)=-1\) and has
a double zero at \(1/2\). The actual physical detector is
\[
 V_f(n)=(\log n)\sum_{d\mid n}\mu(d)f(\log d/L),
 \qquad H_f(n)=V_f(n)-\Pi(n).
\]
In particular \(H_{f_*}\) is exactly zero on central prime rows.

**Theorem.** Uniformly for all even targets,
\[
                   \langle H_{f_*},H_{f_*}\rangle
                                  =R_J-M+o(M).                 \tag{1}
\]
There are fixed constants \(D>1,\gamma>0,\kappa>0\) so that the
following positive estimates hold. On actual rows with
\(\max(\omega(x),\omega(y))>K\), the absolute weighted sum
\(\sum |H_{f_*}(x)H_{f_*}(y)|\) is \(O_J(D^{-K}M)\); on rows with
a true prime factor \(\le N^\eta\) in either integer it is
\(O_J(\eta^\gamma M)\) for fixed small \(\eta\). The same estimates
hold uniformly for the smooth strictly sub-root approximations
to \(f_*\) defined below. Replacing either score by its corresponding
smooth approximation at width \(\delta\) costs
\(O_J(\delta^\kappa M)\) in the **absolute sum of the difference of
paired weights**, uniformly in \(N\) sufficiently large. There is
no order-one seam contribution of this kind.

Consequently, the actual correlation reduces to pairs of true
squarefree integers at fixed ranks, with arbitrarily small error
at scale \(M\), using their own logarithmic factor angles. In these
coordinates the normalized sharp score is identically zero at
every even rank \(\ge6\). The two remaining even ranks give
\[
 H_2(u)=1-P(u),\quad 0<u\le \tfrac12,\qquad
 H_4(u_1,u_2,u_3,u_4)=-144\prod_i u_i.                         \tag{2}
\]
Here \(H_2\) is positive and \(H_4\) is negative. The true odd
ranks remain. In particular (1) is not a lower bound for Goldbach.
This is a different score, not an approximation to the unit-jump
score in [the short odd receiver](../short_odd_receiver/Proof.md).

## 1. A prime harmonic upper with the correct phase coefficient

Write \(A_\xi(p)=|1-\exp(i\xi\log p/L)|\). For any fixed
\(\epsilon>0\) one has, uniformly in \(N\ge3\) and \(\xi\in\mathbb R\),
\[
 \sum_{p\le N}\frac{A_\xi(p)}p
       \le (4/\pi+\epsilon)\log(2+|\xi|)+O_\epsilon(1).        \tag{3}
\]
We give the frequency ranges since the cruder coefficient \(2\)
would not give the needed uniform weighted Fourier norm.
Put \(T=|\xi|\). For \(T\le1\) the log-weighted prime
harmonic bounds the sum by \(O(1)\). For \(1<T\le\sqrt L\), the
same bound applies to primes up to \(N^{1/T}\).
For the remaining primes use the ordinary prime number theorem
in partial summation, replacing the prime harmonic with
\[
       \int_1^T |1-e^{iu}|\frac{du}{u}
                      =\frac4\pi\log T+O(1).
\]
The bounded primitive of the periodic mean-zero part proves the
last equality. For the replacement, the usual zero-free-region
PNT error is more than enough: if
\(\pi(v)=\operatorname{li}(v)+O(v\exp(-c\sqrt{\log v}))\),
the endpoint and derivative errors from
\(v^{-1}A_\xi(v)\) above a cutoff \(V\) are
\[
 \ll \bigl(1+T/L\bigr)
       \left(e^{-c\sqrt{\log V}}+
                     \int_{\log V}^\infty e^{-c\sqrt z}\,dz\right).
\]
This is bounded in the frequency ranges where it is used. Use the Lipschitz derivative bound
\((2+T/L)/v^2\), valid almost everywhere.

For \(\sqrt L<T\le L^2\), discard primes below
\(V=\exp((\log L)^4)\) at the positive cost
\(O(1+\log\log L)\). The same PNT replacement above \(V\)
has bounded error, and its nonnegative integral is at most
\((4/\pi)\log T+O(1)\): below the phase argument 1,
\(|1-e^{iu}|\le u\). The discarded cost is absorbed into
\(\epsilon\log(2+T)+O_\epsilon(1)\). For \(T>L^2\) the crude
upper \(2\sum_{p\le N}1/p\le 2\log L+O(1)\) suffices.
Fixed small \(N\) are absorbed into the constants. This proves
(3) for all frequencies, without a frequency-dependent assumption
on the target's prime factors.

For \(0<\eta\le1/4\) and any fixed \(0<\gamma<1\), we also have
\[
 \sum_{p\le N^\eta}\frac{A_\xi(p)}p
                  \ll_\gamma (\eta T)^\gamma .              \tag{4}
\]
For \(\eta T\le1\) apply \(A_\xi(p)\le T\log p/L\) and the
weighted prime harmonic. Otherwise split at \(N^{1/T}\).
The small-prime contribution is \(O(1)\), and by Mertens the
remaining sum is \(O(1+\log(\eta T))\). If the splitting point
is below 2, the full reciprocal sum has this upper because
\(T>L/\log 2\). The remaining cases use
\(1+\log s\ll_\gamma s^\gamma\) for \(s\ge1\).

## 2. Absolute arithmetic envelopes, uniformly in the width

Extend \(f_*\) and the approximations below to compactly supported
real functions by a common smooth left cut identically one near
\([0,1/2]\). Fourier inversion gives
\[
  |V_f(n)|\le L\int_{\mathbb R}|\widehat f(\xi)|W_\xi(n)\,d\xi,
       \qquad W_\xi(n)=\prod_{p\mid n} A_\xi(p),               \tag{5}
\]
using one fixed transform normalization throughout. The product
depends on distinct genuine primes; (5) is valid with prime
powers and for any of the stated profiles.

Apply the actual two-linear-form envelope of
[the wide finite-angle lemma, §2](../nearfull_high_vaughan/WideJointGiantFiniteAngles.md)
with \(A_\xi(p)\) in place of \(A_\xi(p)+\log p/L\).
In more detail, use
[Henriot's corrected Theorem 5](https://doi.org/10.1017/S0305004114000280)
on \(x,N-x\), with value \(D A_\xi(p)\) on every positive
power of \(p\) on the first arm and similarly on the second,
and zero at positive powers of target primes. These functions
have uniform growth parameters since \(A_\xi(p)\le2\).
At \(p\nmid N\), the two affine roots are distinct. The corrected
valuation model, after extension to the independent Euler product,
has factor \(1+D(A_\xi(p)+A_\zeta(p))/p\). Indeed the sum over
exact positive valuations at one root is precisely its constant
prime-power weight divided by \(p\). The initial root product is
\(O_J(\mathfrak S(N)/L^2)\), and at target primes the two
weights vanish at their shared root. Inserting (3) gives
\[
 \sum_{\substack{x\in NJ\\(x,N)=1}}
    D^{\omega(x)+\omega(y)}W_\xi(x)W_\zeta(y)
 \ll_{D,\epsilon,J}\frac M{L^2}
     (2+|\xi|)^c(2+|\zeta|)^c,
       \qquad c=D(4/\pi+\epsilon).                            \tag{6}
\]
If a fixed actual \(p\mid x\) is imposed, put \(x=pv\);
use the primitive forms \(v,N-pv\) at length \(\asymp_J N/p\),
reset all positive powers of \(p\) on the first arm to 1,
and extract \(D A_\xi(p)\) once. Only one root survives
at the leading prime \(p\), giving a bounded local change;
\(p\mid N\) never contributes on target-unit rows. For
\(p\le N^{1/4}\) the coefficient-size and length requirements
of the theorem have fixed slack, as in the cited wide lemma.
This supplies (6) with the extra factor \(O_D(A_\xi(p)/p)\);
the reflected estimate has \(A_\zeta(p)/p\).
Therefore the union bound for a genuinely small factor costs
\(O_\gamma(\eta^\gamma)\) and an extra exponent \(\gamma\)
in the extracted arm's frequency by (4).
A true \(\Pi\)-leg may instead be majorized by \(L\) times
the indicator of \(N^{1/4}\)-rough integers, whose Euler
cost under (6) is bounded for fixed \(D\). There is no tiny
factor on the true prime leg. These arguments prove absolute
pairing inequalities for every choice of \(V_f\) or \(\Pi\)
on the two arms; addition gives those for \(H_f\).

Take, for instance, \(D=5/4\), \(\epsilon=1/40\),
and \(\gamma=1/4\), so that \(c+\gamma<2\).
Let \(\chi\) be a fixed smooth profile equal to 1 on
\((-\infty,-2]\), zero on \([-1,\infty)\), and between 0
and 1. For fixed \(0<\delta<1/20\) set
\[
       f_\delta(t)=P(t)\chi((t-1/2)/\delta)\quad(t\ge0).
\]
Then \(f_\delta=f_*\) below \(1/2-2\delta\) and
\(f_\delta\) is zero from \(1/2-\delta\) onward. In their
common real extensions the sharp profile is compactly supported,
is \(C^1\), and its second derivative is of bounded variation;
thus its Fourier transform is \(O((2+|\xi|)^{-3})\).
The difference has the exact form
\[
    f_\delta(t)-f_*(t)=\delta^2\Phi_\delta((t-1/2)/\delta),
\]
where \(\Phi_\delta\) is supported on \([-2,0]\) and has uniformly
bounded piecewise derivatives through order three, is \(C^1\),
and has second derivative of uniformly bounded variation.
This follows directly from the quadratic zero of \(P\), without
a bound on the unscaled derivatives of the original taper.
By Fourier scaling, for every fixed \(0\le j<2\),
\[
 \int_{\mathbb R}|\widehat{f_\delta-f_*}(\xi)|
                         (2+|\xi|)^j\,d\xi
                               \ll_j \delta^{2-j}.             \tag{7}
\]
Both profile norms with \(j=c+\gamma\) are thus uniformly
bounded. Equations (5)--(7) prove all the stated positive
bounds, including the absolute paired comparison with
\(\kappa=2-c-\gamma>0\), independent of the shrinking width.
For the rank tail multiply the positive weights by
\(D^{\omega(x)+\omega(y)}\) in (6) and divide by \(D^K\).

## 3. The short load and the binary atom

Fix \(\delta>0\) first. Both moduli in
\(\langle V_{f_\delta},V_{f_\delta}\rangle\) are at most
\(N^{1/2-\delta}\). They are coprime on physical target-unit rows
and each is coprime to \(N\). Actual CRT, opening the target
units over divisors of \({\rm rad}(N)\), gives density
\((\varphi(N)/N)/(de)\) and crossed total floor error
\(N^{1-2\delta+o(1)}\), including the log weights by partial
summation on the central interval. In the principal, complete
the two signed Möbius harmonics one at a time at
\(S=\exp((\log L)^4)\), with the actual opposite-divisor mask.
This is the same standard short two-variable completion as in
[the two-endpoint calculation, §2](../nearfull_high_vaughan/JointGiantEndpointDerivative.md).
The Euler series before the two inverse zetas is
\(\prod_{p\nmid N}(1-p^{-s}-p^{-t})\) at \((s,t)\) near \((1,1)\).
Including \(\varphi(N)/N\), its regular factor at \((1,1)\)
is \(\mathfrak S(N)\). The zeroth moment on either side is
zero; the first-log/first-log moment is \(\mathfrak S(N)\).
For clarity, the arbitrary-log completion follows by convolving
ordinary Mertens with the absolutely summable regular Euler factors
on abscissae \(1-1/(10\log L)\); while completing one variable
the opposite divisor just joins the polynomial coprimality mask.
The exceptional Euler factor norms are polylogarithmic in \(L\),
as checked in the cited completion, and the fixed smooth cutoffs
are handled by partial summation. This leaves higher fixed log
moments bounded by \((\log L)^{O(1)}\).
Taylor expansion on the completed \(d,e\le S\) box therefore
gives the principal \(f_\delta'(0)^2M+o(M)=M+o(M)\).
Here the real spatial \(\log x\log y/L^2\) is replaced by
\(1+O_J(1/L)\) **after** computing the signed main.

For \(\langle V_{f_\delta},\Pi\rangle\) and its reflection
use ordinary maximal-prefix prime BV at these same strictly
sub-root moduli, retaining \((d,N)=1\) and the true central
spatial \(\log x\). The signed \(\mu(d)/\varphi(d)\) model
has a zero at the zeroth moment and first moment
\(-\mathfrak S(N)\), as in
[the whole mark transfer, §2](../nearfull_high_vaughan/WholeMarkPrimeTransfer.md).
Both genuine prime crosses are thus
\(-f_\delta'(0)M+o(M)=M+o(M)\). Proper prime powers from a BV
statement about \(\Lambda\) may be removed: each of the
\(N^{1/2+o(1)}\) genuine higher powers contributes at most a
fixed log power times \(\tau(N-p^j)\) actual moduli, which
is power-small overall. The term \(\langle\Pi,\Pi\rangle=R_J\)
is kept with its exact coefficient one. Consequently for every
fixed \(\delta\),
\[
             \langle H_{f_\delta},H_{f_\delta}\rangle
                              =R_J-M+o_\delta(M).
\]
Use (7) in the actual absolute difference first, take the
limsup over even \(N\) for every fixed \(\delta\), and then
let \(\delta\downarrow0\). This proves (1) without applying
prime BV at modulus \(\sqrt N\) or any above-root modulus.

## 4. Actual squarefree reduction and the surviving signs

Choose sufficiently large fixed rank \(K\) and sufficiently small
fixed floor \(\eta>0\). By §2 this costs at most
\(O_J((D^{-K}+\eta^\gamma)M)\) in absolute weight. Remaining
nonsquarefree rows have some \(p^2\mid x\) or \(p^2\mid y\)
with \(p>N^\eta\); there are \(O(N^{1-\eta})\) such rows,
and each score has a fixed divisor-power bound times \(L\).
These rows cost \(o(M)\). This gives absolute deletion of
all nonsquarefree rows upon finally making the fixed floor
arbitrarily small. On the retained rows the own-log argument
\(\log d/\log n\) differs from \(\log d/L\) by \(O_J(1/L)\);
the sharp profile is uniformly Lipschitz even at its half-root.
On a fixed-rank row the score changes by \(O_{J,K}(1)\).
The number of bilateral \(N^\eta\)-rough rows is
\(O_{\eta,J}(M/L^2)\) by the same positive two-root sieve
(as in [the wide finite-angle lemma, §3](../nearfull_high_vaughan/WideJointGiantFiniteAngles.md)).
The score change is therefore \(o(M)\). This comparison
uses no bound for the number of subset sums at polynomial
distance \(\delta\) from half.

For a squarefree composite with own-log angles \(u_i\),
\(\sum_i u_i=1\), the normalized own-log score is
\(\sum_{A}(-1)^{|A|} f_*(\sum_{i\in A}u_i)\).
For every even rank, the complement of \(A\) has the same
sign as \(A\), and
\(f_*(t)+f_*(1-t)=P(t)\), also at equality by the double zero.
Thus this score equals the half full alternating sum of
the symmetric quartic. All ranks \(>4\) give zero in this
even sector by finite differences. Rank four gives half the
constant fourth derivative \(-288\) times \(\prod u_i\),
as in (2). Rank two gives \(1-P(u)\) for the smaller angle
\(u\); this is positive by strict monotonicity of
\(g(a)=a^2(7-3a^2)/4\) for \(0<a<1\).
The signed integrals in the ordinary simplex harmonic density
are \(3/2\) and \(-1\), respectively:
\[
 \int_0^{1/2}\frac{1-P(u)}{u(1-u)}\,du=\frac32,
 \qquad
 -\frac{144}{4!}\int_{u_1+\cdots+u_4=1\atop u_i>0}
                                          du_1du_2du_3=-1.
\]
These elementary angular integrals are not assertions about
the actual paired rank distribution.

For rank three with no giant, the score is
\(1-\sum_iP(u_i)\ge0\): the arguments \(a_i=1-2u_i\)
belong to \([0,1]\) and sum to 1, and
\[
 g(a+b)-g(a)-g(b)
  =ab\{3.5-3(a^2+b^2)-4.5ab\}\ge0\qquad(a+b\le1).
\]
With a giant and two smaller angles \(a,b\), the score is
the actual second difference on its small cofactor,
\[
 H_3(a,b)=ab\{14-36(1-a-b)^2-12(a^2+b^2)\}.
\]
It can be negative. At sufficiently high odd rank a giant has
zero score by applying the quartic finite difference to its
entire complement, but nongiant odd ranks remain. The
ordinary simplex rank-two and rank-four masses cannot be
substituted for their **actual signed cross** at a specified \(N\).
No statement here estimates that cross or the combined
odd-rank remainder sufficiently for a binary lower.
