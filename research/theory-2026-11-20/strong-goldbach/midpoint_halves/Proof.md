# Nonnegative reflected correlations of the opposite halves of critical polynomial sieves

Let \(P\) tend to infinity through even integers, \(I=[P/3,2P/3]\),
\(X=P/3,\ L=\log P,\ r=P-n\), and put
\(\langle W,T\rangle=\sum_{n\in I}W(n)T(P-n)\). Write
\[
 \mathfrak S(P)=2\prod_{p>2}(1-(p-1)^{-2})
       \prod_{\substack{p\mid P\\p>2}}(p-1)/(p-2).
\]
For a fixed integer \(k\ge2\) define the critical one-sided polynomial weight
and its two actual parts by
\[
 A_k(n)=(\log n)\sum_{d\mid n}\mu(d)(1-2\log_n d)_+^k,\qquad
 H_k(n)=A_k(n)1_{\mu^2(n)=1,\ \omega(n)\equiv k\pmod2},\qquad
 O_k=A_k-H_k .
\]
Here \(u_+=\max(u,0)\). On nonsquarefree inputs all of \(A_k\) is assigned
to \(O_k\); it is not asserted to be a pure parity projector there.

**Theorem.** For fixed integers \(j,k\ge2\), at every large even target,
\[
 \langle O_j,O_k\rangle=\langle H_j,H_k\rangle+o(X\mathfrak S(P))
                       \ \ge -o(X\mathfrak S(P)).                       \tag{1}
\]
Each \(H_k\) is nonnegative and supported on squarefree ranks at most \(k\).
In particular the reflected correlation of the generally signed opposite
halves really has a one-sided asymptotic bound, not just a predicted sign.
Formula (1) extends by bilinearity to fixed linear combinations on each
side; the lower bound holds when the corresponding two finite-rank
combinations are nonnegative. This is an entrywise sign, not positive
semidefiniteness of the indefinite reflection pairing.

For instance \(H_2(n)=4(\log n)xy\) when \(n=pq\) is squarefree and zero
otherwise, where \(x=\log_n p,\ y=\log_n q\).
\(H_3=V+C_3\), where \(V(p)=\log p\) on primes and zero elsewhere, and
\(C_3(n)=24(\log n)xyz\) on squarefree triprimes (zero elsewhere).
Thus (1) for \(j=2,k=3\) compares a signed odd-against-even correlation
with genuine semiprime-against-(prime or triprime) counts, with the same
integer target on both sides. It does not assert those counts are positive
on their natural scale. Nor does this more gradual transition prove the
sharp-midpoint transfer, or binary Goldbach.

## 1. The finite-rank, positive half and its density

On squarefree \(n=p_1\cdots p_b\), put \(x_i=\log_n p_i\).
Pair \(d\) with \(n/d\). In the matching parity case,
\(2H_k(n)/\log n=\sum_{d\mid n}\mu(d)(1-2\log_n d)^k\).
In the other parity case both sides are zero. Its exponential generating
function on the right is
\[
 e^z\prod_{i=1}^b(1-e^{-2zx_i})=\prod_i2\sinh(zx_i).
\]
In particular \(H_k/\log n\) is a polynomial with nonnegative coefficients:
\[
 \frac{k!}{2}\sum_{\substack{m_i\ge1\ {\rm odd}\\\sum m_i=k}}
                          \prod_i\frac{2x_i^{m_i}}{m_i!}.             \tag{2}
\]
The lower-degree vanishing, positivity, and displayed examples follow.

First keep all primes \(>P^\alpha\) for fixed \(\alpha>0\). The ordinary
unshifted central mass of this truncated \(H_k\), divided by \(X\), tends
to the sum of the rank-\(b\) simplex integrals of (2) against
\(dx_1\cdots dx_{b-1}/(b!\prod x_i)\) on \(\sum x_i=1,\ x_i>\alpha\).
For \(b=1\) this denotes the evaluation at 1. Here and below only
\(1\le b\le k\) occur. To see the normalization, sum over the first
\(b-1\) prime labels with their reciprocal weights; the last prime lies
in \([P/(3p_1\cdots p_{b-1}),2P/(3p_1\cdots p_{b-1})]\). Uniform PNT
at last-prime lengths \(\gg P^\alpha\) gives \(X/(p_1\cdots p_{b-1}Lx_b)\);
the outside \(\log n=(1+O(1/L))L\) cancels \(L\). The other prime
reciprocal measures converge on compact subintervals to \(dx_i/x_i\).
Squeeze the moving simplex boundaries by fixed meshes and then reduce their
width, since the limiting densities are bounded away from zero exponents.
Repeated labels on this rough set cost \(P^{1-\alpha+o(1)}+P^{1/2+o(1)}\).
Division by \(b!\) removes the order. These arguments apply also with any
fixed polynomial windows on the prime factors.

As \(\alpha\downarrow0\) the integrand after cancellation of \(\prod x_i\)
is a polynomial, so there is no lower-face divergence. The uncut limiting
mass is
\[
 \frac{k!}{2(k-1)!}[t^k]\exp\!\left(\sum_{m\ge1\ {\rm odd}}\frac{2t^m}{m}\right)
 =\frac{k}{2}[t^k]\frac{1+t}{1-t}=k.                                 \tag{3}
\]
Indeed the integral of \(\prod x_i^{m_i-1}\) is
\(\prod (m_i-1)!/(k-1)!\). To get the ordinary mass without initially
truncating, an unweighted one-form version of §2 gives \(O_k(\alpha^\nu X)\)
on the small-prime sector, or one may sum (2) by prime reciprocal estimates.
The two-stage limit alone suffices below.

## 2. Squareful and very small factors: why two derivatives suffice

We record an absolute bound since the cutoff for \(k=2\) is only \(C^1\).
Fix \(\nu=1/16\). For fixed \(j,k\ge2\), the contribution to
\(\sum_{n\in I}|A_j(n)A_k(r)|\) from \(P^-(n)\le P^\alpha\) or
\(P^-(r)\le P^\alpha\) is \(O_{j,k}(\alpha^\nu X\mathfrak S(P))\).
There is also an unrestricted \(O_{j,k}(X\mathfrak S(P))\) bound.
Both apply if an \(A\) in absolute values is replaced by the corresponding
\(H\) or \(O\), since these only retain or omit an entire physical row.
At fixed \(\alpha\), squareful or target-nonunit rows on the doubly rough
set cost \(o_\alpha(X\mathfrak S(P))\) by the large-prime-square count
above or by summing over primes \(>P^\alpha\) of \(P\); absolute weights
are \(P^{o(1)}\).

Here are details of the finite Fourier integrability. Extend
\(a_k(v)=(1-2v)_+^k\) smoothly and compactly on the negative side
(agree on a neighborhood of \(0\)). The transforms of
\(c a_k(v/c),\ c=\log n/L\asymp1\), have a common bound
\(C_k(1+|t|)^{-k-1}\): the distributional derivative of order \(k+1\)
is a bounded measure. Absolute inversion bounds \(A_k/L\) by the integral
of this envelope times \(\prod_{p\mid n}h(t\log p/L)\), where
\(h(u)=|1-e^{iu}|\). For the side with a least prime below \(P^\alpha\)
extract \((\alpha|t|/2)^\nu\), replacing its local factors by
\(h_\nu(u)=2^\nu h(u)^{1-\nu}\). The ratios at all other primes are
at most one. Use \(h_0=h\) on an unmarked side.

Apply the raw nonnegative local sum in corrected
[Henriot, Theorem 5](https://doi.org/10.1017/S0305004114000280)
to \(n,P-n\), with these multiplicative factors constant on positive
prime powers. The degree, coefficient height, central interval length
and uniform class bounds are as in
[the basic two-form estimate](../midpoint/Proof.md#2-an-absolute-physical-two-form-estimate).
Its prefactor is \(O(\mathfrak S(P)/L^2)\); its local series at \(p\) is bounded
by \(1+(a+b)/p+O(p^{-2})+O(1_{p\mid P}ab/p)\), where \(a,b\in[0,2]\)
are the spectral weights. At a shared prime use \(p^{-\max(i,j)}\) for
joint positive valuations; at other primes there is no such pair.
For \(\max(|t|,|w|)\le\sqrt L\), summing \(ab/p\) over \(p\mid P\)
costs \(O(1)\): on \(p\le L^2\), each local weight is
\(O((2\log L/\sqrt L)^{1-\nu})\), and \(\sum_{p\mid P,p>L^2}1/p\ll1\).
For larger frequencies the entire exceptional product is
\((\log L)^{O(1)}\), since \(\sum_{p\mid P}1/p\le\log\log L+O(1)\)
by the same split. Thus it can be absorbed by an arbitrarily small
power of the largest frequency.

For completeness, uniformly in \(t\), at either \(v=0\) or \(v=\nu\),
\(\sum_{p\le P}h_v(t\log p/L)/p\le
 (\overline h_v+\epsilon)\log(2+|t|)+O_\epsilon(1)\), where the bar
denotes periodic mean. The following argument also handles the cusps
of \(h_v\). For bounded \(T=|t|\), use
\(h_v(s)\le2^\nu |s|^{1-\nu}\) at small \(s\) and partial summation.
For \(4<T\le\sqrt L\) remove primes below \(\exp(L/T)\) at \(O(1)\)
cost by that same estimate. For \(\sqrt L<T\le L^3\) remove primes
below \(\exp((\log L)^4)\) at \(O(\log\log L)\) cost. On the remaining
interval replace prime reciprocal measure by \(dx/(x\log x)\) via
the classical PNT. Explicitly the primitive error for the prime reciprocal
measure minus \(dx/(x\log x)\), with the constant taken at infinity, is
\(O(\exp(-c\sqrt{\log x}))\); this is partial summation of the PNT.
The total variation of \(h_v(T\log x/L)\) on that interval is \(O(1+T)\)
since every period has uniformly bounded variation. The product of this
variation and the error bound at the lower endpoint is \(o(1)\) uniformly
in the indicated ranges. The integral of \(h_v(s)/s\) from any positive
lower endpoint to \(T\) is at most \(\overline h_v\log T+O(1)\), using
integrability at zero and bounded primitive of the periodic centered
function. Absorb \(O(\log\log L)\) in \(\epsilon\log T\) in the second
range. For \(T>L^3\), use \(2\log L+O(1)\). Jensen gives
\(\overline h_v\le2^v(4/\pi)^{1-v}<1.4\).

It follows that the two-form upper bound after the prefactor is
\(O((2+|t|)^{1.5}(2+|w|)^{1.5})\), allowing room for the exceptional
product. Each frequency integral with exponent \(-3+1.5+\nu<-1\)
converges, proving the asserted absolute estimates. With one form alone
there is a single \(1/L\) prefactor and no shared-prime term.

## 3. The actual critical correlations

We prove, for each fixed pair of degrees,
\[
 \langle A_j,A_k\rangle=(4jk+o(1))X\mathfrak S(P),\qquad
 \langle A_j,H_k\rangle=(2jk+o(1))X\mathfrak S(P).                 \tag{4}
\]
Write \(w_{k,d}(u)=(\log u)(1-2\log d/\log u)_+^k\). This is nonnegative
and increasing on the central interval. Its maximum is at \(u=2P/3\)
and \(\sum_{d\le\sqrt{2P/3}}\sup_I w_{k,d}\ll_k\sqrt P/L^{k-1}\):
sum \(\log^k(\sqrt{2P/3}/d)\) by integral comparison. Opening the two
divisors gives the condition \((d,e)\mid P\), and then one residue modulo
\([d,e]\). The one-class count against \(w_{j,d}(u)w_{k,e}(P-u)\)
differs from its integral divided by \([d,e]\) by \(O(\sup w_{j,d}\sup w_{k,e})\);
partial summation and monotonicity of both factors give that variation bound.
The **sum** of floor errors is \(O_{j,k}(P/L^{j+k-2})=o(X)\), including
the critical moving endpoints.

We detail the remaining smooth CRT mean. Put
\[
 {\cal B}_P(s,t)=
 \sum_{(d,e)\mid P}\frac{\mu(d)\mu(e)}{[d,e]d^s e^t}
 =\frac{K_P(s,t)}{\zeta(1+s)\zeta(1+t)} .
\]
Its factor before removing the inverse zetas is
\(1-u-v+1_{p\mid P}puv\), with \(u=p^{-1-s},v=p^{-1-t}\).
Thus \(K_P(0,0)=\mathfrak S(P)\) exactly, including \(p=2\).
For the double Dirichlet coefficients \(c_{h,i}\) of \(K_P\),
\(\sum |c_{h,i}|(hi)^{1/\log L}\ll(\log L)^{O(1)}\). Indeed the local
quotient after its constant is
\((1_{p\mid P}p-1)uv/((1-u)(1-v))\). Away from target primes the
absolute sum is uniformly convergent; on \(p\mid P,\ p\le L^2\)
its first majorant is \(O(1/p)\), and above \(L^2\) the sum
\(\sum_{p\mid P}p^{-1+2/\log L}\) over these primes is \(O(1)\) for large \(P\).
This moment also bounds the unweighted log moments by powers of \(\log L\).

For \(h\le P^{1/8},\,u_0\in I\), convolution with \(\mu(m)/m\) gives
\[
 \sum_m\frac{\mu(m)}m w_{j,hm}(u_0)
   =2j+O_j((1+\log h)/L).                                           \tag{5}
\]
Indeed set \(Z=\sqrt{u_0}/h\) and expand
\(2^j(\log(Z/m))^j/(\log u_0)^{j-1}\) for \(m\le Z\).
Classical PNT partial summation gives, with arbitrary log savings at \(Z\),
\(\sum_{m\le Z}\mu(m)/m=0+O_A((\log Z)^{-A})\),
\(\sum_{m\le Z}\mu(m)\log m/m=-1+O_A((\log Z)^{-A})\),
and bounded higher moments of any fixed order (their limits are
derivatives of \(1/\zeta(1+s)\) at \(s=0\)).
This yields \(2j(1-2\log h/\log u_0)^{j-1}+O_j(1/L)\), proving (5).
The trivial bound is \(O_j(L^2)\) for every \(h\). Large \(h\) or \(i\)
costs arbitrary log savings by the preceding tilted moment. At small
\(h,i\), expand the product of (5) and its \(k\)-counterpart; the summed
errors are \(O((\log L)^{O_{j,k}(1)}/L)=o(1)\).
This evaluates the CRT integrand as \(4jk\mathfrak S(P)+o(1)\) uniformly
in \(u_0\), proving the first formula of (4).

For the second formula first impose \(P^-(r)>P^\alpha\), costing
\(O_{j,k}(\alpha^\nu X\mathfrak S(P))\) by §2. Nonunit \(r\) now
cost \(P^{1-\alpha+o(1)}\); restrict divisors to \((d,P)=1\), then restore
unrestricted rough \(r\) in the progression calculation with the same
physical power cost. The ordinary maximal-prefix convolution
[Bombieri–Vinogradov theorem of Motohashi](https://www.jstage.jst.go.jp/article/pjab1945/52/6/52_6_273/_pdf)
applies at \(d\le\sqrt P/L^B\), \(B\) sufficiently large for the desired
logarithmic saving. For prime products compare also
[the explicit distinct-prime version, Thm. 3.2](https://doi.org/10.1007/s40993-017-0089-3).
In (2) use ordered lists, divide by \(b!\), and separate the prime weights
\((\log p_i/L)^{m_i}1_{p_i>P^\alpha}\), with remaining centrally smooth
factor \(L^k/(\log r)^{k-1}\). Such truncated prime sequences satisfy the
same Siegel–Walfisz inputs by partial summation. Repeated rough labels
may be included in applying the theorem then removed: in physical
divisor sums they cost \(P^{1-\alpha+o(1)}+P^{1/2+o(1)}\), and in
the expected main each total weight costs only a further \(O(L^2)\).
On the subcritical interval \(w_{j,d}(P-r)\) is an ordinary polynomial
in \(\log d\) with smooth coefficients in \(\log(P-r)\); a fixed number
of partial summations incurs only log powers. The comparison replaces
\(1_{r\equiv P\bmod d}\) by \(1_{(r,d)=1}/\phi(d)\), with summed
\(O_A(PL^{-A})\) error there.

In the omitted logarithmic shoulder \(\sqrt P/L^B<d\le\sqrt{2P/3}\),
\(\sup w_{j,d}\ll_{j,B}(\log L)^j/L^{j-1}\).
Uniformly for target-unit \(d\) there, the actual rough \(H_k\)-mass on
\(r=P-dm\) is \(O_{\alpha,k}(P/\phi(d))\): bound \(H_k\) by \(O_k(L)\)
on this support and upper-sieve the one linear form in an interval
of length \(\asymp P/d\) to \(\min(P^\alpha,P^{1/100})\).
The sieve product is \(O_\alpha(d/(\phi(d)L))\). For example a
dimension-one upper sieve of fixed large parameter with level
\((P/d)^{1/3}\) has negligible integer-count remainders (reduce the
sifting exponent further to \(1/200\) if desired). The expected main
also has this bound since the total rough \(H_k\)-mass is \(O_k(P)\)
by (2) and the fixed-\(\alpha\) calculation. As
\(\sum_{D<d\le2D}1/\phi(d)\ll1\) by the Euler divisor expansion
of \(d/\phi(d)\), this shoulder costs \(O_{\alpha,j,k,B}(P(\log L)^{j+1}/L^{j-1})=o_\alpha(P)\)
on both sides. This is not a trivial integer estimate for \(j=2\).

The full arithmetic reference at fixed rough \(r\), \(n=P-r\), contains
\[
 \sum_{(d,Pr)=1}\frac{\mu(d)}{\phi(d)}w_{j,d}(n)
                 =2j\,\mathfrak S(Pr)+o(1) .
\]
The one-variable Dirichlet product is \(K_{Pr}(s)/\zeta(1+s)\),
with local \(K=(1-1_{p\nmid Pr}p^{-s}/(p-1))/(1-p^{-1-s})\).
As before \(K(0)=\mathfrak S(Pr)\), and its absolute coefficient
moment at \(1/\log L\) costs \((\log L)^{O(1)}\), uniformly for
\(Pr\le P^2\): at \(p\nmid Pr\) the correction starts at
\(O(p^{-2+1/\log L})\), and at \(p\mid Pr\) use the same split at \(L^2\).
Apply (5). On rough \(r\), \(\mathfrak S(Pr)=\mathfrak S(P)(1+o_\alpha(1))\)
since there are only \(O_\alpha(1)\) new primes \(>P^\alpha\).
Use the fixed-\(\alpha\) central mass from §1, then send \(\alpha\downarrow0\)
using (3) and the error from §2. This proves (4).

Expansion of \(\langle A_j-H_j,A_k-H_k\rangle\) now proves (1).
In the same way, if \(T\) is \(\log r\) times any fixed polynomially
rough triprime window of normalized central mass \(t\), the specific
quadratic signed comparison is
\[
  \langle O_2,T\rangle=4tX\mathfrak S(P)-\langle H_2,T\rangle
                                 +o(X\mathfrak S(P)).
\]
No sign of this last difference is known here.

**Relation to earlier work.** These are truncated polynomial Möbius
sieves and generalized von Mangoldt finite differences, not a new
substitute for the classical asymptotic sieve; compare
[Friedlander–Iwaniec, *On Bombieri's asymptotic sieve*](https://www.numdam.org/item/ASNSP_1978_4_5_4_719_0.pdf).
The specific comparison here is between the two actual parity halves
at one macroscopic even target, for the critical moving cutoff with
quadratic or higher vanishing. The [earlier smooth midpoint](../midpoint/Proof.md)
and [its growing-rank window](../midpoint_rank_window/Proof.md) use a
narrower, complementary transition and do not give (1) for these weights.
No priority claim is needed, and no asymptotic for a pure prime-pair or
pure semiprime-pair count is asserted.

**Dated comparison.** [Arneth, October 19, 2026](https://zenodo.org/records/23477014) uses a different cubic prime minorant, and [Bahbouhi, November 2026](https://www.preprints.org/manuscript/202611.0975) studies different finite multiplicity moments. The critical polynomial opposite-half equality above concerns their actual reflected covariance, not the sufficiency of those other moment methods or a pure prime-pair bound.
