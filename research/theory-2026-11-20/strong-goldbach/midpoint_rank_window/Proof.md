# A shrinking rank window for the balanced-triprime midpoint transfer

Let \(P\) be a large even integer, \(I=[P/3,2P/3]\), \(X=P/3\),
\(L=\log P\), and \(S(P)\) the binary singular series. Write
\(\langle W,T\rangle=\sum_{n\in I}W(n)T(P-n)\) and
\[
 D_h(n)=(\log n)\sum_{d\mid n}\mu(d)h(\log_n d).
\]
Fix a nonincreasing smooth \(F(s)\) on the real line with \(F=1\) through
\(s=-1\), \(F=0\) from \(s=1\), \(F=1/2\) on \([-1/4,1/4]\), and
\(F(s)+F(-s)=1\). For example, integrate a nonnegative even smooth bump
supported in \((-1,-1/4)\cup(1/4,1)\) of total mass one. For
\(0<\delta<.001\) put, on \([0,1]\),
\[
 f(t)=F((t-1/2)/\delta),\qquad f_0=(2f-1)_+,\qquad g=f-f_0.
\]
Then \(f_0=1\) through \(1/2-\delta\), \(f_0=0\) from \(1/2-\delta/4\),
and \(g(t)=H((t-1/2)/\delta)\) for the single smooth compact even bump
\(H(s)=\min(F(s),1-F(s))\). Write \(U=D_f,\ E=D_g\).

**Theorem.** Let \(T(r)\) be \(\log r\) times the indicator in \(I\)
of squarefree triprimes with three prime factors in prescribed fixed
polynomial windows and all \(>P^\eta\), where \(\eta>0\) is fixed.
In particular, the three factors may all lie near \(P^{1/3}\); there
is no short-factor assumption \(p<P^{1/12}\). Put
\[
 {\cal W}_\delta(P)=\{n\in I:\ \mu^2(n)=1,\ (n,P)=1,\
  \omega(n)\ {\rm even},\
 .35\log(1/\delta)<\omega(n)<3.6\log(1/\delta)\}.
\]
Then
\[
 \lim_{\delta\downarrow0}\ \limsup_{\substack{P\to\infty\\2\mid P}}
 \frac{\left|\langle U,T\rangle-
        \langle E1_{{\cal W}_\delta(P)},T\rangle\right|}{XS(P)}=0.       \tag{1}
\]
Moreover the omitted \(E\) term off this window is small in **total
variation**, against any test satisfying
\(|T(r)|\le L\,1_{P^-(r)>P^\eta}\). The signed subhalf transfer in
(1) is only asserted for the actual triprime test, not for arbitrary
rough weights. It extends to fixed finite linear combinations of
such windows.

Thus a macroscopic failure of the balanced-row transfer along a
sequence of narrowing admissible cutoffs has to persist on even ranks
comparable to \(\log(1/\delta)\). There is no saving or sign for the
whole surviving window. At fixed \(\delta\) this window is finite, but
it is not fixed as \(\delta\downarrow0\). The statement does not
allow arbitrary \(\delta=\delta(P)\).

## 1. Even sector and the actual triprime test

Since \(g(t)=g(1-t)\), complementary divisors cancel exactly in
\(E(n)\) whenever \(\mu(n)=-1\), including primes. Also \(U-E=D_{f_0}\).
For fixed \(\delta\) we have
\[
                       \langle D_{f_0},T\rangle=o_\delta(XS(P)).         \tag{2}
\]
The support of \(f_0\) stays a fixed distance below \(1/2\). Ordinary
convolution Bombieri--Vinogradov applies to the indicator of products
of distinct primes from the prescribed polynomial intervals at every
level \(1/2-\epsilon\), with maximal reduced residue. See
[Theorem 3.2 of *Bounded gaps between products of distinct primes*](https://doi.org/10.1007/s40993-017-0089-3)
and [Motohashi's convolution theorem](https://doi.org/10.3792/pja/1195518296).
For overlapping unequal windows split their endpoints into finitely
many disjoint intervals and use the finitely many multiplicity patterns.
Equivalently, convolve ordered prime lists on the disjoint intervals,
divide by the appropriate label factorials, and omit repeats as in the
cited theorem. Central prefix cuts \(y\asymp P\) are available by the
maximal-prefix form of Motohashi's theorem; multiplying the three prime
sequences by interval indicators preserves its input bounds uniformly
by differences of prefixes. The fixed drop below \(1/2\) absorbs
constant and logarithmic endpoint variations. Weights \(\log r\) and
smooth physical weights are recovered by partial summation.

For the actual moving logarithm, Taylor expand \(a f_0(v/a)\) at \(a=1\),
where \(a=\log n/L=1+O(1/L)\), \(v=\log d/L\). After order \(K_0\) the
remainder in \(D_{f_0}\) is \(O_{\delta,K_0}(L^{-K_0}\tau(n))\). Each
coefficient function is smooth, constant near zero, and cut off through
the same subhalf level. The physical factors \(\log^j(1-r/P)\) are
smooth centrally. Choose \(K_0\) sufficiently large for the desired
log accuracy. Inputs not unit to \(P\) cost \(P^{1-\eta+o(1)}\):
on this support any common prime divisor of \(P,r,n\) exceeds \(P^\eta\).
Discard these physical inputs first, restrict divisor moduli to
\((d,P)=1\), and then restore unrestricted \(T\) for the signed
unit-modulus sum at the same power cost, using the \(O(L\tau(n))\)
absolute ceiling. After the progression comparison, the reduced main
has inner sum \(\sum_{(d,Pr)=1}\mu(d)h(\log_P d)/\phi(d)\) for a Taylor
coefficient \(h\). This is \(O_{A,\delta}(L^{-A})\) uniformly in the
central \(r\): integrate the large sharp cutoffs in
[the coprime harmonic Mertens calculation](../midpoint_mover/Proof.md#2-complete-modulus-range-for-the-signed-transfer).
All varying sharp cutoffs are \(>P^{.49}\). This proves (2).

At fixed \(\delta\), nonsquarefree \(n\) contribute \(o_{\eta,\delta}(XS(P))\)
in total variation against the rough ceiling. If \(P^-(n)>P^\alpha\),
prime squares cost \(P^{1-\alpha+o(1)}\) for fixed \(\alpha>0\).
On \(P^-(n)\le P^\alpha\), Fourier expansion uses the multiplicative
envelope \(g_t(n)=\prod_{p\mid n}\min(2,|t|\log p/L)\). Extract
\((|t|\alpha/2)^{1/2}\) from a least prime, replacing the factors
by \(\sqrt{2g_t(p)}\). Their prime reciprocal sum is
\(O(1+\log(2+|t|))\), by splitting at \(P^{1/(2+|t|)}\). Formula (3)
below therefore gives only polynomial growth in \(t\), the other side
being rough. Against the Schwartz bound for the fixed-\(\delta\) cutoff
this gives \(O_{\eta,\delta}(\alpha^{1/2}XS(P))\), as in
[the absolute physical estimate](../midpoint/Proof.md#2-an-absolute-physical-two-form-estimate).
First take \(P\to\infty\), then \(\alpha\downarrow0\), at fixed
\(\delta\). These deletion constants need not be uniform as
\(\delta\downarrow0\). The preceding target-unit physical count also
applies against all rough tests.

## 2. Uniform multiplicative estimate for the two affine forms

Let \(d=1\) or let \(d\in[P^{.4},P^{.6}]\) be squarefree,
\(P^\delta\)-rough and coprime to \(P\). Put \(x=P/(3d)\).
For a nonnegative multiplicative function \(A\) constant on positive
prime powers, with \(0\le A(p)\le M\) uniformly, the corrected
[Henriot, Theorem 5](https://doi.org/10.1017/S0305004114000280)
([preprint and basic formulation](https://arxiv.org/abs/1102.1643))
on the primitive linear forms \(m,P-dm\) yields
\[
 \sum_{x\le m\le 2x} A(m)1_{P^-(P-dm)>P^\eta}
 \ll_{\eta,M}\frac{P S(P)}{dL^2}\frac{d}{\phi(d)}
       \exp\!\left(\sum_{p\le P}\frac{A(p)}p\right).                      \tag{3}
\]
Endpoints may be included by enlarging the interval by one. It has
full dyadic length, and the polynomial product has degree two,
coefficients \(O(P)\), and \(x\gg P^{.4}\). Thus a single
coefficient-height exponent, e.g. \(1/10\), works. The
multiplicative-class constants depend only on \(M\): subpower growth
follows from \(\max(1,M)^{\omega(n)}\ll_{\epsilon,M}n^\epsilon\).

The prefactor's root count is two for \(p\nmid Pd\), one for
\(p\mid Pd\). Its product through \(x\) is
\(O(S(P)L^{-2}d/\phi(d))\) by Mertens and \(\log x\asymp L\);
treat 2 directly. Indeed the additional factor at an odd \(p\mid d\)
is \((p-1)/(p-2)\), whose ratio to \(p/(p-1)\) gives a bounded
absolute Euler product. Since \(d\) is rough, \(d/\phi(d)=1+o_\delta(1)\)
uniformly, as it has \(O(1/\delta)\) prime factors.

Use the theorem's raw nonnegative local sum rather than attaching a
second discriminant product. For exponents \((i,j)=(1,0),(0,1)\) the
starred local densities are at most \(1/p\) (the second is zero
when \(p\mid d\)). Higher powers of one form cost \(O_M(p^{-2})\).
Both exponents positive are impossible unless \(p\mid P\); even then
they have zero weight for \(p\le P^\eta\) by roughness of \(P-dm\).
At \(p\mid P,\ p>P^\eta\) and \(p\nmid d\), either one of the two
linear congruences bounds the joint density by \(p^{-\max(i,j)}\).
All positive powers cost \(O_M(1/p)\) there, with \(O_\eta(1)\)
such primes. The rough test's own prime reciprocal sum over
\(P^\eta<p\le P\) is \(O_\eta(1)\). This verifies (3) with coefficient
**one** before the \(A(p)/p\) exponent.

For a complete dyad \(D<d\le2D\), \(P^{.39}<D<P^{.61}\), the
one-form version with prime value \(b1_{p>P^\delta}\), \(0<b<1\),
likewise gives
\[
 \sum_{D<d\le2D,\ P^-(d)>P^\delta}b^{\omega(d)}
       \ll_b (D/L)\delta^{-b}.                                           \tag{4}
\]
Indeed \(\sum_{P^\delta<p\le P}1/p\le\log(1/\delta)+O(1)\) for all
sufficiently large \(P\) at fixed \(\delta\). Its limiting implied
constant is independent of \(\delta\). There is no short-interval
prime theorem or composite-divisor assumption here.

## 3. Lower edge of the window

Take \(K\ge1\), \((K+2)\delta<.05\). On squarefree unit \(n\) with
\(\omega(n)\le K\), split off all prime factors \(\le P^\delta\)
in \(n_s\). Open the larger divisors only:
\[
 D_g(n)/\log n=\sum_{d\mid n/n_s}\mu(d)\sum_{v\mid n_s}\mu(v)g(\log_n(dv)).
\]
A contributing \(d\) must satisfy \(|\log_P d-1/2|\le(K+2)\delta\)
for large \(P\) at fixed \(\delta,K\), since \(\log_P n_s\le K\delta\).
Impose this necessary condition before taking absolute values.
The Fourier transform of \(g(t/a)\) has envelope
\(C_j\delta(1+\delta|t|)^{-j}\) in frequency \(t\), uniformly for
\(a=\log n/L\), since translation costs only a phase. The inner
sum is bounded by the integral of the envelope times
\(\prod_{p\mid n_s}\min(2,|t|\log p/L)\), up to the absolute inverse
Fourier normalization. On the restricted set introduce
\(1_{\omega(n)\le K}\le b^{-K}b^{\omega(n)}\); this separates over
\(d,n/d\) since they are coprime. Only now drop remaining restrictions
to upper-bound. With \(m=n/d\), its multiplicative weight is
\[
 A(p)=b\min(2,|t|\log p/L)\quad(p\le P^\delta),\qquad
 A(p)=b\quad(p>P^\delta).
\]
Its prime reciprocal sum is at most
\(b\log(1/\delta)+O_b(1+\log(2+\delta|t|))\): split smaller primes at
\(P^{1/|t|}\) if needed, and use
\(\sum_{p\le y}\log p/p\ll\log(2y)\) and Mertens; if the splitting
point is below 2 use only the cap 2. Thus (3) costs at most
\(\delta^{-b}(2+\delta|t|)^{C_b}\) beyond its prefactor. Choose
\(j>C_b+2\) and integrate; the rescaled cost is uniform in \(\delta\).

Sum \(b^{\omega(d)}/d\) in the necessary collar, including prime
\(d\). At most \(C((K+2)\delta L+1)\) complete dyads cover it.
Formula (4) on those dyads gives reciprocal mass
\(\ll_b (K+2)\delta^{1-b}\) for large \(P\) at fixed \(\delta,K\).
After multiplying both external logarithms this proves
\[
 \limsup_{P\to\infty}
 \frac{\sum_{\substack{n\in I:\mu^2(n)=1,\ (n,P)=1\\ \omega(n)\le K}}
       |E(n)T(P-n)|}{XS(P)}
 \ll_{\eta,b}(K+2)b^{-K}\delta^{1-2b}.                                  \tag{5}
\]
Take \(b=1/5,\ K=\lfloor .35\log(1/\delta)\rfloor\). The power
\(0.6-.35\log5>0.036\) beats \(K+2\).

## 4. Upper edge of the window and the \(4/\pi\) factor

Let \(h(s)=|1-e^{is}|\), with period mean \(4/\pi\). Uniformly for
real \(t\) and large \(P\), for every \(\epsilon>0\),
\[
 \sum_{p\le P}\frac{h(t\log p/L)}p
 \le (4/\pi+\epsilon)\log(2+|t|)+O_\epsilon(1).                         \tag{6}
\]
Write \(T_0=|t|\). For \(T_0\le4\), the log-harmonic prime bound and
\(h(s)\le|s|\) give \(O(1)\). For \(4<T_0\le L^{1/2}\) put
\(Y=\exp(L/T_0)\); the primes below \(Y\) cost \(O(1)\).
Above \(Y\), PNT with classical error and partial summation replace
the sum by \(\int_Y^P h(T_0\log x/L)\,dx/(x\log x)\) with bounded
error: the weight \(h(T_0\log x/L)/x\) is Lipschitz with a.e.
derivative \(O((1+T_0/L)x^{-2})\), and the prime counting error
is \(O(x e^{-c\sqrt{\log x}})\). The integral equals
\(\int_1^{T_0}h(s)\,ds/s=(4/\pi)\log T_0+O(1)\), using the bounded
primitive of the mean-zero periodic remainder.

For \(L^{1/2}<T_0\le L^3\) put \(Y=\exp((\log L)^4)\).
The smaller primes cost \(O(\log\log L)\); above \(Y\) the same
PNT error is \(o(1)\) even with \(T_0/L\le L^2\). The corresponding
integral up to \(T_0\), with any positive lower endpoint, is
at most \((4/\pi)\log T_0+O(1)\), since its part below 1 is \(O(1)\).
Absorb the smaller-prime cost into
\(\epsilon\log T_0+O_\epsilon(1)\). For \(T_0>L^3\) use
\(2\log L+O(1)\le(2/3)\log T_0+O(1)\). This proves (6).

For high ranks Fourier-expand the *full* divisor sum and insert
\(B^{-K}B^{\omega(n)}\) for \(B>1\). Formula (3) with \(d=1\) and
\(A(p)=B h(t\log p/L)\), followed by (6), gives
\[
 \limsup_{P\to\infty}
 \frac{\sum_{n\in I,\ \omega(n)\ge K}|E(n)T(P-n)|}{XS(P)}
 \ll_{\eta,B,\epsilon} B^{-K}\delta^{-B(4/\pi+\epsilon)}.                \tag{7}
\]
Indeed integrating \(\delta(1+\delta|t|)^{-j}
(2+|t|)^{B(4/\pi+\epsilon)}\) costs
\(O(\delta^{-B(4/\pi+\epsilon)})\) at sufficiently large fixed \(j\).
The Euler factor is \(h\), not its square. With \(B=e,\epsilon=.01\),
\(e(4/\pi+.01)<3.49<3.6\); use
\(K=\lceil3.6\log(1/\delta)\rceil\). In general the lower threshold may
be any constant strictly below
\(\sup_{0<b<1/2}(1-2b)/\log(1/b)\), and the upper any constant
strictly above \(4e/\pi\). They do not meet.

Combine (2), the fixed-\(\delta\) deletions, and (5),(7), then let
\(\delta\downarrow0\). This proves (1). In the identity \(2J=V-U\)
the remaining sum still concerns the actual fixed reflected target.
The estimates do not prove that sum vanishes, nor that a Goldbach
representation exists.

**Dated comparison.** [Pham, October 30 v1](https://www.preprints.org/manuscript/202610.3061) treats a different balanced rough-pair benchmark and signed boundary problem. [Arneth, October 19 v1](https://zenodo.org/records/23477014) isolates a remaining correlation using a cubic prime minorant. Neither is used for the new rank window of this actual smooth midpoint term; the ordinary convolution and short-interval upper bounds used here are the cited existing inputs. No claim on the sign within the surviving window follows.
