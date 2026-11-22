# The native critical deletion at every even target

Use the exact high-cut identity (1) of
[NativeCofactorProduct.md](NativeCofactorProduct.md), with
\(I=[N/S^{C_0},N/S]\), \(C_0>1\), the genuine two prime labels
\(f,h>W=\sqrt N/S^{C_0+10}\), and the **grouped** short coefficient
\[
 H_U(n)=1_{n>1}\sum_{\substack{d\mid n\\ d\le U}}\mu(d),
 \qquad U=\exp((\log\log N)^3).
\]
In particular \(H_U(1)=0\), the shorter \(Q_y(m)\) is unchanged,
and the two true additive products are \(x=A f,\ y=m C h=N-x\).
All actual rough and target-unit conditions of (1) remain.

**Extension.** For some fixed \(\delta>0\), the whole native
critical contribution
\[
                      A(mC)\ge N\exp(-(\log N)^\delta)
\]
in this **same** score is \(o(N)\) uniformly for all sufficiently
large individual even \(N\), with no restriction on
\(\operatorname{rad}(N)\). Thus this high-cut form of \(C_I\) may
be restricted to \(A(mC)<N\exp(-(\log N)^\delta)\), and its
surviving genuine prime-label product satisfies
\(f h\gg_{J_0}N\exp((\log N)^\delta)\).
This is an extension of the grouped native region only, not of
a different raw-\(\mu\) or low-cutoff score. The surviving
operator is not bounded here.

There are two places where the earlier proof imposed a small
radical. We give their replacements separately. All other
phase, product-cut, and short-mask arithmetic is retained.

## 1. The actual projected character input at square-root length

For every retained native critical row, \(A,C,f,h=N^{1/2+o(1)}\):
\(A\) and \(mC\) are between \(\sqrt N\exp(\pm 2(\log N)^\delta)\)
by the argument in the companion, \(m\le S^{C_0}\), and
\(A f,m C h\asymp_{J_0}N\). Any actual full projected modulus
has the form \(M=N d_{\rm arc}\), \(d_{\rm arc}\le
(\log N)^{D_0}\) for fixed \(D_0\). At such a modulus and for
any nonprincipal \(\chi\bmod M\), uniformly on every real
subinterval at length scale \(X=N^{1/2+o(1)}\), one has
\[
                    \left|\sum_{n\in H}\chi(n)\right|
                       \ll X N^{-1/20}.                           \tag{1}
\]
Here the \(o(1)\) in the length refers to the actual scales and
label divisions below. Use the unrestricted-modulus \(r=2\)
case of [Burgess, *On character sums and L-series, II*](https://doi.org/10.1112/plms/s3-13.1.524),
namely \(O_\epsilon(Y^{1/2}q^{3/16+\epsilon})\) for a primitive
nonprincipal character of conductor \(q\) on an interval of
length \(Y\). This case has no cube-free requirement; compare
the explicit scope of [Punch, (1)](https://arxiv.org/abs/2610.22939).
Write the imprimitive sum as the inclusion-exclusion on primes
of \(M\) not dividing the inducing conductor, then apply the
primitive bound on the divided interval of length \(O(X/w)\)
for each such divisor \(w\). If this divided interval exceeds
the conductor, complete periods cancel before using the bound.
For \(X<w\le 2X\) a possible integer of the short interval is
also covered by a constant times the same bound. The total is
\[
       \ll_\epsilon X^{1/2}M^{3/16+\epsilon}\tau(M)
       \ll N^{7/16+\epsilon+o(1)} .
\]
The empty terms \(w>2X\) are omitted and \(\tau(M)=N^{o(1)}\).
A sufficiently small fixed \(\epsilon>0\) proves (1);
partial summation also permits the usual fixed-log-frequency
twists. Thus no zero-free theorem for \(\mu\)-twists is needed.

To evaluate the *particular* grouped \(A\)-coefficient of the
native proof, open the true \(d\le U\) in \(H_U(A)\), with
\(P^-(d)>z=\exp((\log\log N)^2)\) and \((d,M)=1\).
The variable \(A\) is \(z\)-rough and a target unit, so it is
automatically a unit at every prime in any additional
polylogarithmic rational-arc denominator. Expand any periodic
arc factors on these unit groups in characters at log-power
cost. The inducing conductors still divide the corresponding
\(N\) times a polylogarithmic arc factor. The true bank
avoidances and roughness on \(A/d\) open by labels \(e\) of size
and count at most \(\exp(O((\log N)^{.3}))\), exactly as in
NativeCofactorProduct §1. They are coprime to \(d,M\): primes
of \(e\) are either \(\le z\) or above the actual \(U\), and
primes of \(M\) can be omitted from the sieve alphabet
because the summation is on units at \(M\). Thus for every
retained \(d,e\) the true free length of \(G=A/(de)\) is
\(N^{1/2-o(1)}\). The omitted-label factorial harmonic and
the \(O(X/(de)+1)\) count still give arbitrary-log accuracy,
including all floor costs. For a nonprincipal character use
(1) in \(G\) and sum only the reciprocal \(d,e\) harmonics.
For a principal character, the integer unit count in \(G\)
has density \(\varphi(M)/M\) and floor \(O(\tau(M))\), which
remains negligible even after all subpower label counts.
The main factors the signed
\[
       \sum_{d\le U,\ P^-(d)>z,\ (d,M)=1}\frac{\mu(d)}d
                   =O_A((\log N)^{-A}),
\]
by the arbitrary-mask rough harmonic of the all-even
[high-cut proof](Proof.md), §1. The modulus-size bound
\(M\le N(\log N)^{D_0}\) is sufficient for that harmonic.
The usual divisor-moment clipping on the long \(A\)-slot,
both in the actual physical sum and in the linear character
bound, is unchanged.

The other projected-major use of small radical was the
Gram estimate in restricted Bessel. For distinct characters
on \(M\), apply (1) to their product quotient character on the
**whole integer** \(f\)-interval \(N^{1/2+o(1)}\). The normalized
off-diagonal Gram entries are \(O(N^{-1/20})\), and the
exceptional set of high tag polynomials has \(N^{o(1)}\)
members by the original literal high-moment identity
(products of tags below the full modulus). Hence the same
row-sum argument gives restricted Bessel on the genuine
\(\Lambda(f)\) coefficient with the exact source masks,
without a prime character-sum assertion. The projector
Fourier coefficients are still bounded by \(1/\varphi(N)\)
on the actual full unit group, by its onto reduction to
modulus \(N\); this reasoning never uses a small radical.
Tag moment normalizations and full-product Parseval are
unchanged. The [projected minor comparison](../target_slope_switch/Proof.md) is already valid for general \(N\); the
one-prime endpoint primitivity argument in the native proof
uses the actual prime \(f\), complete bank avoidance and
target units, not the radical. Remove the finitely many
target prime divisors from the bank supply at reciprocal
cost \(O((\log N)\exp(-c(\log N)^{.1}))=o(1)\), retaining the
same fixed-width family margins. These observations give
the same covered first-success cancellation on the literal
native product for every even target.

## 2. The actual overlap of the two positive prime sieves

The missed contribution still uses the positive simultaneous
upper sieve on \(f h\) from the native proof. Its support is
\(d\le N^{.0001}\). For \(d_f\mid f,d_h\mid h\) with
\([d_f,d_h]=d\), write \(j=(d_f,d_h)\); any compatible overlap
has \(j\mid N\). Unlike the small-radical case, \(j\) can now
be large, but always \(j\le N^{.0001}\). Divide both sides
of the actual equation by \(j\). The two progression factors
are \(A(d_f/j),mC(d_h/j)\) and the target is \(N'=N/j\).
The exact cross masks on \(A,d_h\) and \(mC,d_f\) are retained,
so these two factors are mutually coprime on the compatible
rows. They need not each be coprime to \(N'\); the plain
nonzero reciprocal bound only requires their mutual gcd
one and its actual nonzero phase multiplier. The **base**
coefficients are still target units at \(N\).

Relative to \(N'\), the two exponents of these products lie
in \([.5-o(1),.5002+o(1)]\), since
\(1\le d_f/j,d_h/j\le N^{.0001}\). For large \(N\) one can
take \(g\in[.999,1.001]\), \(h\le .501\), where \(g\) is their
sum and \(h\) their maximum. The four reciprocal exponents
of [the high-cut proof](Proof.md) are then respectively at
most \(-.02405,-.0615,-.0241,-.06175\), before the arbitrarily
small fixed Fourier losses. Thus the nonzero terms have more
than enough uniform power margin for the \(N^{.0002}\)
possible label pairs and all remaining subpower/logarithmic
counts. The target \(N/j\) is itself \(\ge N^{.9999}\), so a
fixed power saving there remains one relative to \(N\).
The zero density is exactly \(N j/(A mC d_f d_h)\) with its
original central integral. The signed gcd inclusion--exclusion
therefore reassembles the unchanged actual root model
\(\rho(p)=1\) for \(p\mid N A mC\) and \(2\) otherwise.
Nothing about the number or size distribution of primes
dividing \(N\) enters its dimension bound; their harmless
Euler correction is \((\log\log N)^{O(1)}\) uniformly for
\(N A m C\le N^{O(1)}\).

The resulting positive main is still
\(O\bigl(N(\log\log N)^{O(1)}/(A mC)\bigr)\) after both
genuine prime log weights. Bind the independent **actual**
integer harmonic windows of \(A,C\) with the same
\(H_U^2\) estimates and Cauchy as in NativeCofactorProduct
§3; the principal model may drop the base target-unit
constraints only in this positive majorant. The independent
bank-failure count at that stage is now taken with the
unchanged target-unit bank labels but no extra radical
condition. This yields
\(O(N(\log\log N)^{O(1)}L^{2\delta-\kappa/2})+o(N)=o(N)\)
after the same fixed order of comparison precision, bank
color count, failure exponent \(\kappa\), and smaller
\(\delta<\min(.01,\kappa/10)\). At the curved native product
boundary, the same positive reciprocal calculation can
drop units of the free \(f,h\) and keep the exact base-unit
and coprimality constraints; no extra unit-floor loss
arises there. Thus the result holds for the entire literal
native chart, not only a rectangular or smoothed subset.
