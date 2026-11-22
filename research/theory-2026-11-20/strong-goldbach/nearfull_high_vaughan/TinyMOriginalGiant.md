# Tiny tags in the actual small quotient of the original giant score

Use the exact score from
[the giant-divisor reduction](../giant_prime_divisor_remainder/Proof.md).
At an even target \(N\), let \(L=\log N\), \(\ell=\log L\),
\(S=\exp(\ell^4)\), \(B=N/S\), \(T_y=y/B\), and
\[
 Q_y(m)=\sum_{\substack{d\mid m\\d<T_y}}\mu(d).
\]
Fix \(J\subset J_0\Subset(0,1)\), a fixed \(C_1>0\), and a real interval
\(I\subset(\sqrt N/(S L^{C_1}),B]\). The literal prime score is
\[
 {\cal G}_I=\sum_{\substack{x+r m=N,\ x\in NJ,\ r\in I\\
                              x,r\ {\rm genuine\ primes}}}
                     (\log x)(\log r)Q_y(m),\qquad y=N-x.       \tag{1}
\]
Take disjoint tiny banks as in
[TinyTagProjection.md](TinyTagProjection.md), with fixed
\(1<\theta_-<\theta_+<2\). There can be \(O_K(\log\ell)\) families,
each of \(K\) separated colors. A family is hit if **the original
\(m\)** has a prime factor in every color. Denote by \(E(m)\) the
indicator of at least one hit.

**Theorem.** On \(\operatorname{rad}(N)\le L^{B_0}\) for fixed \(B_0\),
the portion of (1) with multiplier \(E(m)\) is \(O_D(NL^{-D})\)
for any fixed \(D>0\), when the fixed \(K\) is chosen sufficiently
large after \(D\). This includes the physical subpower-\(m\) range
and involves no change of the two actual primes or the original
strict \(Q_y\) endpoint. The conclusion covers all the displayed
giant \(r\) values, not a chosen dyad of \(r\). There is no estimate
here for the **no-hit** part, which includes the genuine prime
\(m\) rows.

There is also an **all-even native** consequence, on the exact
grouped high-cut score (1) of
[NativeCofactorProduct.md](NativeCofactorProduct.md): for every
fixed \(\varepsilon>0\) the part with \(E(m)=1\) and the genuine
left prime label \(f\le N^{2/3-\varepsilon}\) is \(O_D(NL^{-D})\).
The right label \(h>W\) is unrestricted in that score. This
second assertion is not a transfer of the first assertion
without a radical restriction. It concerns a different, already
grouped representation of the near-full interval, and the two
deletions are not added.

## 1. Two exact short-quotient tools

First we record the true harmonic for the Type I principal,
with **no** radical restriction. Let \(\mathcal B\) be any subset
of the bank primes, and \(H\le N^C\) for fixed \(C\). On a real
subinterval of \([M,2M]\cap[T,\infty)\) with \(M\gg S\) and
\(T\asymp S\), and with real or complex \(F\) of fixed log-bounded
supremum and total variation, one has
\[
 \sum_{\substack{m\ {\rm in\ that\ interval}\\
             (m,H)=1,\ m\ {\rm avoids}\ \mathcal B}}
       \frac{F(m)}m\sum_{\substack{d\mid m\\d<T}}\mu(d)
                =O_D(L^{-D}).                                \tag{2}
\]
Here and below all harmless fixed constants, including the
valuation mask \(H\), may be different from those in a preceding
packet. Put \(\mathcal M=H\prod_{p\in\mathcal B}p\) simply as a
formal finite prime-exclusion mask; no polynomial bound on
\(\mathcal M\) is required. At
\(\sigma=1-c/\ell^{\theta_+}\) for fixed small \(c>0\),
\[
 \prod_{p\mid\mathcal M}(1+p^{-\sigma})+
 \prod_{p\mid\mathcal M}(1-p^{-\sigma})^{-1}
 \ll \ell^{O(1)} .
\]
Indeed \(p^{1-\sigma}\) is bounded for every bank prime, whose
total reciprocal weight is \(O(\log\ell)\). For \(H\) split
\(p\le L^2\) and \(p>L^2\), using prime Mertens for the former
and \(O(L)\) factors for the latter. The inverse-mask convolution
of \(\mu\) with integers supported on the excluded primes now
proves the uniform harmonic
\[
 \sum_{\substack{d\le t\\(d,\mathcal M)=1}}\frac{\mu(d)}d
             =O_D(L^{-D})\qquad(t\ge c_0\sqrt S) .
\]
Split the convolution at \(\sqrt t\), use ordinary Mertens
on the smaller part, and bound the complementary harmonic
by \(t^{-(1-\sigma)/2}\ell^{O(1)}\). The real moving endpoints,
including strict bounds, are allowed by taking integer parts
and absorbing a possible endpoint of size \(O(1/t)\).

Now open \(m=dn,\ d<T\). For \(d>\sqrt S\), fix \(n\) and use
this signed harmonic with the precise independent \(d\)-interval
and weight \(F(dn)\), then sum \(1/n\). For \(d\le\sqrt S\)
count the \(\mathcal M\)-units in the free \(n\)-interval of scale
\(M/d\gg\sqrt S\). In a real interval of scale \(Y\) the exact
unit-count error is at most
\[
 O\!\left(Y^\sigma\prod_{p\mid\mathcal M}(1+p^{-\sigma})\right):
\]
expand the finite prime exclusions and bound each floor or
omitted expected count by \(O(\min(1,Y/e))\) at its unit label
\(e\mid\operatorname{rad}(\mathcal M)\). Partial summation gives
the same relative saving in the \(n^{-1}F(dn)\) harmonic.
The remaining density \(\varphi(\mathcal M)/\mathcal M\)
is independent of \(d\), except for \(1/d\) and its actual own
unit condition, and the signed \(d\)-prefix up to \(\sqrt S\)
is arbitrarily log-small. This proves (2). Exact hit and no-hit
Booleans are finite combinations of avoidance masks. On
\(O_K(\log\ell)\) disjoint families their total expansion has
\(\ell^{O_K(1)}\) terms, also harmless for (2).

Second, for projected Type II use the first actual hit family.
Freeze the original \(m\)-gate \(y/m\in I\) and the strict
\(d<T_y\) threshold by relative log-fine \(y\)-cells, so
\(T_y\) is temporarily \(T\). A moved boundary \(y=m r_0\)
or \(y=Bd\) is priced using the true multiple \(m\mid y\) or
\(d\mid m\mid y\), respectively. At label \(b\) such rows are
\(O(N L^{-G}/b+1)\) in the relative \(L^{-G}\) crossing band.
Their total is \(O(NL^{1-G}+N^{1/2+o(1)})\), summing only the
actual \(m\le N^{1/2} S L^{C_1}\) or \(d\ll S\). Crossed
divisor moments give arbitrary-log accuracy after increasing
\(G\). Smooth the now independent \(m\)-window and the short
\(d\)-threshold in still thinner relative collars. A changed
divisor cutoff at scale \(X\) has actual labels dividing \(y\)
and total count \(O(N(L^{-G'}+1/X)+X L^{-G'}+1)\) per
cutoff; here \(X\gg S\) and \(X\le N^{1/2+o(1)}\).
Choose the fixed smoothing precision after the cell count.
All coefficients, before/after opening, are bounded by a fixed
divisor-power envelope, possibly times fixed powers of \(L\).

Discard actual \(p^2\mid y\) for a chosen bank prime. Their
count is \(O(N/p_0+\exp(O(\ell^{\theta_+})))\) by summing
multiples, and their divisor-weighted contribution is
arbitrarily log-small. Extract \(w\mid m\), one actual prime
from each chosen color, by the exact reciprocal hit allocation
at \(m=w m'\):
\[
                 \prod_\nu (1+\omega_\nu(m'))^{-1},
\]
where \(\omega_\nu\) counts distinct primes of that color.
Earlier failures are unchanged on \(m'\) because families
are disjoint. The extracted primes are **below \(T\)**, so the
original weight becomes the exact expression
\[
 Q_T(wm')=
       \sum_{s\mid w}\mu(s)
              \sum_{\substack{d\mid m'\\ ds<T}}\mu(d) .          \tag{3}
\]
Here the removal of squares made \((w,m')=1\); no extra
selected-tag gcd is kept in the operator. Restoring square
rows on either side of (3) costs the same positive estimate,
because all retained factorizations still have \(w\mid m\mid y\)
and any new incompatible row still has \(p^2\mid y\). The
sum over the \(2^K\) subset choices changes only fixed constants.

To use one Mellin separation for the smooth \(ds<T\) gate,
take real part \(1/L\) for its step kernel; the norm is a
fixed log power and the tail at sufficiently large fixed
log-power height is arbitrarily log-small by integration
by parts. The tag part is \(s^{-v}\), a product of individual
bounded multipliers on the selected colors; the other part
is the actual \(d^{-v}\) on the residual, with the independent
bound \(d\le T(1+O(L^{-G'}))\) throughout the smoothing.
The independent \(m=w m'\) smooth cutoff separates by its
own Mellin integral, with a unit-modulus product on \(w\).
The central \(x\)-weight is separated on the two source
factors by the same standard real Mellin procedure. The
result is the exact coefficient shape of TinyTagProjection,
with actual equation \(N-x=w b\) and a single divisor-bounded
coefficient of \(b\) containing \(m'\) and the genuine other
prime/other labels. Its square norm on \(w\asymp Y\) is
\(O((N/Y)L^{O(1)})\). In particular no averaging in the true
target occurs.

## 2. The original prime source at polylogarithmic radical

Remove the negligible nonunit or proper-power terms on the
\(x\)-leg and keep \((xrm,N)=1\). For actual central primes, if
\(r\mid N\) then \(r\mid x\) and \(x=r\); if a central \(x\mid N\)
there are \(O(1)\) such \(x\) and at most \(\tau(N-x)\) choices
of \(r\) each. These exceptions are negligible. In the opened Type I use of true
prime \(r\), removal of its target-prime values remains harmless:
there are \(O(L)\) such labels and \(O(N/r)\) physical multiples per
label, with the same divisor envelope and \(r\ge N^{1/2-o(1)}\).
Replacing \(x\)
by the Mangoldt function and requiring \(P^-(x)>Z=\exp(L^{.24})\)
costs power-small error from proper powers. Apply the exact
Vaughan identity at both cutoffs \(N^{.10}\) on this slot:
the two Type I terms are the short \(\mu\)-log convolution
minus the short \(\mu\)-short \(\Lambda\) convolution with a
free factor, and the last term is
\[
 \sum_{\substack{a b=x\\a>N^{.10}}}\mu(a)
              \sum_{\substack{f\mid b\\f>N^{.10}}}\Lambda(f).
\]
The identity follows from \(\mu*1\) and \(\Lambda*1=\log\);
the atom at \(x\le N^{.10}\) is outside the central support.
All physical factors of \(x\) are \(Z\)-rough.

For Type I write the actual modulus \(q=a f e\), \(f=1\)
in the first term, with \(e\) the usual short Bonferroni label
for the remaining free factor's \(Z\)-roughness. Since the \(Z\)-alphabet has reciprocal mass \(O(\ell)\), use degrees
\(C_D\ell\) with fixed sufficiently large \(C_D\). The reciprocal
tails are factorially small, and the label sizes/counts stay \(N^{o(1)}\). For every actual \(m\) the unexpanded
opposite \(r\) is a true prime at length scale \(N/m\ge
N^{1/2-o(1)}\) in the literal reduced class \(N\bar m\bmod q\).
Only \((m,Nq)=1\) is retained, as forced by the original
units and equality. The actual modulus \(q\le N^{.20+o(1)}\)
has a fixed power reserve for ordinary true-prime
Bombieri--Vinogradov at this length. It can be used in maximal
prefixes at the strict \(d<T_y\) endpoint after opening
\(d\mid m\); the \(\log(x/a)\) factor in the first term
has log-bounded real variation. Modulus multiplicities are
fixed divisor powers and are paid by weighted BV as in
[the polynomial native calibration](../reverse_giant_typeI/PolynomialNative.md).
The BV error over \(m\) sums its \(N/m\)-scale times
\(\tau(m)\), not the number of \(m\)'s. The positive first
omitted degree in the roughness expansion is in the same
BV range; its main upper uses factorial reciprocal tails.
No congruence for arbitrary signed \(m\) has been assumed.

In the genuine Type I model set \(x=N-mr\), so the measure is
\(dx/m\). At fixed central \(x\) and fixed \(q\) with external
weights, \(T_y\) is fixed, and the physical \(m\)-interval
\(y/m\in I\) lies in \(m\ge T_y\). The model \(1/\varphi(q)\)
is independent of \(m\); the remaining condition \((m,Nq)=1\)
is exact. Apply (2) with \(E(m)\) expanded only on this
principal, and sum the other reciprocal labels with fixed
log-power cost. This settles both original Type I terms,
in fact without a radical assumption.

For Type II the two actual \(Z\)-rough factors \(a,b\) have
polynomial length and automatically avoid all tiny banks.
Use the beta coefficient displayed above, bounded by \(\log b\),
and the genuine \(\mu(a)\) coefficient. At small radical its
uniform full projected character cancellation and the
distinct-character Gram estimate are exactly those of
[the small-radical major proof, §§1–2](../small_radical_projection/Proof.md).
The rough cutoff is its original \(Z\); all input phases
have the fixed log-power height accounted for in §1.
Apply the tiny-tag operator with the exact zero-major bound
from those inputs. Its arbitrary-log second moment and
Cauchy against the literal residual \(b_{\rm res}=m'r\)
after (3) give arbitrary-log cancellation in each genuine
packet. All factor packets, log-fine cells, tag shells,
colors, Mellin norms and first-hit terms fit the fixed log
losses by choosing the comparison precision before \(K\).
Restoring the already paid real boundaries proves (1) on the
stated \(E(m)=1\) rows.

## 3. All-even grouped native application

Keep the exact grouped native weight \(H_U(A)H_U(C)Q_y(m)\)
and cutoff \(f\le N^{2/3-\varepsilon}\), so
\(A\gg N^{1/3+\varepsilon}\). The source is \(A f\), with
\(A\) and actual \(f\) both \(z=\exp(\ell^2)\)-rough, thus
avoiding the entire chosen tiny \(m\)-bank automatically.
The genuine \(m\le S^{C_0}\) is extracted exactly as in §1.
Its remaining residual coefficient now includes the true
\(h\)-prime and \(H_U(C)\), still with fixed divisor envelope.

For the source character estimate open \(H_U(A)\) and the
true rough mask as in AllEvenNative. The principal is its
original signed rough harmonic at \(U\), uniform in
polynomial coprime masks. The nonprincipal bound and the
distinct-character Gram use unrestricted \(r=3\) Burgess
on the actual free \(A\)-factor and whole \(f\)-interval,
as in [PooledFarOverRoot.md, §1](PooledFarOverRoot.md).
The first free scale is \(\ge N^{1/3+\varepsilon-o(1)}\)
after dividing the subpower labels, and \(f>W=N^{1/2-o(1)}\).
No high-conductor estimate for a prime-only sum is used.
After the usual fixed divisor clipping on the actual \(A\mid x\),
TinyTagProjection gives the same complete covered conclusion.
No assumption on \(C\)'s length or on the right prime-label
exponent beyond its literal native support was needed for
this residual norm. This proves the second assertion.

The total reciprocal mass of tiny bank labels allows only
\(O(\log\ell)\) independent constant-mass families. Neither
these estimates nor the m-harmonic evaluated for their
modeled principals supplies a true full no-hit signed
estimate.
