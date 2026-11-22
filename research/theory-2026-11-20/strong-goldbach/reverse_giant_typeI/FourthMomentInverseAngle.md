# A whole above-root modulus band from inverse fourth moments

Use [the direct double-Möbius remainder](SecondTypeI.md),
with every actual cutoff, and \(I\subset[N^{1/2+\varepsilon},B]\).
Consider the simultaneous physical intervals
\[
 N^{.249}\le a\le N^{.251},\quad
 N^{.355}\le m,k\le N^{.395},\quad
 N^{.501}\le b\le N^{.518}.                                      \tag{1}
\]
The decimals in (1) are exact.

**Theorem.** The restriction of \(\mathcal D_I\) to (1)
is \(O_{A,\varepsilon,J_0}(NL^{-A})\) for each fixed \(A>0\)
and every prescribed even \(N\). No factorability or
smoothness of \(b\), and no restriction on
\(\operatorname{rad}(N)\), is required. The condition
\(\mu(b)\ne0\) already makes \(b\) squarefree.

The whole indicated \(b\)-band is removed in this physical
angle, not just the factored class in
[FactoredInverseAngle.md](FactoredInverseAngle.md). It is
above the range in [ConductorHalf.md](ConductorHalf.md).
Moreover \(mk\asymp N/a\) gives its exponent at most
\(.751+o(1)\), less than \(1.5\cdot .501\), so it is outside
the [Weil rectangle](IntegerRectangles.md). The long
factor exponent for [OverRootAngles.md](OverRootAngles.md)
is near \(.75\), not on its Fouvry–Radziwiłł rails.
No bound on the entire over-root remainder or on
the original signed giant score is asserted.

## 1. A fourth moment for arbitrary odd squarefree moduli

Write
\[
 S_q(\lambda,h)=\sum_{v\bmod q}^{*}e_q(\lambda\overline v+hv),
 \qquad e_q(u)=e^{2\pi i u/q}.
\]
Let \(q\) be odd and squarefree. Let \(W(v)\) be a smooth
weight in a shifted positive interval at scale \(K'\),
with \(\|W\|_\infty\ll1\), support length \(O(K')\), and
derivatives of order \(r\) bounded by
\(K'^{-r}L^{O_r(1)}\). We only use polynomial scales
\(K'<q\) with fixed power slack. Put
\[
 T_q(\lambda)=\sum_{(v,q)=1}W(v)e_q(\lambda\overline v),
 \qquad \lambda\in(\mathbb Z/q\mathbb Z)^\times .
\]
For fixed small \(\rho>0\) with \(K'\gg N^{2\rho}\) we prove
\[
 \left(\sum_{\lambda\bmod q}^{*}|T_q(\lambda)|^4\right)^{1/4}
       \ll N^{\rho+o(1)}\left(q^{5/8}+q^{1/4}(K')^{1/2}\right).
                                                                  \tag{2}
\]
All moduli and scales here are at most \(N^{O(1)}\).
The implicit \(o(1)\) permits fixed powers of \(L\).

Normalize \(c_h=q^{-1}\sum_v W(v)e_q(-hv)\).
The elementary bound is \(|c_h|\ll K'/q\). Poisson or
repeated summation by parts, at the stated derivatives,
permits restricting to the signed frequencies
\(|h|\le H=(q/K')N^\rho<q/2\) at arbitrary fixed
power accuracy in \(N\). Complete Weil with
\((\lambda,q)=1\) pays the tail pointwise. The zero
term is \(c_0 S_q(\lambda,0)=c_0\mu(q)\), with
fourth norm \(O(K'/q^{3/4})\), harmless in (2).

The complete sums \(S_q(\lambda,h)\) are real, by
negating their summation variable. Thus complex
conjugation on two Fourier coefficients in the
fourth moment does not alter their actual \(h\)'s.
CRT, for \(\kappa=q/p\), writes the local normalized
factor at \(p\mid q\) as
\[
  p^{-1/2}S_p(\lambda\overline\kappa,h\overline\kappa)
          =-\mathrm{Kl}_2(\lambda h\overline\kappa^{\,2};p)
\]
when \(h\) is a unit at \(p\).
Use [Fouvry–Kowalski–Michel, Corollary 3.3, the even-rank specialization of Corollary 1.6](https://people.math.ethz.ch/~kowalski/sums-of-products.pdf):
the complete \(p\)-sum of four rank-two normalized
Kloosterman traces at multiplicative shifts is
\(O(\sqrt p)\) unless every distinct shift occurs
an even number of times. Indeed the even-rank
sheaf has symplectic monodromy and trivial
projective automorphism group, and their normal
tuple condition is precisely some odd multiplicity.
The estimate is for \(\lambda\ne0\) and applies
uniformly to all nonzero shifts, including negative
integers modulo \(p\). If one of the four \(h\)'s
vanishes mod \(p\), its local normalized sum is
\(-p^{-1/2}\) for all \(\lambda\ne0\) and the other
three factors are bounded by 2. Thus this case also
has local bound \(O(\sqrt p)\). In the paired case
use \(O(p)\). Consequently the absolute complete
four-product for the unnormalized \(S_q\)'s is
at most \(q^{5/2+o(1)}\) times
\(\prod_{p\ {\rm paired}}\sqrt p\).

There are three possible pairings of four positions.
Dominate the last product by summing over disjoint
squarefree divisors \(e_1,e_2,e_3\) of \(q\), with
each divisor imposing its corresponding pairing
congruences and weight \(\sqrt{e_1e_2e_3}\).
There are at most \(4^{\omega(q)}=q^{o(1)}\) choices.
Let
\[
 x=h_1+h_2-h_3-h_4,\quad
 y=h_1-h_2+h_3-h_4,\quad
 z=h_1-h_2-h_3+h_4 .
\]
The pairings \((12)(34),(13)(24),(14)(23)\)
respectively constrain \((y,z),(x,z),(x,y)\).
Conversely each pair of linear constraints gives
the pairing, since 2 is invertible modulo all
\(e_i\). Therefore \(e_2e_3\mid x,\ e_1e_3\mid y\)
and \(e_1e_2\mid z\).
For fixed \(h_1,x,y,z\) there are at most a bounded
number of integer tuples (in fact at most one).
Thus the number within \(|h_i|\le H\) is
\[
 \ll H\prod_{i<j}\left(1+\frac{H}{e_i e_j}\right).
\]
Writing \(D=e_1e_2e_3\), the product of this bound
with \(\sqrt D/H^4\) is \(O(1+\sqrt q/H^2)\).
To see this, expand
\(\sqrt D\prod_{i<j}(H^{-1}+(e_i e_j)^{-1})\).
The term with three powers \(H^{-1}\) is
\(\sqrt D/H^3\); those with two are at most
\(\sqrt q/H^2\); those with one are at most 1;
and the term with none is \(D^{-3/2}\).
This counts exact equalities as well as differing
pairings at different primes. Since
\((K'/q)^4 H^4=N^{4\rho}\), the result of summing
the Fourier expansion is
\[
 \ll N^{4\rho+o(1)} q^{5/2}
               (1+\sqrt q\,(K'/q)^2).
\]
It includes all nonzero-frequency configurations,
even those reducing to zero at some local prime.
Taking fourth roots proves (2).

## 2. Applying the moment to the true three-coordinate count

Work in fixed dyads with \(a\asymp A_0,m\asymp M,k\asymp K\),
\(A_0MK\asymp N\), and \(b\) in (1). Open the actual
\(d\mid m\) in \(Q_y(m)\), with \(d<T_y\ll S\).
Keep \(a,b,d\) target units. The two free variables
\(n=m/d,k\) satisfy \(a n k\equiv N\overline d\bmod b\),
and a physical unit row requires \((ad,b)=1\).

The \(N\)-unit masks on \(n,k\) can be expanded with
target divisors \(f_1,f_2\mid\operatorname{rad}(N)\),
truncated to \(f_1,f_2\le N^\rho\), with
\(\rho=1/10000\).
The omitted terms cost \(N^{1-\rho+o(1)}\) on
the original physical integer rows. Indeed \(f_i\)
divides \(y\); for each such label there are at most
\(N/f_i\) multiples in the central interval, with no
additive floor. The number of other labels is at most
\(\tau(N)^{O(1)}\), while the tuples and absolute weights
over \(y\) are bounded by fixed divisor powers on
\(y,N-y\) and fixed log powers, all \(N^{o(1)}\).
Thus no support restriction on target prime factors
has been assumed. The \(f_i\)'s are units modulo \(b\).

After each of these openings there are two actual
intervals at scales \(M',K'\) for the free integers,
after possible division by \(d,f_1,f_2\).
Complete the one from the **smaller physical scale**
among \(M,K\) (before these divisions), and call its
free scale \(M'\). Call the other \(K'\).
Write \(M_*=\min(M,K)\), \(K_*=\max(M,K)\),
so \(M'\ll M_*,K'\ll K_*\) and
\(M'\gg N^{.355-\rho-o(1)}\). The relation is
\(uv\equiv c(a)\bmod b\), where
\(c(a)=c_*\overline a\) and \(c_*\) is a
fixed unit depending on \(N,d,f_1,f_2,b\).

Take smooth weights on the two intervals with the
same derivative convention as in §1, and arbitrary
\(|\alpha(a)|\le1\) on a fixed subinterval of the
actual \(a\)-dyad, restricted to \((a,b)=1\).
Complete \(u\). Its Fourier coefficients have size
\(O(M'/b)\), and only
\[
                 0<|j|\le J_2=(b/M')N^\rho
\]
are needed for the nonzero part, at arbitrary power
accuracy. Since
\(\log_N(A_0J_2)\le .251+.518-.355+2\rho+o(1)<.501\),
all ratios used below have determinant smaller than \(b\).
For \(g=(j,b)\), the normalized Fourier coefficient
magnitudes on the multiples of \(g\) sum to
\(O(L^{O(1)}/g)\), by real summation by parts.
Put \(q=b/g\); inserting \((v,g)=1\) by
\(e\mid g\) makes \(v=e v'\).
Squarefreeness gives \((e,q)=1\).
The inverse phase has unit numerator
\[
              \lambda=(j/g)c_*\overline{a e}\bmod q .
\]

For \(g\ge N^{.025}\) use completed Weil,
including the zero Ramanujan term after
completion. The latter costs \(O(K'/(e q))\).
Summing over \(a,g,e\) with the Fourier \(1/g\)
gives, per \(b\),
\[
           \ll N^{o(1)} A_0
                     (b^{1/2}N^{-.0375}+K_*/b).                  \tag{3}
\]
It holds also when \(q<K'\), by removing complete
periods or summing the zero and nonzero frequencies.

For \(g<N^{.025}\), \(q\ge N^{.476}\) while
\(K_*\ll N^{.395}\). Apply (2) after dividing
the \(v\)-interval by \(e\), so all length conditions
have a fixed power margin. Fix \(g,e\), the sign of
\(j\), and \(t=(a,|j|/g)\). On this set the distinct
pairs \((a,j)\) give distinct \(\lambda\bmod q\):
equality of two ratios modulo \(q\) forces their
integer cross difference to be zero, since
\(A_0 J_2<b/4\) for large \(N\); after dividing both
coordinates by \(t\) the ratios are reduced.
There are \(O((A_0/t)(J_2/(gt)))\) such pairs.
Hölder with (2) gives a saving after
\(\sum_{t\ge1} t^{-3/2}<\infty\). Summing \(g,e\) as
divisors costs \(N^{o(1)}\); we obtain, per \(b\),
\[
 \begin{split}
 &\ll N^{\rho+o(1)}\frac{M'}b(A_0J_2)^{3/4}
                      (b^{5/8}+b^{1/4}K_*^{1/2})\\
 &\ll N^{7\rho/4+o(1)} A_0^{3/4}(M_*/b)^{1/4}
                      (b^{5/8}+b^{1/4}K_*^{1/2}).                \tag{4}
 \end{split}
\]
All bounds are for the **sum over \(a\)** with its
arbitrary coefficient. In particular they serve the
weighted signed count and also the positive count
needed for cutoffs.

We sum (3)–(4) over the \(b\)-dyad.
At the worst fixed exponents from (1),
\(M_*\ll N^{.3755+o(1)}\) by \(a M K\asymp N\).
Ignoring the \(7\rho/4\) and the \(o(1)\), the two
exponents in (4) after summing \(b\) are at most
\[
 \tfrac34(.251)+\tfrac14(.3755)+\tfrac{11}8(.518)
                   =.994375,\qquad
 \tfrac34(.251)+\tfrac14(.3755)+\tfrac12(.395)+.518
                   =.997625 .
\]
The leading exponent in (3) after that sum is
\(.251+\tfrac32(.518)-.0375=.9905\); its other term
is smaller. These fixed reserves pay every
\(N^{o(1)}\) label count and all logarithmic weights.

The zero \(u\) frequency gives the exact unweighted
box density \(\varphi(b)/b^2\) times the two real
interval lengths, uniformly for each \((a,b)=1\).
Ordinary unit counting by divisors of \(b\), and
Euler summation for the smooth weights, pays floors
\(L^{O(1)}\tau(b)^{O(1)}(M'+K'+1)/b\); their total
has a fixed power reserve. For sharp intervals, bracket
each by smooth upper/lower weights with transitions
of relative size \(L^{-F'}\) at the physical scale,
and use the **positive** count (3)–(4), with
\(\alpha(a)=1\), for the differences. The principal
difference has corresponding relative-scale volume
\(O(M'K' L^{-F'})\) times its density, even for a
very short interval. Choose \(F'\) large. The same
elementary floors and nonzero errors apply to those
weights, so this recovers the sharp counts without
assuming any signed cancellation in a thin band.

## 3. Literal domain and zero mode

Take a fixed log-fine mesh on \(a,m,k\), with relative
step \(L^{-F}\), before varying \(b,d\). At fixed
\(b,d\), all original gates are axes or planes in
these log coordinates; in particular the moving
\(d<T_y\) and \(b>Z(N/(mk))\) are precisely
\(amk>Bd\) and \(mk>N/(b^2HL^{2D_1})\).
The new exponent bands (1) only add axis cuts.
Apply the positive version of §2 to the union of
boundary cells, with the fixed actual \(a\)-interval
per cell. For each fixed integer \(a\), each
non-axis plane has ambiguous area
\(O(MK L^{-F})\) in \(m,k\). The axes may be
enforced exactly beforehand. Thus the total
positive boundary principal at fixed \(a,b,d\)
is \(O(MK L^{-F}/(bd))\), or divided additionally
by \(f_1 f_2\) in the sieve-opened model. This
latter division also applies to the smoothing
losses, so the sum uses \(f_1,f_2\) reciprocals,
not their cardinalities. The arithmetic errors
are paid by (3)–(4), which allow arbitrary
subsets of the \(b\)'s per cell. The number of
cells costs only fixed log powers.
On interior cells, \(\log k\log j\), with
\(j=(N-amk)/b\), varies by \(O(L^{2-F})\).
Its replacement and the restoration of the
literal domain in the zero mode therefore cost
arbitrarily small log powers, by positivity and
the same counting estimates.

After the change \(n=m/d\) and restoring the
target-unit sums, the zero density at fixed
\(a,b,d\) has factor
\[
  \frac1d\,\frac{\varphi(b)}{b^2}
                  \left(\frac{\varphi(N)}N\right)^2 .
\]
Indeed \(\sum_{f\mid N, f\le N^\rho}\mu(f)/f
=\varphi(N)/N+O(N^{-\rho+o(1)})\), so the omitted
density is negligible too. The outside \((a,bN)=1\)
is exact and independent of \(d\). No unit factor
for \(j\) is inserted, as it is automatically a
target unit. At fixed real \(m,k\) in the domain
and fixed \(a,b\), the only remaining \(d\)-gate is
the literal \(d<T_y\). Its signed harmonic
\[
       \sum_{\substack{d<T_y\\(d,bN)=1}}\frac{\mu(d)}d
                   =O_A(L^{-A}),\qquad T_y\asymp S,
\]
is uniform by [IntegerRectangles.md](IntegerRectangles.md), (4).
After integration the model pays only the
reciprocal \(a,b\) harmonics and fixed log powers.
This proves the stated signed deletion.
