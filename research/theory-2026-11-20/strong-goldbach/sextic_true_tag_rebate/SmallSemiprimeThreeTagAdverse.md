# A signed debit for the small genuine semiprime against the full three-tag arm

Keep exactly \(N,J,L,M,S=G_b+W\), \(b=.003\), the original
sharp sextic and the target-unit pairing \(x+y=N,\ x\in NJ\),
as in the [three-by-three comparison](ThreeByThreeTagCredit.md).
Let \(\mathcal A\) be the whole following physical chamber:

* The first coordinate \(x=pq\) is a genuine squarefree
  semiprime, with the smaller prime \(p\) in
  \((N^{.003},N^{.080}]\);
* The second coordinate \(y\) is squarefree, with exactly
  three distinct primes in \((N^{.003},N^{.080}]\) and all
  remaining prime factors \(>N^{.080}\).

Take also its reflection \(\mathcal A^{\rm op}\).
There are no other angular, quotient-rank, or sign restrictions.

**Proposition.** Uniformly through individual sufficiently large
even targets, the complete original signed sum obeys
\[
 -.229M+o(M)
    < \sum_{\mathcal A\cup\mathcal A^{\rm op}} S(x)S(y)
    < -.0095M+o(M).
\]
This is a cost to remove a genuinely adverse part of the exterior,
not an additional positive credit. The remaining one-by-three
rows on which the one-tag coordinate is not a semiprime are
not covered.

## 1. The literal score and the signed sub-root calculation

Both coordinates pass the .003 gate and have \(Q=0\).
On the semiprime arm \(W=0\), since its second prime has
angle at least \(.920-O_J(1/L)\). On the three-tag arm
\(W=0\) even when the sum of the two least angles is small:
its two-tag quotient contains the physical third prime
\(\le N^{.080}\), whereas \(W\) would require quotient roughness
above \(N^{(.555-.065)/3}\). Thus both scored arms are the
original \(H\), with no prime atom. The exact .080 tag counts
are \(1,3\), respectively, so this sector is disjoint from every
one-by-two, two-by-three, three-by-three, zero-by-two and
at-least-four-tag chamber. Both arms contain a prime at most
\(N^{.080}\), excluding the .1251-rough and mixed Q-boundary
chambers. The long semiprime quotient also excludes the older
two-small-tag ambient. The two new orientations are distinct;
they use \(J\) and \(1-J\), of the same length.

For the left angle \(t=\log p/L\), put \(w(t)=1-F(t)\ge0\),
where \(F\) is the original sharp sextic. The left score is
\(Lw(t)+O_J(1)\). Write \(y=h m\) with its actual three
least primes in \(h\); their angles are \(u,v,w'\).
Write
\[
  g(s)=\frac{(1-\tau_u)(1-\tau_v)(1-\tau_{w'})F(s)}
                    {uv w'},
    \qquad \tau_\xi F(s)=F(s+\xi).
\]
As in the [two-by-three calculation](TwoByThreeTagCredit.md),
after dividing the score by \(Luv w'\) the term is
\(\sum_{d\mid m}\mu(d)g(\log d/L)+o(1)\).
It uses the true third divided difference, including when a shifted
argument is across .5; no taper is introduced. All ranks and
angles here have fixed positive floors. The original own logs may
be replaced in the weights at \(o(M)\) cost by the same true
rough receiver bound even for \(d=1\), and the physical prime/divisor
conditions themselves are not changed.

Use the actual compact weighted semiprime source, of ordinary
unopposed mass \((m_Z+o(1))|J|N/L\), with
\[
 m_Z=\int_{.003}^{.080}\frac{1-F(t)}{t(1-t)}\,dt,\qquad
 m_0=\int_{.003}^{.080}\frac{1-F(t)}t\,dt .
\]
The first uses the actual PNT in the true \(q\) slot with the
true prime \(p\) harmonic. The second is the same positive
\(p\)-harmonic without a PNT assertion on \(q\).

Divide each right tag angle into half-open .004 bins from .003,
shortening the last bin to end at .080. For each nondecreasing
triple of bins the true ordered volume is their width product
divided by the factorials of the repeated bins, as in the
three-by-three proof. For a \(d>1\) layer use a \(10^{-4}\)
bin in \(s=\log d/L\). Let \(\tau\) be the upper tag sum,
\(s_+\) the upper layer endpoint, and
\(D=.499-\tau-s_+\). When \(D>0\), open \(hd\) in
\(y=hdr\) and use genuine product BV of the full \(p q\)
source to linear-sieve \(r\) at the actual level \(N^D\).
All true moduli are \(hde\le N^{.499}\) in the reduced
class \(N\). Use the
[previous signed sub-root transfer](MediumSemiprimeAdverse.md#2-both-signs-in-the-ordinary-subroot-transfer),
including the same coefficients \(k(D),U(D)\), the real unit
mask \(N x h d\), and the exact ordinary even and odd divisor
densities \(e_a(s),o_a(s)\) at \(a=.080\). The inner sieve
divisor \(e\) does not test the named primes; right squares
with \(p>N^{.003}\) are physically discarded at a power
saving, as before. Distinct left and right labels cannot
share primes on the true unit rows, and their exclusions
affect a fixed-floor reciprocal model by \(1+o(1)\). The
weights \(uv w'\) cancel the three actual tag reciprocals.

Explicitly, write \(g_\pm=[\pm g]_+\). Per unit right-cell
volume, \(ds\), and \(M\), the non-atomic layer lower, when this
estimate is available, is the negative of
\[
    m_Z\{(Uo_a-ke_a)g_+ +(Ue_a-ko_a)g_-\},
\]
and its upper is
\(m_Z\{(Ue_a-ko_a)g_+ +(Uo_a-ke_a)g_-\}\).
These are two-sided true sieve estimates before subtraction
of opposite signs, not a signed independent quotient model.
The \(d=1\) atom has \(g(0)<0\) on every tag bin, as checked
outward, and uses \([m_Z U g(0),m_Z k g(0)]\)
at \(D=.499-\tau\).

## 2. A strengthened true affine upper for each layer

There is a second, positive estimate for every non-atomic
layer, including those beyond the sub-root transfer.
Fix the actual compatible labels \(p,h,d\). The equation
\(pq+hdr=N\) has \(q,r\) on one actual primitive affine
line, parametrized over an interval of length
\(|J|N/(phd)+O(1)\). Here \(q\) is a genuine prime, not
a rough integer represented as prime, and \(r\) is rough
at \(N^a\). The exact roots up to \(N^a\) are as in the
[previous affine tail](MediumSemiprimeAdverse.md#3-the-beyond-transfer-tail-is-an-actual-prime-opposite-upper):
one at primes dividing \(Nphd\), including two coincident
roots at a target prime off \(phd\), otherwise one slope
zero and its constant a unit at the named factors, and
two roots elsewhere. All \(p,h,d\) are ordinary target
units and \((p,hd)=1\). At 2 the root is single since \(N\)
is even.

Use an ordinary Selberg square with support exponent
\[
       D_2=\min\{\,4a,\ .499(1-.080-\tau-s_+)\,\}.
\]
Its real floor \(O(N^{2D_2}L^C)\) is power-small per
fiber: the available exponent is at least .180 and
\(2D_2\le .998(1-.080-\tau-s_+)\). A fixed divisor-power
sieve coefficient bound suffices for the floors; these
sum with the actual harmonic \(1/(phd)\). Unlike the earlier
tail, also sieve the \(q\) form alone at primes in
\((N^a,N^{D_2}]\) off \(Nphd\). The prime \(q\) itself exceeds
\(N^{.919}\) on the true central interval for large \(N\),
so no actual rows are lost. These additional primes give
one root and positive local denominator coefficient
\(1/(\ell-1)\).

For completeness write \(u_2=D_2/a\), \(\mathcal G(u)=
\int_0^u\rho_2(z)\,dz\), with the ordinary Dickman-2
denominator of the previous proof. The Selberg denominator
from squarefree sieve labels with every prime \(\le N^a\)
is \((1+o(1))\mathfrak S(N)^{-1} a^2 L^2\mathcal G(u_2)\);
the extra marked factors change it by \(1+o(1)\) since
they are polynomially large and bounded in number.
Keep also the positive denominator terms with **exactly
one prime** \(\ell>N^a\). At its scaled angle \(v\), the
remaining denominator is the same two-root one at scaled
level \(u_2-v\). More explicitly any fixed intervals
\([v_{i-1},v_i]\subset[1,u_2]\) add a normalized lower
\[
            \sum_i \mathcal G(u_2-v_i)(v_i-v_{i-1})/v_i .
\]
To see this, retain small-factor labels only up to
\(N^{a(u_2-v_i)}\) on that interval and use the actual
prime harmonic \(\sum1/(\ell-1)\sim\log(v_i/v_{i-1})\).
Omitting primes dividing \(Nphd\) makes a uniformly
vanishing harmonic error. The zero-length remaining
small level contributes zero to this lower. There is
no double count: the extra prime is the unique factor
of its denominator label above \(N^a\). In particular an
outward lower \(\mathcal G_*(u_2)\) for the sum of these
two positive denominator pieces gives an affine upper
\[
   (1+o(1))\frac{|J|N\mathfrak S(N)}{phdL^2}
                   \frac{1}{a^2\mathcal G_*(u_2)} .
\]
This estimate keeps the true prime on one affine form
and the true rough integer on the other. The proof
does not average over the target or assert an asymptotic
for the individual fibers.

When summing the affine bound, the actual \(p\)-weight
uses \(m_0\), since the prime \(q\) has already been paid
by the sieve. Put \(C_2=1/(a^2\mathcal G_*(u_2))\).
For the lower retain a debit \(m_0C_2(o_a g_++e_a g_-)\);
for the upper allow an addition
\(m_0C_2(e_a g_++o_a g_-)\). Both are per the same exact
right tag volume, \(ds\) and \(M\) as in §1. Each entire
fixed cell admits the better of the two genuine available
bounds for its lower and, independently, the better of
the two for its upper. This never counts any physical
term twice and keeps every right quotient rank.

## 3. Outward replay on every cell

Run:

    python3 -OB check_small_semiprime_three_tag.py

The verifier reuses the exact earlier third-difference and
ordinary signed-density setup. It uses the ordinary
\(10^{-4}\) ratio bins for \(e_a,o_a\) and the true outward
cubic profile range for every \(s\) bin. The ordinary
source masses use \(10^{-4}\) bins and the monotone sharp
\(F\) on the actual left interval. The cumulative
Dickman-2 lower uses the integer scale \(10^{13}\) and
the same outward recurrence already checked in the
[medium adverse comparison](MediumSemiprimeAdverse.md#4-exact-numerical-enclosure-on-the-entire-triangle).
For the extra denominator the arguments are rounded down
to that same \(10^{-4}\) grid, and each complete interval
of length \(1/80\) from 1 uses its **right** endpoint in
both factors of the positive lower integrand. Every sum
in the second bound is thereby rounded in the safe direction.

All 1540 triples of bins are included; in each, all
non-atomic profile layers through its actual .5 endpoint
are priced. The per-orientation ordered tag volume is
\(.077^3/6\). The two reflected sums have strict outward
enclosures \(-.228708M\) from below and \(-.009508M\)
from above (the reported lower-debit affine subtotal is
below \(.071792M\)). These are estimates of one full
literal adverse chamber. No sign of its complement
is inferred.
