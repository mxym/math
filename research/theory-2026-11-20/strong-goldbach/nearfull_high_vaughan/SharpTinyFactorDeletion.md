# The sharp near-full giant score: all tiny-factor quotients and the full terminal collar

Fix a nondegenerate compact central interval \(J\subset(0,1)\),
constants \(C_0>1,B_0>0\), and put
\[
 L=\log N,\qquad \ell=\log L,\qquad S=\exp(\ell^4),\qquad B=N/S.
\]
Use the **original sharp score** of
[the giant remainder](../giant_prime_divisor_remainder/Proof.md) and
[TinyMOriginalGiant.md](TinyMOriginalGiant.md). In particular
\(x,r\) are both genuine primes, \(x\in NJ\), \(y=N-x=rm\),
\(N/S^{C_0}\le r\le B\), \(T_y=y/B\), and
\[
 Q_y(m)=\sum_{\substack{d\mid m\\d<T_y}}\mu(d).
\]
Write \(\mathfrak S(N)=2\prod_{p>2}(1-(p-1)^{-2})
\prod_{p\mid N,\ p>2}(p-1)/(p-2)\).

**Theorem.** Fix \(1<\theta<4/3\) and \(0<\eta<4-3\theta\).
For even \(N\) with \(\operatorname{rad}(N)\le L^{B_0}\), the entire
part of the original sharp score on \(P^-(m)\le Z_0=\exp(\ell^\theta)\)
satisfies
\[
 \sum_{\substack{x+mr=N,\ x,r\ {\rm prime}\\
              x\in NJ,\ N/S^{C_0}\le r\le B\\P^-(m)\le Z_0}}
       (\log x)(\log r)Q_y(m)
       =O_{J,C_0,B_0,\theta,\eta}
                 \bigl(N\mathfrak S(N)\ell^{-\eta}\bigr).        \tag{1}
\]
One may intersect \(m\) with any real interval, with no loss in the
stated bound. In particular (1) applies to
\([S^{1+\delta},S^{1+2\delta}]\) for fixed \(\delta>0\) and retains its
original moving threshold. This is a signed deletion at the original
sharp cutoff, on all actual quotient ranks. The restriction
\(P^-(m)>Z_0\) left outside (1) includes genuine prime quotients and
also has actual locally nonrough quotients. There is no net sign
assertion on that remainder and no representation assertion.

**Terminal-collar theorem.** There are fixed \(C>0\) and
\(\delta_0>0\), depending at most on the fixed data above, such that
for every fixed \(0<\delta\le\delta_0\), the original sharp score
on the entire true terminal interval, without any rough predicate,
satisfies
\[
 \left|\sum_{\substack{x+mr=N,\ x,r\ {\rm prime}\\
                   x\in NJ,\ N/S^{1+\delta}\le r\le B}}
       (\log x)(\log r)Q_y(m)\right|
 \ll N\mathfrak S(N)\,\delta(1+\log(1/\delta))^C
                                   +o_\delta(N\mathfrak S(N)).
                                                               \tag{2}
\]
The implicit constant before the displayed \(\delta\)-factor is
uniform for fixed \(\delta\) followed by sufficiently large \(N\).
There is no averaging in the cutoff or target. In particular this
pays the original full collar to any prescribed fixed relative
tolerance by making \(\delta\) small first, including all prime
and composite quotients there. It does not give a signed comparison
at the \(\delta\)-scale or control the remaining larger \(m\)'s.
The argument also applies directly to the matched annulus
\(S^{1+\delta}\le m\le S^{1+2\delta}\) in the original range, with
the same displayed type of bound; see §4.

For large \(N\) suppress the target nonunit exceptions at a power
saving, as in TinyMOriginalGiant: an actual prime \(r\mid N\) forces
\(x=r\), and all central target-dividing \(x\) have only divisor-many
assignments. One may assume \((xrm,N)=1\). In the model put
\[
                c(m)=\prod_{\substack{p\mid m\\p>2}}
                                    \left(1+\frac1{p-2}\right).
\]
Here \(T_y\asymp_J S\), \(m\ge T_y\) by the *literal* upper bound on
\(r\), and \(m\ll_J S^{C_0}\). At fixed \(y\) the two giant cutoffs
and any extra interval in \(m\) impose just one interval
\[
                    T_y\le m\le yS^{C_0}/N
\]
intersected with that extra interval.

## 1. An adaptive palette and the exact covered main

Take a fixed \(R>40\). Divide all the prime logarithms above
\(\ell^\theta\) up through \(C_0\ell^4\) into consecutive geometric
cells
\[
 \mathcal C_j=\{p:e^{u_j}<p\le e^{Ru_j}\},\qquad
 u_j=R^j\ell^\theta.
\]
Use the whole last cell, even if its upper edge passes the physical
bound on \(m\). There are \(B_1=O(\log\ell)\) cells. Their reciprocal
prime masses are bounded above and below by positive constants
depending only on \(R\), by the prime reciprocal theorem, uniformly
as the bottom endpoint tends to infinity. Every such prime is a
target unit and is below the usual
\(Z=\exp(L^{.24})\) source roughness. For fixed \(K\), call the part
of \(m\) above \(Z_0\) **covered** when it occupies at least \(2K\)
cells. Then it occupies \(K\) cells with consecutive selected indices
differing by at least two. Choose the lexicographically first such
\(K\)-tuple, based only on which cells are occupied. Thus there are
at most \(B_1^K\) packets.

Here is the uniform version of the input being used. In the
[geometric rescaling](TrueCompositeQuotientCredit.md) of the
[tiny tag comparison](TinyTagProjection.md), each packet uses these
\(K\) cells as its colors. The lower endpoint \(u_s\) of the \(s\)-th
chosen color has
\[
 \sum_{\nu<s} Ru_\nu\le \frac{R}{R^2-1}u_s<u_s/10,\qquad
             \ell^\theta\le u_s\ll_{R,C_0}\ell^4.                \tag{3}
\]
One need not hold \(u_s/\ell^4\) fixed. Indeed the bound for the
lower-color choices in
[Jiang–Lau–Lü v2, equation (5.11) and §§5–6](https://arxiv.org/html/2611.12467v2)
in the proof-scale substitutions of the two cited notes is
\(\log|\mathcal N_s|\le K\log m_0+\sum_{\nu<s}Ru_\nu
 \le (.1+o(1))u_s\), with \(m_0=1+\lfloor L^{.01}\rfloor\),
and the local tolerance is \(100e^{-u_s}\). Lower-scale errors from
separation, repeats, and the real determinant minor are therefore
arbitrarily small in \(L^{-1}\), uniformly in the cell choices.
The tiny-tag rescaling, not the printed lower bound on \(\log Y\)
in Lemma 6.11, is used: the large-sieve part in its zero-memory
block is bounded by \(O(L^{-A}+Y^{-\sigma})\) with the same arc
denominator window, possible here because \(\log Y\gg\ell^\theta\).
The upper-scale geometry and frame budgets have
\(\log H=O_{K,R,C_0}(m_0\ell^4)=o(\sqrt L)\), and the
full-target character-moment index satisfies
\(j=O(L/\ell^\theta)\), \(j\log j+j\log L=o(L)\).
The term \(B_*m_0^{-K}\) in the nonzero-memory bound is unchanged.
The normalization of colors uses their uniform reciprocal bounds
rather than their exact widths. These are exactly the lower and upper
scale checks in TinyTagProjection and the geometric rescaling; their
estimates apply uniformly here with \(K\) fixed sufficiently large
after the required log saving and the separation precisions. The
\(B_1^K\) packets and tag shells cost only fixed log powers.

Put \(m=v n\), where \(v\) is the whole part supported on
\(p\le Z_0\), with all its powers, and \(P^-(n)>Z_0\).
The mask in (1) is \(v>1\). For each covered packet extract one
actual prime per chosen cell into \(w\mid n\), writing \(m=w m'\).
Remove actual squared tag primes first. The reciprocal hit
allocation is \(\prod_{\mathcal C}(1+\omega_{\mathcal C}(m'))^{-1}\).
The occupied cells in \(m\) after extraction can be recovered as the
union of the occupied cells of \(m'\) and the known selected cell
indices. Consequently the first-choice predicate, even for
overlapping candidate packets, is a literal predicate on \(m'\)
within this packet, independent of the values of the extracted
primes. The same is true of \(v>1\). A restored incompatible row
still has \(w\mid m\mid y\) and an actual \(p^2\mid y\) with \(p>Z_0\).
Their count is \(O(N/Z_0)\) by summing actual multiples, and crossed
divisor moments make the weighted error arbitrarily log-small.
There is no hidden selected-prime gcd in the separated coefficient.

For clarity write the covered main, including its actual units, as
\[
 \mathcal M_{\rm cov}=
 \mathfrak S(N)\int_{NJ}
    \sum_{\substack{T_y\le m\le yS^{C_0}/N,\ (m,N)=1\\
          v>1,\ m\ {\rm covered}}}
           \frac{c(m)Q_y(m)}{m}\,dx,\qquad y=N-x.              \tag{4}
\]
Any extra interval in \(m\) is understood in (4). The true covered
score is (4) with \(O_D(NL^{-D})\) error. To verify this, use the
original sharp Vaughan split in TinyMOriginalGiant, with
\(N^{.10},N^{.10}\) cutoffs on the genuine \(x\) leg and \(Z\)-rough
factors. For Type II the literal tag-residual divisor expansion is
\[
 Q_T(wm')=\sum_{s\mid w}\mu(s)
                      \sum_{\substack{d\mid m'\\ds<T}}\mu(d).
\]
It holds before the restoration and imposes no tag-dependent mask
after it. If a selected prime is above \(T\), the terms including
that prime in \(s\) simply cannot pass the original gate. As in the
cited proof, freeze the moving thresholds in log-fine \(y\) cells
and use individual prime Mellin factors for the smoothed
\(wm'\)-window and \(ds<T\). This is a temporary approximation, not
a change to the sharp score. A moved boundary in \(y=mr_0\) or
\(y=Bd\) is paid by the actual corresponding divisor \(m\mid y\)
or \(d\mid y\). Over \(m\ll S^{C_0}\) and \(d\ll S\), the raw
crossing count at relative precision \(L^{-G}\) is
\(O(NL^{-G}\log S+S^{O(1)})\) per fixed endpoint. The separate
relative smoothing collars in the fixed divisor thresholds are paid
by the same actual-multiple bound; all these thresholds have size
\(\gg S\). Divisor moments and the fixed log-power mesh give the
stated saving. On each shell \(w\asymp Y\), the residual factor is
the actual \(m'r\), with \(\log r\), the real quotient masks and a
fixed divisor-power coefficient, of squared norm
\(O((N/Y)L^{O(1)})\). The uniform comparison from (3) and the same
[full small-radical character major](../small_radical_projection/Proof.md)
give the arbitrary-log Type II estimate.

For Type I, hold the actual \(m\) fixed and use true prime \(r\)
Bombieri–Vinogradov at \(N/m=N^{1-o(1)}\) in the actual class
\(N\bar m\bmod q\) with \(q=afe\le N^{.20+o(1)}\).
The two terms and the exact local Euler derivative are those in
[TrueCompositeQuotientCredit.md, §2](TrueCompositeQuotientCredit.md).
Its fixed-\(m\) argument applies to each opened \(d\mid m\):
\(d<T_y\) is a real interval endpoint in \(x\), and the outer
\(v\), coverage, and interval masks involve only \(m\). The actual
roughness factor is
\(\prod_{p\le Z,\ p\nmid mN}(1-1/(p-1))\), which multiplies the
same derivative \(G_Z(1)\) and gives \(\mathfrak S(N)c(m)\);
the other \(a\)-harmonic vanishes. All factors of \(mN\) are below
\(Z\). Keep the strict endpoints in the BV maximal prefixes.
The BV errors sum over true \(m\) with weight \(O(\tau(m)/m)\);
\(\sum_{m\ll S^{C_0}}\tau(m)/m\ll(\log S)^2\). Thus this
calibration has not assumed any model for actual \(m\) with small
factors, and yields (4) as stated.

## 2. Absolute estimate for every missed quotient with \(v>1\)

The necessary witness on such rows is elementary. Since \((v,n)=1\),
\[
 Q_y(vn)=\sum_{d\mid n}\mu(d)
                       \sum_{\substack{b\mid v\\b<T_y/d}}\mu(b).
\]
For \(v>1\) the inner sum is zero if \(d<T_y/v\), by the complete
Möbius sum of \(v\), and also if \(d\ge T_y\), since it is empty.
Equality at the lower end has not been dropped. Thus, with fixed
\(0<c_1<C_1\) such that \(c_1S\le T_y\le C_1S\),
\[
       \sup_{y}|Q_y(vn)|
       \le \tau(v)
         \sum_{\substack{d\mid n\\c_1 S/v\le d<C_1S}}\mu^2(d).
                                                                  \tag{5}
\]
Every missed \(n\) is supported on fewer than \(2K\) cells.
There are \(O((1+\log\ell)^{2K})\) choices for these cell sets,
and the sum of reciprocal primes in any one possible set is
\(O_{K,R}(1)\). Overcount by summing over cell sets; no equality
of these sums or independence of actual prime conditions is needed.

All \(n\) with some \(p^2\mid n\) can be dropped as in §1 in the
true score. The same deletion costs \(O_D(L^{-D})\) in its harmonic
model: split \(m\) into \(O(\log S)\) dyads, use the actual multiples
\(p^2\mid m\) with \(p>Z_0\) and ordinary divisor moments in each
dyad. Also \(c(n)=1+o(1)\) uniformly, since
\(\omega(n)\le O_{C_0}(\log S/\log Z_0)\).
The needed smooth-part harmonic is
\[
 \sum_{P^+(v)\le Z_0}
               \frac{\tau(v)c(v)(1+\log v)}v
        \ll (\log Z_0)^3.                                      \tag{6}
\]
The Euler factor without \(1+\log v\) is \(1+2/p+O(p^{-2})\);
a logarithmic derivative costs \(O(1+\sum_{p\le Z_0}\log p/p)\).
In addition \(v>S^{.1}\) can be removed with an error smaller
than any power of \(\ell^{-1}\), even before using the witness.
Use Rankin with exponent \(1/\log Z_0\) in (6) without the log,
and \(|Q_T(vn)|\le\tau(v)\tau(n)\). The tilted Euler product is
\(O((\log Z_0)^{O(1)})\), since \(p^{1/\log Z_0}\le e\);
the factor \(\exp(-.1\log S/\log Z_0)\) absorbs this, all cell
choices, and \(\sum_{n}\tau(n)/n=O_{K,R}(1)\) within each set.

Let \(k_0=\lceil\log\ell\rceil\). Within each fixed set of cells,
the squarefree \(n\)'s with \(\omega(n)>k_0\) have
\(\tau(n)/n\)-sum at most
\(\sum_{k>k_0}(C_{K,R})^k/k!\), smaller than every fixed inverse
power of \(\ell\). Again this pays even after (6) and the choice
count. For \(\omega(n)\le k_0\) and \(v\le S^{.1}\), any witness
\(d\) in (5) has a prime factor \(p\) with
\(\log p\ge .8\log S/k_0\), for large \(N\). Open
\(n=p n_0,\ d=p d_0,\ d_0\mid n_0\), and upper bound by summing
every possible such \(p\). For fixed \(v,n_0,d_0\), its allowed
interval is contained in
\[
 [c_1S/(v d_0),\, C_1 S/d_0]\cap
                       [\exp(.8\log S/k_0),\,S^{C_0}],
\]
of logarithmic length \(O_J(1+\log v)\).
The prime reciprocal sum is at most
\(O_J((1+\log v)k_0/\log S)\): split into fixed-ratio dyads and
use Chebyshev's upper bound, including the endpoint dyad. This
does not use a uniform prime asymptotic in short intervals.
The remaining sum \(\sum_{n_0}\tau(n_0)/n_0\) per cell set is a
bounded Euler product. Using (6), the entire missed absolute
harmonic is
\[
 \sum_{\substack{m\ \text{in the physical range}\\
           v>1,\ m\ {\rm missed}}}
        \frac{c(m)}m\sup_y |Q_y(m)|
 \ll_{J,C_0,K,R,\theta}
 \frac{(1+\log\ell)^{2K+1}(\log Z_0)^3}{\log S}
             +O_A(\ell^{-A})
 \ll \ell^{-\eta}.                                           \tag{7}
\]
A marked witness can be counted several times; (7) is an upper,
not a one-to-one parametrization.

For the same absolute bound on the true missed score, at each
stated \(m\) apply the true two-affine-prime upper sieve of
[TinyMWholeWindows.md, §2](TinyMWholeWindows.md) to \(r,N-mr\)
over the full central range. Its log-weighted upper is
\(O_J(N\mathfrak S(N)c(m)/m)\), uniformly for
\(m\ll S^{C_0}\), which lies in its valid range. Bound the sharp
score by (5) on these actual rows. The discarded squared \(n\)
and target nonunits have already been separately accounted for.
Therefore (7) pays both the true missed score and the missed
part of the model in (4).

## 3. Full signed harmonic with the actual \(v>1\) mask

For fixed \(y\), the full \(v>1\) model before applying the
covered/missed distinction is arbitrarily log-small. We give the
exact version with the factor \(c(m)\). Write
\[
 c(m)=\sum_{b\mid m}f(b),\qquad
 f(p)=1/(p-2)\ (p>2),\quad f(2)=0,
\]
where \(f\) is nonnegative multiplicative supported on squarefree
integers, with \(f(1)=1\). The part \(b>S^{.1}\) is power-small in
\(S\): on an \(m\)-dyad the actual multiples of \([b,d]\) cost
\(O(1/[b,d])\) in the reciprocal harmonic, and
\(\sum_{d<T_y}\mu^2(d)/[b,d]\le \tau(b)(1+\log T_y)/b\).
There are \(O(\log S)\) dyads and
\(\sum_b f(b)\tau(b)/\sqrt b<\infty\).

For \(b\le S^{.1}\) with \((b,N)=1\), set \(m=bu\) and expand
\[
 Q_y(bu)=\sum_{s\mid b}\mu(s)
              \sum_{\substack{d\mid u,\ (d,b)=1\\d<T_y/s}}\mu(d).
                                                               \tag{8}
\]
This identity holds even when \((b,u)>1\), by allocating the
squarefree \(d\)-label's primes dividing \(b\) to \(s\).
If \(b\) contains a prime \(\le Z_0\), the \(v>1\) condition is
already fulfilled. Otherwise it is the difference of the
unrestricted sum and the sum with \(P^-(u)>Z_0\). Thus in each
term the \(u\)-mask is exactly coprimality to the prime factors
of \(N\) and optionally all primes \(\le Z_0\). Call this set of
excluded primes \(\mathcal P\); the additional exclusion of
primes dividing \(b\) applies only to the inner variable \(d\).

For either formal exclusion set \(\mathcal P\) or
\(\mathcal P\cup\{p:p\mid b\}\), and
\(\sigma=1-c/\log Z_0\) with a fixed small \(c>0\), the two
products \(\prod_p(1+p^{-\sigma})\) and
\(\prod_p(1-p^{-\sigma})^{-1}\) over the exclusion set are
\(\ell^{O(1)}\). Indeed at \(p\le Z_0\) this is prime Mertens
with \(p^{1-\sigma}=O(1)\), and the target and \(b\) together
have at most \(O(L)\) prime factors larger than \(Z_0\).
The latter contribute \(o(1)\) in the prime reciprocal
exponent. The inverse-mask convolution of \(\mu\), split at
the square root of the variable endpoint, now yields the
uniform estimate
\[
 \sum_{\substack{d\le X\\d\ \text{avoids the exclusion set}}}
                    \frac{\mu(d)}d=O_D(L^{-D})
              \qquad (X\gg S^{.3}).                            \tag{9}
\]
The ordinary Mertens error on the lower tail of the convolution
is arbitrarily log-small at a fixed power of \(S\); its upper
tail is bounded by \(X^{-(1-\sigma)/2}\ell^{O(1)}\).
The usual finite prime-exclusion floor estimate, expanding the
actual integer divisibility labels, is
\(O(Y^\sigma\prod(1+p^{-\sigma}))\) on a real interval of
scale \(Y\); after partial summation it has the corresponding
relative saving for reciprocal harmonics.

Finally open \(u=dn\) in (8). Its dyadic \(u\)-intervals have
scale \(\gg S^{.9}\), and \(T_y/s\gg S^{.9}\) uniformly.
For \(d>S^{.3}\) fix \(n\) and use (9) on the actual \(d\)
interval with its own \(b\)-mask and strict endpoint, then sum
\(1/n\). For \(d\le S^{.3}\), count the true coprime \(n\) in
the actual interval with scale at least a fixed multiple of
\(S^{.6}\). The density relative to \(\mathcal P\) is independent
of \(d\) and the reciprocal interval has endpoints both scaled
by \(1/d\), so after this count the remaining signed \(d\)-prefix
cancels by (9). Its \(b\)-mask is still present; no \(b\)-mask
was inserted in the \(n\) count. The model error is arbitrary
log-small on both pieces after summing the logarithmic factors,
\(O(\log S)\) outer dyads, and \(\sum_b f(b)\tau(b)/b<\infty\).
This includes real intervals and strict thresholds by integer
parts. The whole sum in (4), without coverage, is consequently
\(O_D(L^{-D})\) per real \(y\), uniformly.

Subtract the missed harmonic estimated in (7) from this full
model and add the true missed score using the same bound.
Equation (4) now proves (1). The proof retains both actual
primes on the left hand side and only uses integer models after
their stated comparison or the positive two-prime upper bound.

## 4. Every quotient in the original sharp terminal collar

Use the exactly same palette, with \(K\) chosen once for a fixed
arbitrary-log error, independently of \(\delta\). For example
one may choose \(\delta_0<\min((C_0-1)/3,.05)\).
Replace the lower cutoff of the true \(r\)-interval by
\(N/S^{1+\delta}\). Then the true \(m\)-interval at fixed real \(y\)
lies in \([T_y,S^{1+\delta}]\). The analysis in §1 applies **without**
the \(v>1\) mask: that mask was simply a residual predicate.
The calibration and boundary estimates are uniform over changing the
real interval endpoints in the stated range. The full model with no
\(v\) predicate is arbitrary-log small by the unrestricted version of
§3. The true and model missed parts with \(v>1\) are \(o(N\mathfrak
S(N))\) by §2, even without the extra terminal cut. All repeated prime
factors above \(Z_0\) are still negligible. It remains to bound the
absolute model on squarefree missed \(m\) with \(P^-(m)>Z_0\);
the actual affine prime-pair upper then gives the same bound for
the original score.

First take \(P^-(m)>S^{2\delta}\). For all sufficiently large \(N\)
after \(\delta\), every proper divisor is at most
\(S^{1-\delta}<T_y\), and \(m\ge T_y\), so \(Q_y(m)=-\mu(m)\).
The possible prime factors lie in \(O_R(1+\log(1/\delta))\)
cells of the palette. A missed support is confined to a set of
fewer than \(2K\) of these cells. Fix such a set; its total prime
reciprocal mass is \(O_{K,R}(1)\).
Mark any largest factor \(p\) of \(m=p n\). At fixed \(n\) the
prime has \(\log p\gg\log S/(\omega(n)+1)\) and lies in the
interval \([c_1 S/n,S^{1+\delta}/n]\) of logarithmic length at
most \(\delta\log S+O_J(1)\). By the same dyadic Chebyshev
bound as in §2 its reciprocal mass is
\[
                   O_J((\omega(n)+1)(\delta+1/\log S)).
\]
After opening \(n\) over the chosen cell set the
\((\omega(n)+1)/n\) harmonic is bounded uniformly by its finite
prime-reciprocal Euler product and one derivative. Therefore the
entire absolute reciprocal sum of this part (including \(c(m)\))
is
\[
 O_{J,K,R}\!\left(\delta(1+\log(1/\delta))^{2K}\right)+o_\delta(1).
                                                               \tag{10}
\]

For the complementary \(Z_0<P^-(m)\le S^{2\delta}\), mark the
actual least factor \(p\), in its cell \(j\). Since \(m=p n\) is
squarefree, the sharp divisor pairing is exactly
\[
                 Q_y(pn)
              =\sum_{\substack{d\mid n\\T_y/p\le d<T_y}}\mu(d).
                                                               \tag{11}
\]
This estimates the entire complementary branch, not just the
locally nonrough rows; in particular it includes any \(p\) above
the actual \(m/T_y\) but below \(S^{2\delta}\). Write
\(a_j=Ru_j/\log S\) for the upper exponent of cell \(j\).
If this cell can contain the marked \(p\), then
\(a_j\le 2R\delta\). Every other occupied cell has index at least
\(j\). The number of possible sets of fewer than \(2K\) cells
at or above \(j\), through the end of the palette, is at most
\[
 O_{K,R,C_0}\bigl((1+\log^+(1/a_j))^{2K}\bigr).
\]
Fix one such set, and bound all squarefree supports confined
to it.

In (11) fix \(p\) and mark one largest prime \(q\) of the actual
witness \(d\), writing \(n=q n_0,\ d=q d_0\), \(d_0\mid n_0\).
A witness satisfies \(d\ge c_1 S/p\), so for the stated
\(\delta_0\) and all sufficiently large \(N\),
\(\log q\gg \log S/(\omega(n_0)+1)\). At fixed \(p,n_0,d_0\)
the prime \(q\) is in \([c_1 S/(p d_0),C_1 S/d_0]\), of
logarithmic length \(O_J(1+\log p)\). Its reciprocal mass is at
most
\(O_J((\omega(n_0)+1)(1+\log p)/\log S)\).
The remaining \(\tau(n_0)(\omega(n_0)+1)/n_0\) harmonic within
the chosen cells is a bounded Euler product and derivative, and
the reciprocal mass of \(p\) in its cell is bounded independently
of \(j\). Since \((1+\log p)/\log S\ll a_j\), the bound per cell
\(j\) and per set is \(O_{J,K,R}(a_j)\).
The exponents \(a_j\) form a geometric progression with ratio
\(R\). Summing downward from \(2R\delta\) gives
\[
 \sum_{a_j\le2R\delta}a_j(1+\log^+(1/a_j))^{2K}
             \ll_{K,R}\delta(1+\log(1/\delta))^{2K},             \tag{12}
\]
as follows by summing \(R^{-i}(1+i)^{2K}\).
We did not need to restrict \(\omega(n_0)\), assume independent
prime assignments, or replace the physical score by \(-\mu\) in
this branch. Overcounting marked witnesses is permitted because
(11) was bounded absolutely. The original moving \(T_y\) is
handled by its fixed comparison endpoints \(c_1S,C_1S\) only in
this upper, not in the score itself.

Equations (10) and (12), the fixed-\(m\) true affine upper, and
the comparisons preceding them prove (2) with \(C=2K\).
For the stated matched annulus use \(m\in[S^{1+\delta},S^{1+2\delta}]\).
Its harmonic window again has length \(\delta\log S+O_J(1)\),
and use the separating cut \(P^-(m)>S^{4\delta}\) instead of
\(S^{2\delta}\) in the estimate for the first branch. All
proper divisors are then \(<S^{1-2\delta}<T_y\).
In the other branch \(a_j\le4R\delta\) and
\(\log d\ge(1-4\delta)\log S+O_J(1)\), so the paired-divisor
argument and geometric sum are unchanged. Thus intermediate
prime factors below the coarse roughness threshold are paid as
well. This is an original sharp-cutoff statement, unlike an
average in the cutoff, and a larger cohort than
[RoughQuotientWholeAnnulus.md](RoughQuotientWholeAnnulus.md).
Those cohorts must not be added to this one.
