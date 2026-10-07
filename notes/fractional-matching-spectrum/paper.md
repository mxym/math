# The complete bounded-packing fractional matching spectrum

Research continuation, 7 October 2026. We extend the sharp intersecting
fractional-cover curve to arbitrary hypergraphs with a bounded matching
number. The result gives an exact limiting spectrum for every fixed
matching bound, an explicit finite error, a finite formula for the
spectrum, and its limit when the matching number diverges. All cover
values are fractional unless explicitly stated otherwise.

## 1. Definitions and statements

A hypergraph here is a finite simple family of nonempty finite sets.
Its rank is at most an integer \(r\ge2\); its edge count is m. Its
matching number \(\nu(H)\) is the largest number of pairwise disjoint
edges. Its fractional vertex-cover number \(\tau^*(H)\) is the
minimum sum of nonnegative vertex weights with sum at least one on
an edge. Finite LP duality identifies this with the maximum
\(Y=\sum_E y_E\) under
\[
             y_E\ge0,\qquad \sum_{E\ni v}y_E\le1.           \tag{1}
\]
The complete finite separation argument is given in Appendix A of
[F]. Empty families have both numbers zero and are allowed below.

Recall the continuous nondecreasing function
\[
 \psi(x)=x/2\quad(0\le x\le1),\qquad
 \psi(x)=\max\{a/(a+1),x/(a+2)\}
            \quad(a\le x\le a+1,\ a=1,2,\ldots).           \tag{2}
\]
It is the sharp intersecting fractional frontier proved in [F].
For an integer \(s\ge1\), define
\[
 \boxed{\displaystyle
 \Psi_s(c)=\max\left\{\sum_{i=1}^s\psi(c_i):
              c_i\ge0,\ \sum_{i=1}^sc_i=c\right\}.}        \tag{3}
\]
This is an attained maximum on a compact simplex. For \(s=1\), it
is exactly \(\psi\).

**Theorem 1 (finite and sharp bounded-packing law).** Every H with
\(\nu(H)\le s\) satisfies
\[
                  \tau^*(H)\le r\Psi_s(m/r)+s/2.           \tag{4}
\]
If s is fixed, \(r_j\to\infty\), \(\nu(H_j)\le s\), and
\(m_j/r_j\to c<\infty\), then
\[
                  \limsup_j\tau^*(H_j)/r_j\le\Psi_s(c).    \tag{5}
\]
For every real \(c\ge0\), a sequence of simple uniform hypergraphs
of ranks tending to infinity attains equality in this limit and
has matching number **exactly s**. The result imposes no partite,
regularity, linearity or intersection-size assumption.

Here and below fixed-matching sharpness is an asymptotic statement,
not an assertion that (4) is the best bound for every finite (r,m,s).

**Theorem 2 (finite closed formula).** Put \(c=Q+\theta\), where
\(Q=\lfloor c\rfloor\) and \(0\le\theta<1\). For \(s\ge2\) set
\(u=s-1\). For integers \(0\le a\le Q\), write
\(Q-a=ub+t\), with \(0\le t<u\). Then
\[
 \boxed{\displaystyle
 \Psi_s(c)=\max_{0\le a\le Q}
 \left\{\psi(a+\theta)
       +(u-t)\frac{b}{b+1}+t\frac{b+1}{b+2}\right\}.}      \tag{6}
\]
In particular, \(\Psi_2(3)=7/6\), \(\Psi_2(7/2)=7/6\), and
\(\Psi_2(15/4)=5/4\). This formula involves a finite list, not a
numerical optimization or an unverified solver assumption.

Define h by linear interpolation of its nonnegative integer values
\(h(a)=a/(a+1)\). Thus
\[
 h(x)=\frac{a}{a+1}+
       \frac{x-a}{(a+1)(a+2)}\quad(a\le x\le a+1).          \tag{7}
\]

**Theorem 3 (arbitrary and diverging matching numbers).** For every
nonempty H, putting \(s=\nu(H)\),
\[
 \frac{\tau^*(H)}{r s}\le h\!\left(\frac{m}{r s}\right)
                                      +\frac1{2r}.         \tag{8}
\]
For all fixed \(c\ge0\),
\[
            h(c)-\frac1{2s}\le\frac{\Psi_s(sc)}s\le h(c).   \tag{9}
\]
Consequently when \(r_j\to\infty\), \(\nu(H_j)\to\infty\), and
\(m_j/(r_j\nu(H_j))\to c<\infty\), the sharp upper limit of
\(\tau^*(H_j)/(r_j\nu(H_j))\) is h(c). Uniform families attain
this for any prescribed integer sequences of ranks and matching
numbers tending to infinity.

## 2. The anchored finite inequality

The key point is that the earlier signed-bin proof does not require
all pairs of edges in a group to intersect. It only requires an edge
of maximum weight that meets every edge of that group.

**Lemma 4 (anchored bound).** Let G have \(t\ge1\) edges of rank at most r,
and let y be a vector satisfying (1) on G. Suppose \(P\in G\),
every other edge meets P, and \(b=y_P\ge y_E\) for all E in G.
Then, for every integer \(k\ge2\),
\[
 \sum_{E\in G}y_E\le
       \max\{((k-1)r+1)/k,t/(k+1)\}.                      \tag{10}
\]
If \(t\ge2\), the same sum is at most t/2. If \(t=1\) it is at most one.
In all cases,
\[
              \sum_{E\in G}y_E\le r\psi(t/r)+1/2.          \tag{11}
\]

**Proof.** Write \(Y_G=\sum_{E\in G}y_E\). The nonnegative incidence
count on P gives \(Y_G\le r-(r-1)b\). If \(b\le1/(k+1)\), use
\(Y_G\le tb\); if \(b>1/k\), use that star bound. Both give (10).
In the remaining interval \(1/(k+1)<b\le1/k\), assign every other
edge to exactly one of its intersection vertices with P. A bin of
\(\ell\) edges has total W with \(W\le\ell b\) and \(W\le1-b\). Put
\(B=1-kb\ge0\) and \(p=(k+1)b-1>0\). For \(\ell\le k-1\),
\[
          W-B\ell\le\ell p\le(k-1)p;
\]
for \(\ell\ge k\),
\[
          W-B\ell\le1-b-kB=(k-1)p.
\]
Sum only over this genuine partition. Total mass is \(Y_G-b\)
and total count is t-1, so, with \(g=(k-1)r+1\),
\[
            Y_G\le t-g+b\{(k+1)g-kt\}.
\]
This is affine in b, taking the values t/(k+1) and g/k at the two
reciprocal endpoints. This proves (10), without any assumption
about intersections between non-anchor edges.

For the half bound, every other edge satisfies \(y_E+b\le1\).
If \(b\le1/2\), use \(Y_G\le tb\le t/2\). Otherwise
\[
          Y_G\le b+(t-1)(1-b)
                    =t-1-(t-2)b\le t/2\quad(t\ge2).
\]
For \(t=1\), nonemptiness of P gives \(b\le1\).
If \(t\ge2\) and \(t/r\le1\), this half bound is exactly \(r\psi(t/r)\).
If \(t/r\ge1\), choose an integer a>=1 with \(a\le t/r\le a+1\)
and apply (10) with k=a+1. Its first term differs from
\(r a/(a+1)\) by \(1/k\le1/2\), proving (11). For \(t=1\),
\(r\psi(1/r)+1/2=1\); this also verifies (11).

## 3. Greedy partition and the finite law

Fix any feasible y on H. Among the remaining edges choose one of
maximum weight, P_1, and let G_1 consist of every remaining edge
meeting P_1, including P_1 itself. Remove G_1. Repeat until no edge
remains. At every step the selected edge meets all edges of its group
and has maximum weight there. Its group's restricted vector is feasible.

All selected anchors are pairwise disjoint: a later selected edge
was not removed as a neighbor of an earlier anchor. Hence the number
l of groups is at most \(\nu(H)\le s\). Their edge sets partition H;
write \(t_i=|G_i|\), and pad the list to s groups with empty groups.
Applying (11) to each nonempty group gives
\[
 Y\le r\sum_{i=1}^s\psi(t_i/r)+l/2
       \le r\Psi_s(m/r)+s/2.
\]
The exact partition identity \(\sum_i t_i=m\) is what permits (3).
This holds for every feasible vector, proving (4) by finite duality.
Empty families cause no difficulty. The universal additive constant s/2
cannot be reduced: s disjoint r-edges have \(m=s\), \(\tau^*=s\),
and \(\Psi_s(s/r)=s/(2r)\), so (4) holds with exact equality.

Both psi and \(\Psi_s\) are nondecreasing and 1/2-Lipschitz.
For psi, this follows from its piecewise slopes, all between zero
and 1/2. For \(\Psi_s\), increasing total mass by delta can only
increase the maximum: add delta to a coordinate of a maximizing
allocation. Conversely trim delta from coordinates of any allocation
at the larger total mass; the sum changes by at most delta/2.
Taking the maximum proves the Lipschitz bound. Dividing (4) by r
and passing to the limit now proves (5).

## 4. Sharpness with a common rank

One must not silently combine unrelated rank subsequences. We prove
the following common-rank construction explicitly.

**Lemma 5.** For every fixed \(x\ge0\) and every sufficiently large integer
R, there is a simple intersecting R-uniform family \(H_R(x)\) with
\[
            |H_R(x)|/R\to x,\qquad
            \tau^*(H_R(x))/R\to\psi(x).                   \tag{12}
\]
For fixed positive integer x=a this uses only Wilson's named design
existence theorem, not Kahn's covering corollary.

**Proof.** We use the exact constructions of [F], whose two published
inputs are restated here. Wilson's theorem provides a Steiner
2-(v,k,1) design for every sufficiently large admissible v with fixed
k, subject to \(k-1\mid v-1\) and \(k(k-1)\mid v(v-1)\).
In particular choose \(v=1+k(k-1)N\); replication is \(r_0=kN\).
Its incidence dual has fractional value v/k, certified by uniform
old-edge weights 1/k and old-vertex weights \(1/r_0\). Kahn's 1994
Corollary 5.4 states that an intersecting \(r_0\)-uniform family with
at most \(Cr_0\) edges, C fixed, and maximum pair intersection
\(o(r_0)\) has an integer cover of size
\((C/(C+1)+o(1))r_0\). Here take C=k: the dual is linear and
\(v=(k-1)r_0+1\le kr_0\), so a cover \(C_0\) smaller than \(r_0\) exists.
There are \(vr_0/k=\Theta(r_0^2)\) old vertices. Enlarge \(C_0\) to a
set T of \(r_0\)-1 old vertices and add edges \(T\cup\{p\}\) for distinct
old p outside T, skipping original edges. There are \(\Theta(r_0^2)\)
candidates and only \(O(r_0)\) forbidden originals, so any requested
\(O(r_0)\) additions are possible. Every added edge meets the originals
through \(C_0\) and other new edges through T. The old dual weights
extended by zero and the old primal weights \(1/r_0\) still agree at
v/k. This proves the plateau extension explicitly.

If x lies on the plateau in [a,a+1], take k=a+1,
\(N=\lfloor R/k\rfloor\), and \(r_0=R-O(1)\). Add
\(\max\{0,\lfloor xR\rfloor-v\}\) plateau edges. Privately pad all
edges from rank \(r_0\) to R. Put zero primal weight on every padding
vertex. The old primal/dual certificates still agree at v/k, while
the edge count divided by R tends to x. For x=a, only O(1) additional
edges could be requested, and taking no additional edges instead
still yields (12); thus Kahn is unnecessary at integer x.

If x>0 lies on a ramp, choose its block size k=a+2, or k=2 below
one. Choose the largest admissible
\(v=1+k(k-1)N\le xR\). Then \(v=xR+O(1)\), and its replication
\(r_0=(v-1)/(k-1)\le R\) because \(x\le k-1\). Pad every edge privately
to R. The same exact certificates give value v/k and (12).
At a switch either construction works. For x=0 take one R-edge.
This completes the common-rank lemma. The prime-power alternatives in [F] give additional explicit
subsequences; they are not used to assert construction at every
large integer R.

Choose a maximizing allocation \((c_1,\ldots,c_s)\) in (3). For each
large R take the disjoint union of the s families \(H_R(c_i)\), on
disjoint vertex sets. It is simple and R-uniform. Each component is
nonempty and intersecting, so its matching number is one; the union
has matching number exactly s. Fractional cover is additive across
disjoint components, by summing separate feasible primal and dual
certificates. Formula (12) then attains (5). This proves Theorem 1.

## 5. Reduction to a finite formula

On each integer unit interval psi is convex: it is the maximum of a
constant and an affine function, or the affine function x/2 below one.
Take a maximizing allocation in (3). If two coordinates are noninteger,
keep their sum and all other coordinates fixed, and move the two in
opposite directions within their current closed unit intervals. The
allowed parameter values form a nondegenerate closed segment. The sum
of their two psi values is convex on this segment, so one endpoint
has value at least the current value. At an endpoint at least one of
the two coordinates is integral. This replacement preserves a maximum
and decreases the number of noninteger coordinates. After at most s-1
such replacements, all but at most one coordinate are integral.
This elementary reduction uses only one-dimensional convexity, without
an unproved enumeration of continuous allocations.

Thus a maximizing allocation can be chosen with all but at most one
coordinate integral. For \(c=Q+\theta\), the remaining coordinate
is \(a+\theta\), with integer \(0\le a\le Q\). The other u=s-1
integer coordinates sum to Q-a. Their integer values maximize
\(\sum f(n_i)\), where \(f(n)=n/(n+1)\). The increment
\[
                   f(n+1)-f(n)=1/\{(n+1)(n+2)\}
\]
is strictly decreasing. Transferring one unit from a coordinate at
least two larger than another strictly increases the sum. The
maximizing integer coordinates therefore differ by at most one:
u-t equal b and t equal b+1, where \(Q-a=ub+t\). This proves (6),
including \(\theta=0\). Zero integer coordinates contribute zero and
are allowed. No unbounded search remains in that formula.

## 6. Concave limit and an exact gap distinction

The slopes in (7) decrease, so h is concave and 1/2-Lipschitz.
Also \(\psi\le h\), with equality on [0,1] and at integer points,
and strict inequality at every noninteger point greater than one.
To check this directly on [a,a+1], h lies above its constant left
endpoint and its chord to the right endpoint; each of the two terms
in (2) touches it at only its respective integer endpoint.
Jensen's inequality gives
\[
                         \Psi_s(c)\le s h(c/s).             \tag{13}
\]
At integer total c=Q, balanced integer coordinates attain equality
in (13), by the preceding unit-transfer argument. At arbitrary
c=Q+\(\theta\), increasing one coordinate in this integer allocation
shows \(\Psi_s(c)\ge s h(Q/s)\). Consequently
\[
       0\le s h(c/s)-\Psi_s(c)\le(c-Q)/2<1/2.              \tag{14}
\]
This proves (9), and (8) follows from (4) and (13).
For \(c\le s\), choose all coordinates in [0,1], giving \(\Psi_s(c)=c/2\).
For noninteger \(c>s\) the inequality in (13) is strict: equality in
Jensen requires all coordinates to lie in the same linear unit
interval of h above one (or all equal at an integer breakpoint).
Equality \(\psi=h\) then forces integral coordinates, whose total
cannot be a noninteger. This explains why the fixed-s spectrum can
be strictly smaller than the limiting concave curve.

Finally let the rank R and prescribed matching number s both tend
to infinity, and write c=a+\(\theta\) with integer \(a\ge0\). Use only the
common-rank integer endpoint families \(H_R(a)\) and \(H_R(a+1)\),
in proportions tending to 1-\(\theta\) and \(\theta\) among s disjoint copies.
Their edge density and fractional value, normalized by Rs, tend to
c and \((1-\theta)f(a)+\theta f(a+1)=h(c)\). Their matching number
is exactly s. Only two fixed design block sizes occur, so the
common-rank error is O(1/R), uniformly in the number of copies.
This proves the sharpness and arbitrary prescribed-sequence clause
in Theorem 3. The case c=0 uses s disjoint R-edges.

## 7. Dependencies, verification and scope

The finite upper bound uses only feasible weights, the exact greedy
partition and the anchored signed count. It uses neither Wilson nor
Kahn nor any solver output. The common-rank lower constructions use
explicitly named published inputs from [F]; the diverging-matching
sharpness requires only Wilson's design theorem at integer endpoints.

This is a fractional matching and cover result, not an integer-cover
rounding theorem. It does not resolve Ryser, Kahn's triple-intersection
question or the general weighted nonuniform Füredi--Kahn--Seymour
conjecture.

Pinned Lean coverage, exact rational diagnostics, source attribution
and the frozen inventory are recorded in separate files. The full
greedy construction, convex allocation reduction, imported existence theorems,
LP duality and asymptotic sharpness are written proofs, not asserted
to be whole-paper formalized. No external human review, historical
priority or prize-level classification is claimed.

## References

[F] The repository proof *The sharp fractional cover frontier at every
finite edge/rank ratio*, public commit
<https://github.com/mxym/math/commit/c5255aaf66f9e894c6cbb0e2d1eb47c738c23765>,
7 October 2026. Its exact finite incidence Lean proof, construction
certificates and full LP-duality appendix are preserved unchanged.

[W] R. M. Wilson, *An existence theory for pairwise balanced designs,
III: Proof of the existence conjectures*, JCTA A 18 (1975), 71--79,
DOI <https://doi.org/10.1016/0097-3165(75)90067-9>. Fixed-block
Steiner design existence is an explicitly imported classical theorem.

[K] J. Kahn, *On a Problem of Erdős and Lovász. II: n(r)=O(r)*,
JAMS 7 (1994), 125--143, Corollary 5.4, printed p.140,
DOI <https://doi.org/10.1090/S0894-0347-1994-1224593-5>.

[Fu] Z. Füredi, *Maximum degree and fractional matchings in uniform
hypergraphs*, Combinatorica 1 (1981), 155--162. The classical
rank/matching-number bound is prior context. The present spectrum
also fixes the edge/rank ratio; no priority conclusion is drawn.

[FKS] Z. Füredi, J. Kahn and P. D. Seymour, *On the fractional matching
polytope of a hypergraph*, Combinatorica 13 (1993), 167--180,
DOI <https://doi.org/10.1007/BF01303202>.
