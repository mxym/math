# A universal fractional cover envelope and its design equality cases

Research continuation, 7 October 2026. All inequalities in this note
are proved for fractional covers. No small-intersection hypothesis is
used, and no corresponding integer-cover bound is asserted.

## 1. Definitions and finite theorem

Let H be a finite simple intersecting r-uniform hypergraph, \(r\ge2\),
with \(m\ge1\) edges. Ignore vertices outside its edges. A fractional vertex
cover assigns nonnegative weights \(z_v\) to vertices so that
the sum on each edge is at least one; its minimum total is \(\tau^*(H)\).
Its finite linear-programming dual assigns nonnegative weights y_E to
edges, with sum at each vertex at most one, and maximizes
\(Y=\sum_Ey_E\). Appendix A explains the duality used here.

Put \(k=\lceil m/r\rceil\). If \(k=1\), pairing gives
\(\tau^*(H)\le\tau(H)\le\lceil m/2\rceil\le m/2+1/2\). For \(k\ge2\) define
\[
 g=(k-1)r+1,\qquad
 U_k(r,m)=\frac{k(k-1)r^2+(2k-1)r+1-m}
                    {(k^2+k-1)r+1-m}.                 \tag{1}
\]
The choice of k gives \(g\le m\le kr\), and the denominator is positive.

**Theorem 1 (universal finite envelope and equality).** For \(k\ge2\),
\[
                       \tau^*(H)\le U_k(r,m).        \tag{2}
\]
Equality holds if and only if \(m=g\), H is linear, and every active
vertex has degree k. Thus equality hypergraphs are precisely the
incidence duals of Steiner 2-(m,k,1) designs with replication r.
No resolvability is required for this fractional equality statement.
If \(m>g\), inequality (2) is strict.

Define a continuous function phi on nonnegative real numbers by
\[
 \phi(c)=c/2\quad(0\le c\le1),\qquad
 \phi(c)=\frac{k(k-1)}{k^2+k-1-c}
                      \quad(k-1\le c\le k,\ k\ge2).  \tag{3}
\]
The definitions agree at shared endpoints. In particular
\(\phi(a)=a/(a+1)\) for positive integers a.

**Corollary 2 (bounded edge/rank ratios).** For \(k\ge2\),
\[
              \tau^*(H)\le r\phi(m/r)+1/k.           \tag{4}
\]
For any sequence with r tending to infinity and m/r tending to a
finite c>=0,
\[
              \limsup \tau^*(H)/r\le\phi(c).         \tag{5}
\]
This has no partite, linearity or intersection-excess assumption.

Let h be the piecewise linear interpolation of a/(a+1) at nonnegative
integers a. For k-1<c<k, \(k\ge2\), put theta=c-k+1. Then
\[
 h(c)-\phi(c)=\frac{\theta(1-\theta)}
                    {k(k+1)(k^2-\theta)}>0.          \tag{6}
\]
Thus (5) is strictly smaller than both h(c) and c/(1+c) at
noninteger c>1. Neither phi nor the strict finite bound for \(m>g\) is
claimed to be the optimal envelope at these ratios. In fact the
universal strict gap in Theorem 3 below rules out attaining phi there.

## 2. Two weighted counting observations

Fix any feasible dual weights, set \(Y=\sum_Ey_E\), and let
\(b=\max_Ey_E\). Choose an edge P with \(y_P=b\).

Since each edge other than P meets P and weights are nonnegative,
\[
 Y-b\le\sum_{v\in P}\sum_{E\ne P:\ v\in E}y_E
       \le r(1-b),\qquad
                    Y\le r-(r-1)b.                 \tag{7}
\]
The first inequality remains valid with multiple intersections.
No equality or linearity is silently assumed.

Suppose \(b>1/(k+1)\) and put \(t=(1-b)/k\), so \(b>t\). Let G be the set of
edges with weight strictly greater than t; P belongs to G. At a
vertex of P there can be at most k-1 other edges of G: k of them
would have total weight greater than \(kt=1-b\), violating feasibility.
All other members of G meet P. Consequently
\[
                          |G|\le1+r(k-1)=g.          \tag{8}
\]
Every weight in G is at most b, and every weight outside G is at
most t. Because \(b>t\) and \(g\le m\), (8) gives
\[
 Y\le |G|b+(m-|G|)t
       \le gb+(m-g)(1-b)/k.                          \tag{9}
\]
These statements require only finite nonnegative sums and vertex
constraints. In particular they hold for every feasible dual vector,
not just a solver's reported optimum.

## 3. Derivation of the finite envelope

First suppose \(b\le1/(k+1)\). Then \(Y\le m/(k+1)\). The numerator N and
denominator Q in (1) satisfy
\[
 (k+1)N-mQ=(m-(k+1)g)(m-kr-1)>0,                  \tag{10}
\]
because \(g=(k-1)r+1\), \(r\ge2\), \(k\ge2\) and \(m\le kr<(k+1)g\).
Therefore \(Y<U_k(r,m)\) in this case.

Otherwise use (9). The coefficient
\[
                  A=((k+1)g-m)/k
\]
of b is positive. By (7), \(b\le(r-Y)/(r-1)\). Substituting in (9)
and multiplying positive denominators gives
\[
 Y\{k(r-1)+(k+1)g-m\}\le g(kr+1)-m.              \tag{11}
\]
The braces equal Q and the right side equals N. This proves \(Y\le U\).
Theorem 1's inequality now follows by finite LP duality. Its proof
does not use a numerical solver, a colouring theorem or a literature
claim about another research result.

## 4. Complete finite equality analysis

Suppose \(\tau^*=U\). An optimum dual vector exists: each coordinate
lies in [0,1], so its feasible set is a nonempty compact polytope.
By (10) its maximum b is greater than 1/(k+1). Equality in (11)
forces equality in (7) and (9), since \(A>0\). In particular
\[
 |G|=g,\qquad y_E=b\ (E\in G),\qquad
 y_E=t=(1-b)/k\ (E\notin G).                       \tag{12}
\]
Every member of G other than P meets P. Equality in (8) forces each
of P's r vertices to belong to exactly k-1 other G edges, with each
G edge meeting P exactly once. Equality in the last inequality of
(7) forces the total incident dual weight at every vertex of P to
be one.

But a vertex of P already lies in k edges of G. If it also lay in
one outside edge, its total weight would be at least
\[
 kb+t=kb+(1-b)/k>1,                                \tag{13}
\]
where the strict inequality is equivalent to \(b>1/(k+1)\).
Thus no outside edge can meet P. Intersectingness implies that
there are no outside edges, so \(m=g\). Equation (12) gives uniform
edge weights b, and the saturation at P gives \(kb=1\).
Thus \(b=1/k\) and \(Y=m/k\).

Apply (7) to each original edge, all of which now have maximum
weight b. Since \(Y-b=(m-1)/k=r(k-1)/k=r(1-b)\), every inequality in
(7) is an equality. Positive edge weights force every pair of
distinct original edges to intersect exactly once. Saturation at
every active vertex gives \(d(v)b=1\), hence \(d(v)=k\). This proves the
necessary equality conditions.

Conversely, if H is linear, all active degrees are k, and \(m=g\),
uniform dual weights 1/k are feasible with total m/k. Uniform
primal vertex weights 1/r give every edge total one; double
counting incidences gives \(n=mr/k\), so their total \(n/r=m/k\).
Weak duality certifies \(\tau^*=m/k\). At \(m=g\), (1) equals m/k.
This proves the converse without requiring design existence.

The design interpretation is explicit: original edges become points,
and original vertices become k-point blocks. Linearity and
intersectingness say every pair of points belongs to exactly one
block. Each point belongs to exactly r blocks. Conversely the
incidence dual of such a design has all the stated properties.

## 5. Asymptotic comparison and examples

Write c=m/r=k-1+theta with 0<theta<=1 and \(k\ge2\). Set
d=k^2-theta and a=k(k-1), so phi(c)=a/d. Subtracting r phi(c)
from (1) gives
\[
 U_k-r\phi(c)=\frac{(k-\theta-\phi(c))r+1}{dr+1}.
                                                               \tag{14}
\]
This is at most 1/k: after multiplication, the difference between
(dr+1)/k and the numerator is
\[
 r\{\theta(1-1/k)+\phi(c)\}-(k-1)/k\ge0,           \tag{15}
\]
since \(\phi(c)\ge(k-1)/k\) and \(r\ge1\). This proves (4). At c<=1 use
pairing. The continuity in (3) then proves (5), including c=0.
The identity (6) follows by expanding
(k^2-1+theta)(k^2-theta)-k^2(k^2-1)=theta(1-theta).

For a prime power s, the affine-line design on F_s^N has
m=s^N points, block size s and replication r=(s^N-1)/(s-1).
Its dual is linear intersecting r-uniform with degree s and
\(\tau^*=m/s\). Here k=s and m=(s-1)r+1. A parallel class also certifies
the integer cover \(\tau=m/s\), but resolvability was not used above.
These are standard design examples, not new constructions.

The projective plane of order q has r=q+1, m=q^2+q+1,
k=r and m=(k-1)r+1; it also attains (2). In particular the Fano
plane gives r=3,m=7,\(\tau^*=7/3\). This finite boundary is useful:
one cannot drop the finite correction and claim \(\tau^*\)<=r phi(m/r)
for every finite hypergraph.

## 6. A uniform explicit gap at noninteger ratios

**Theorem 3.** Fix \(k-1<c<k\), \(k\ge2\). Every sequence in Corollary 2
has \(\limsup\tau^*/r\le\phi(c)-\zeta_c\) for the positive constant below.
No small-intersection hypothesis is added.

Set \(\theta=c-k+1\), \(p=\phi(c)\), and define
\[
 a_0=k-1-\theta/k,\quad b_0=1-p,\quad t_0=p/k,
 \quad d_0=b_0-t_0>0,
\]
\[
 e_0=\min\{t_0/4,d_0/4,(k-1)d_0/[4(k+1)]\},\quad
 \delta_0=\min\{a_0d_0/[8(k+1)],kt_0/4\},\quad
 M=\lceil2/t_0\rceil.
\]
Then a conservative explicit choice is
\[
 \zeta_c=\min\left\{\delta_0,
   \frac{\theta}{(a_0+1)\{2M/d_0+(M+1)/e_0\}}\right\}>0. \tag{16}
\]

**Proof.** Pass to a subsequence on which \(\tau^*/r\) tends to its upper
limit alpha, choose optimal dual weights, and pass further so their
maxima b_r tend to b. The ceiling of m/r is eventually the fixed k.
Set \(\delta=p-\alpha\ge0\) by Corollary 2. If
\(\delta\ge\delta_0\) the conclusion already holds, so assume \(\delta<\delta_0\).

The small-maximum branch gives \(\alpha\le c/(k+1)\) if \(b\le1/(k+1)\).
But
\[
 p-c/(k+1)=a_0k d_0/(k+1)>\delta_0.
\]
Thus \(b>1/(k+1)\). For all sufficiently large indices use the
threshold \(t_r=(1-b_r)/k\), the set G from Section 2, and
\(g=(k-1)r+1\). Define the nonnegative mass defect
\[
 D_r=gb_r+(m-g)t_r-Y
    =(g-|G|)(b_r-t_r)+\sum_{E\in G}(b_r-y_E)
                           +\sum_{E\notin G}(t_r-y_E). \tag{17}
\]
The star bound and (9), after taking limits, give
\[
 b_0-\delta/a_0\le b\le b_0+\delta,\qquad
 \lim D_r/r=a_0b+\theta/k-\alpha\le(a_0+1)\delta.    \tag{18}
\]
Here \(a_0b_0+\theta/k=p\). All constants are fixed before taking
limits; no uniform asymptotic input is needed.

Call a G edge high-good if \(y_E\ge b_r-e_0\), and an edge outside G
low-good if \(y_E\ge t_r-e_0\). Let their numbers be H_r and L_r.
Equation (17) yields
\[
 H_r\ge g-\frac{D_r}{b_r-t_r}-\frac{D_r}{e_0},\qquad
 L_r\ge m-g-\frac{D_r}{e_0}.                        \tag{19}
\]
The chosen delta_0 and (18) imply \(b_r-t_r\ge d_0/2\) eventually,
and \(t_r-e_0>t_0/2\). They also imply
\[
 (k+1)(b_r-e_0)>1,\qquad
 k(b_r-e_0)+(t_r-e_0)>1.                            \tag{20}
\]
For explicit verification, the unperturbed margins in (20) are
kd_0 and (k-1)d_0. The possible lower change in b is at most
\(\delta/a_0<d_0/[8(k+1)]\), and \((k+1)e_0\le(k-1)d_0/4\).
The asserted strict margins follow. The lower bound on t_r-e_0
uses \(\delta/k<t_0/4\) and \(e_0\le t_0/4\).

Choose an edge P of maximum weight. It is high-good. Every vertex
of P meets at most k-1 other high-good edges by the first inequality
in (20). A vertex meeting a low-good edge meets at most k-2 other
high-good edges by the second. Each such vertex meets at most M
low-good edges because each has weight greater than t_0/2.
All high-good and low-good edges meet P, so
\[
                 H_r-1\le(k-1)r-L_r/M.             \tag{21}
\]
Repeated intersections can only increase the incident counts used
in this inequality and do not invalidate it.

Insert (19) into (21), divide by r, and use (18) and \(b_r-t_r\ge d_0/2\).
This gives
\[
 \theta\le(a_0+1)\delta\{2M/d_0+(M+1)/e_0\}.
\]
Together with the earlier \(\delta\ge\delta_0\) case this proves (16).
Every subsequential upper limit satisfies the result, completing
the proof. The displayed gap is not claimed optimal.

## 7. Implications and limitations

For m/r tending to c>0 and integer cover \(\tau/r\) tending to one,
(5) forces
\[
                  \liminf\tau/\tau^*\ge1/\phi(c).    \tag{22}
\]
The denominator is positive since \(\tau\ge1\) implies \(\tau^*\ge1\), and
the asymptotic statement follows by division. This describes a
necessary integrality gap for sparse maximal-cover families,
including possible partite Ryser counterexamples. It does not
exclude such families.

Kahn's 1994 Theorem 5.2 rounds a fractional cover of a fixed-rank
auxiliary hypergraph only when its *weighted* pair codegrees tend
to zero. An arbitrary optimal fractional cover need not satisfy
that condition. Thus (5) cannot simply be advertised as an
integer-cover theorem, even under small unweighted intersections.
The earlier near-linear integer envelope in this repository has
a separate proof and a separate hypothesis \(I=o(r^2)\).

The proof above is self-contained apart from the standard finite
convex separation used to explain LP duality in Appendix A.
Exact rational primal/dual certificates and partial Lean algebra
exports accompany the note. They do not replace the universal
counting proof. Historical novelty and the optimal noninteger
frontier remain under investigation; no priority is asserted.

## Appendix A. Finite LP duality used here

Let A be the vertex-by-edge incidence matrix. Weak duality follows
from \(y^\top A^\top z\le\mathbf1^\top z\) and \(y^\top A^\top z\ge\mathbf1^\top y\) for feasible z,y.
The primal infimum alpha is attained: clipping each \(z_v\) to at most
one preserves all constraints and leaves a compact feasible cube.

For completeness consider the finitely generated closed convex cone
\[
 C=\{(A^Tz-s,\mathbf1^Tz+t):z,s,t\ge0\}
       \subset\mathbb R^{m+1}.
\]
For \(\beta<\alpha\) the point \((\mathbf1,\beta)\) is outside C. Finite-dimensional
separation supplies (a,b) nonnegative on C and strictly negative
on that point. The generators (-e_i,0) and (0,1) force \(a_i\le0\)
and \(b\ge0\). Write \(y=-a\). The generators associated with each vertex
force \(Ay\le b\mathbf1\), and strict separation gives \(\sum_i y_i>b\beta\).
If \(b=0\), then \(Ay\le0\) and \(y\ge0\); every edge is nonempty, so \(y=0\),
a contradiction. Hence y/b is dual-feasible with value >beta.
Letting beta increase to alpha and using compactness of the dual
feasible cube proves equality of the optima.

The standard facts just used are finite convex separation and the
closedness of a finitely generated cone. For the latter, any point
of such a cone has a representation using linearly independent
generators, by deleting dependencies while preserving nonnegative
coefficients. Along a convergent sequence pass to one fixed
independent subset (there are finitely many); the coefficients
converge by continuity of the inverse on its span, proving
closedness. No asymptotic combinatorial theorem enters this step.

## References and provenance

[K] J. Kahn, *On a Problem of Erdős and Lovász. II: n(r)=O(r)*,
J. Amer. Math. Soc. **7** (1994), 125–143,
DOI <https://doi.org/10.1090/S0894-0347-1994-1224593-5>, Section 5.
Its harmonic integer-cover bound and weighted rounding are prior
results; neither is used to prove Theorem 1 here.

[FKS] Z. Füredi, J. Kahn and P. D. Seymour,
*On the fractional matching polytope of a hypergraph*,
Combinatorica **13** (1993), 167–180,
DOI <https://doi.org/10.1007/BF01303202>. Fractional matching/cover
theory is the classical setting; this reference is not used as
an unproved input for (2).

[Previous] Repository note *An asymptotic cover law for sparse nearly
linear intersecting hypergraphs*, commit 34a212f, with the
subsequent Kahn prior-work addendum. Its h bound is for integer
covers under a different hypothesis. The present fractional
bound has its own proof and complete finite equality analysis.
