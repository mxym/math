# Fractional extremizers force near-design cores

Research continuation, 7 October 2026. We prove quantitative deletion
stability and an asymptotic if-and-only-if characterization at the
integer edge/rank ratios. The finite structural result uses no
linearity or small-intersection assumption. Its integer-cover
corollary uses an explicitly stated theorem of Kahn.

## 1. Conventions and statements

Let H be a finite simple intersecting r-uniform hypergraph, \(r\ge2\),
with \(m\ge1\) edges. Vertices outside all edges are ignored. A vertex
cover meets every edge, and its minimum size is \(\tau(H)\). A
fractional vertex cover has nonnegative vertex weights of sum at
least one on each edge; its minimum total is \(\tau^*(H)\).
Equivalently, by finite LP duality, \(\tau^*(H)\) is the maximum of
\(Y=\sum_E y_E\) over nonnegative edge weights satisfying
\[
                       \sum_{E\ni v}y_E\le1
                       \quad\hbox{for every vertex }v.       \tag{1}
\]
The optimum exists. Appendix A records the duality justification.

For any intersecting subfamily J put
\[
 I(J)=\sum_{\{E,F\}\subset E(J)}(|E\cap F|-1).                  \tag{2}
\]
Pairs are unordered and distinct. Set \(I=0\) for an empty subfamily.
Every summand is nonnegative; \(I=0\) means linearity.

**Theorem 1 (general finite extraction).** Fix an integer \(k\ge2\) and
any feasible weights (1). If \(Y>m/(k+1)\), retain exactly the edges
with \(y_E>1/(k+1)\). Let J be this core, q its edge count, and
\(s=m-q\) the number deleted. Then every active vertex of J has degree
at most k and
\[
 s\le \frac{m(k+1)\{mr-(m+r-1)Y\}}
              {(r-1)\{(k+1)Y-m\}}.                          \tag{3}
\]
Both factors in the denominator are positive. Independently of the
mass condition, this same threshold core has maximum degree at most k.
It satisfies
\[
 \sum_v d_J(v)(k-d_J(v))
       =q\{(k-1)r-q+1\}-2I(J)\ge0,                          \tag{4}
\]
including \(q=0\). In particular \(I(J)\le q\{(k-1)r-q+1\}/2\).

**Theorem 2 (linear deletion stability at a design boundary).** Suppose
\(m=(k-1)r+1\), \(k\ge2\), and put
\[
                     d=m/k-\tau^*(H)\ge0.                  \tag{5}
\]
There is a core J, obtained by the threshold above from any optimal
dual vector, for which
\[
 s\le\frac{2k^2(k+1)r}{r-1}\,d\le4k^2(k+1)d,
 \qquad \max_v d_J(v)\le k,\qquad I(J)\le qs/2.             \tag{6}
\]
If n counts its active vertices, then
\[
 \sum_v d_J(v)(k-d_J(v))=qs-2I(J),\qquad
                     0\le kn-qr\le qs.                    \tag{7}
\]
The dependence on d cannot be replaced by o(d) uniformly, already
for \(k=2\); Section 5 gives a family whose minimum deletion count is 2d.
No optimality of the coefficient in (6) is claimed.

**Theorem 3 (complete asymptotic characterization at integer ratios).**
Fix a positive integer a and a sequence of such hypergraphs with
\(r_j\to\infty\) and \(m_j/r_j\to a\). The following are equivalent:

1. \(\tau^*(H_j)/r_j\to a/(a+1)\).
2. Deleting o(\(r_j\)) edges leaves a core with maximum vertex degree
   at most a+1.

For the cores in either condition, \(q_j/r_j\to a\),
\[
 I(J_j)=o(r_j^2),\quad
 n_j/r_j^2\to a/(a+1),\quad
 \sum_v(d_{J_j}(v)-a-1)^2=o(r_j^2).                          \tag{8}
\]
Moreover
\[
              \tau(H_j)/r_j\to a/(a+1),\qquad
                         \tau(H_j)/\tau^*(H_j)\to1.        \tag{9}
\]
Only (9) uses the published rounding input stated in Section 4.
The hypotheses impose no bound on intersections in the whole family.
In fact (8) can fail for the whole family even when (9) holds exactly,
as Section 5 demonstrates.

## 2. The weighted estimate and finite extraction

Choose an edge P of maximum weight b. Every other edge meets P,
so nonnegative weights and (1) give
\[
 Y-b\le\sum_{v\in P}\sum_{E\ne P,\ v\in E}y_E\le r(1-b).
 \quad\hbox{Thus }Y\le r-(r-1)b.                            \tag{10}
\]
Multiple intersections only increase the middle sum. Since \(Y\le mb\),
\[
             Y\le\frac{mr}{m+r-1},\qquad
 (r-1)(mb-Y)\le mr-(m+r-1)Y=:\Psi.                         \tag{11}
\]
In particular \(\Psi\ge0\). These facts hold for every feasible vector.

For a deleted edge, \(b-y_E\ge b-1/(k+1)\). Thus
\[
 s\{b-1/(k+1)\}\le\sum_{E\text{ deleted}}(b-y_E)
                           \le mb-Y.                      \tag{12}
\]
Here all peak deficits b-y_E are nonnegative. Since \(b\ge Y/m\) and
\(Y/m>1/(k+1)\), combining (11)--(12) proves (3).

If a vertex belonged to at least k+1 retained edges, their weights
would sum to more than one. Hence the retained degree is at most k.
For the core, double counting incidences and edge-pair intersections
gives
\[
 \sum_v d_J(v)=qr,\qquad
 \sum_v\binom{d_J(v)}2=\binom q2+I(J).
\]
Consequently \(\sum_v d_J(v)^2=qr+q(q-1)+2I(J)\).
Subtracting this from kqr proves (4); all summands on its left
are nonnegative. This proves Theorem 1, including empty cores.

## 3. The design boundary and the iff statement

At \(m=(k-1)r+1\), equation (11) gives \(\tau^*\le m/k\), proving
\(d\ge0\). For an optimal dual vector, \(Y=m/k-d\) and \(\Psi=krd\).
If \(d\le m/[2k(k+1)]\), then
\[
              (k+1)Y-m=m/k-(k+1)d\ge m/(2k)>0.
\]
Insert these estimates into (3) to obtain the first bound in (6).
If d is larger instead, the trivial bound \(s\le m\) gives
\(s\le2k(k+1)d\), which is stronger. This proves (6) for every d,
with no small-deficit hypothesis. Formula (4) becomes the first
identity of (7). For each active degree \(1\le d_J(v)\le k\),
\(0\le k-d_J(v)\le d_J(v)(k-d_J(v))\). Summing proves the second
claim of (7). This completes Theorem 2.

For Theorem 3 put \(k=a+1\). Under condition 1,
\[
 \Psi_j/r_j^2
 =m_j/r_j-(m_j/r_j+1-1/r_j)Y_j/r_j\longrightarrow0.
\]
Also \(Y_j/m_j\to1/k>1/(k+1)\). Applying (3) shows \(s_j/r_j\to0\).
This proves condition 2, with an actual threshold core.

Conversely, if a core of size \(q_j=m_j-o(r_j)\) has degree at most k,
put weight 1/k on each core edge and zero on each deleted edge.
These weights are feasible for the original family, giving
\(\tau^*(H_j)\ge q_j/k\). The harmonic upper bound (11) proves
condition 1. This argument is valid for any such core.

For any core as in condition 2, (4) implies
\[
 0\le\sum_v d_J(v)(k-d_J(v))\le q\{(k-1)r-q+1\}=o(r^2),
 \qquad 0\le2I(J)\le q\{(k-1)r-q+1\}=o(r^2).
\]
The bracket is nonnegative for nonempty cores, by (4).
Summing k-d_J as above shows \(kn-qr=o(r^2)\). Finally, for
\(1\le d_J\le k\), \((k-d_J)^2\le(k-1)d_J(k-d_J)\); summation proves
the variance assertion (8). This proves every structural part of
Theorem 3 without a rounding theorem.

## 4. Integer rounding and what is imported

**Input K (Kahn 1994, Corollary 5.4, printed p.140).** For fixed C>0,
an intersecting r-uniform sequence with at most Cr edges and
maximum intersection of distinct edges o(r) satisfies
\[
                    \tau/r\le C/(C+1)+o(1).                \tag{13}
\]
This is a published input, not an assertion proved or formalized
in this note. We explain precisely how its hypotheses are reached.

Let J be a core from Theorem 3 and write \(\epsilon=I(J)/r^2\to0\).
Put \(\rho=\sqrt{\epsilon}+r^{-1/2}\), so \(\rho\to0\) and \(\rho r\ge\sqrt r\).
Every edge pair with intersection at least \(\rho\) r contributes at
least \(\rho r-1\) to I(J). The number of such pairs is at most
\[
 I(J)/(\rho r-1)=o(r).
\]
Indeed its ratio to r is \(\epsilon/(\rho-1/r)\to0\).
Choose and delete one edge from each such pair. At most o(r) edges
are deleted, and no bad pair remains. The resulting family J'
has maximum distinct-edge intersection \(<\rho r=o(r)\).

For each fixed \(\eta>0\), J' has at most \((a+\eta)r\) edges eventually.
Applying Input K and then letting \(\eta\) decrease to zero gives
\(\limsup\tau(J')/r\le a/(a+1)\). Each deleted edge, from either
stage, can be covered with one of its r vertices; thus the total
extra cost is o(r). Therefore the same upper bound holds for H.
The lower bound \(\tau(H)\ge\tau^*(H)\) proves (9).

One consequence is a uniform separation statement: for each fixed
integer a and \(\eta>0\) there exist \(\delta>0\) and R such that, if \(r\ge R\),
\(|m/r-a|\le\delta\) and \(\tau/r\ge a/(a+1)+\eta\), then
\(\tau^*/r\le a/(a+1)-\delta\). If this failed, for \(\delta=1/j\) and
\(R=j\) one could choose a violating family with \(m/r\to a\), integer
cover ratio bounded above the endpoint, and fractional ratio tending
to the endpoint by (11). This contradicts Theorem 3.
No explicit value of \(\delta\), no rate in Input K, and no resolution
of unrestricted Ryser's conjecture are asserted.

## 5. Sharp deletion order and unavoidable exceptional edges

Here is a complete elementary family for \(k=2\). Fix even \(n\ge4\) and
an integer \(t\ge1\), and put \(r=n-1+t\). For each pair of distinct indices
i,j in {1,...,n} use a vertex \(x_{ij}=x_{ji}\). Define n good edges
\[
 A_i=\{x_{ij}:j\ne i\}\ \cup\ \{u_{i,1},\ldots,u_{i,t}\},
\]
where all padding vertices u are distinct and fresh. Thus \(|A_i|=r\),
and distinct good edges meet exactly once. Let C be the n/2 vertices
of one fixed perfect matching of the index set. Each good edge
contains exactly one vertex of C.

Take a fresh common set W of size \(r-n/2-1=n/2+t-2\), and fresh distinct
vertices \(p_1,\ldots,p_t\). The t bad edges are
\[
                         B_l=C\cup W\cup\{p_l\}.
\]
Each has r vertices; all edges are distinct. Each bad edge meets
each good edge exactly once, and two bad edges meet in r-1 vertices.
The whole family is intersecting, with \(m=n+t=r+1\).

Put dual weight 1/2 on the good edges and zero on the bad edges.
Pair vertices have incident dual weight one, good private vertices
have weight 1/2, and all other vertices have weight zero. This is
feasible with total n/2. The integer cover C has size n/2 and meets
every edge. Weak duality therefore certifies
\[
             \tau=\tau^*=n/2,\qquad d=m/2-n/2=t/2.         \tag{14}
\]
Deleting all bad edges leaves degree at most two. Conversely, let
\(\ell\) bad edges remain in any degree-at-most-two subfamily. At a
vertex of C they already have degree \(\ell\), so \(\ell\le2\). Each of the
n/2 disjoint matching pairs originally contributed two good-edge
incidences at its vertex; at least \(\ell\) of these two good edges
must be deleted. These requirements involve disjoint good-edge
sets, so at least \(\ell n/2\) good edges are deleted. The total deletion
count is consequently at least
\[
                     t-\ell+\ell n/2\ge t.
\]
Its exact minimum is \(t=2d\). This proves the sharp linear order claim.

Only bad--bad pairs contribute excess, so
\[
                         I(H)=\binom t2(r-2).              \tag{15}
\]
For the exact integer sequence \(n=2j^4\) and \(t=j^3\), \(j\ge2\), we have
\(t=o(r)\), \(m/r\to1\) and fractional ratio tending to 1/2, but
\(I(H)/r^2\to\infty\). Even the integer ratio agrees with its
fractional counterpart exactly. Thus Theorem 3 cannot require the
whole original family to have \(I=o(r^2)\), nor can it omit deletion.

## 6. Verification scope and significance limits

The finite extraction inequality, threshold degree cap, and
uniform-weight converse are formalized for actual finite incidence
sets in the accompanying pinned Lean project. The weighted-star
proof sums over real edge and vertex sets and uses the genuine
uniformity, intersectingness and feasibility hypotheses; these are
not replaced by a scalar assumption. Kernel reports contain only
propext, Classical.choice and Quot.sound.

The degree/excess double counting, real-sequence limit arguments,
LP duality, the sharpness construction and Input K are written
proofs, not full-paper Lean formalizations. Exact rational diagnostics
check incidence identities, the extraction bound and explicit
primal/dual sharpness certificates; they are not substitutes for
the universal proofs above. No external human review, historical
priority or high-level prize significance is claimed.

## Appendix A. The finite duality fact

Let A be the vertex-by-edge incidence matrix. Weak duality follows
by summing \(\sum_{E\ni v}y_E\le1\) against any feasible primal weights.
The primal infimum \(\alpha\) is attained after clipping each vertex
weight to at most one, which preserves feasibility; the dual is
compact because every edge is nonempty and hence each \(y_E\le1\).

For completeness use the finitely generated closed cone
\[
 \mathcal C=\{(A^Tz-s,\mathbf1^Tz+t):z,s,t\ge0\}
                         \subset\mathbb R^{m+1}.
\]
For \(\beta<\alpha\), the point \((\mathbf1,\beta)\) is outside it. Finite-dimensional
separation yields \((u,b)\), nonnegative on this cone and strictly
negative on that point. The generators \((-e_i,0)\) and \((0,1)\) give
\(u\le0\) and \(b\ge0\). With \(y=-u\), vertex generators imply \(Ay\le b\mathbf1\),
while strict separation gives \(\sum_i y_i>b\beta\). If \(b=0\), nonempty
edges and \(y\ge0\) would imply \(y=0\), a contradiction. Thus \(y/b\) is a
feasible dual vector of value \(>\beta\). Letting \(\beta\) increase to \(\alpha\)
and using dual compactness proves equality of optima.

The standard finite convex separation theorem is used here.
Closedness of the finitely generated cone follows by choosing a
representation with linearly independent generators, deleting
dependencies while preserving nonnegative coefficients. Along a
convergent sequence pass to one fixed independent subset of the
finitely many generators; its coefficients then converge by the
inverse on their linear span. This justifies the needed closedness.

## References and provenance

[K] J. Kahn, *On a Problem of Erdős and Lovász. II: n(r)=O(r)*,
J. Amer. Math. Soc. **7** (1994), 125--143. DOI
<https://doi.org/10.1090/S0894-0347-1994-1224593-5>, Corollary 5.4.
The harmonic integer bound and rounding theorem are prior work.

[F] Repository note *A universal fractional cover envelope and its
design equality cases*, commit 4ae9051, 7 October 2026. Its stronger
noninteger envelope and exact equality classification are preserved.
The present deletion estimate uses only the weighted-star inequality
and supplies a separate quantitative stability theorem.

The limited literature screen also identifies Kayll's DIMACS Report
95-55, Theorem 2.1, as an existing resolution of Kahn's Conjecture
5.6. That theorem is not an input here. The new finite extraction
and fixed-ratio characterization remain subject to further novelty
comparison; no first-result wording is used.
