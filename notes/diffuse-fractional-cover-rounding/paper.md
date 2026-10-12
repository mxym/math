# Diffuse optimum certificates and integer recovery with small triple intersections

Research continuation, 7 October 2026. We prove a finite theorem producing
an optimal fractional cover whose individual weights decrease as the rank
grows. We then combine it with an explicitly imported classical rounding
theorem to recover integer covers on a noninteger interval. The argument
does not assume small pair intersections. It does not resolve the entire
question stated as Kahn's Conjecture 5.5 in 1994.

## 1. Statements and conventions

Let H be a finite simple intersecting hypergraph with m nonempty edges,
each of size at most the integer r, and maximum vertex degree at most the
integer D. Throughout \(r\ge2\) and \(D\ge3\). Its integer vertex cover number is
\(\tau(H)\); its fractional vertex cover number is \(\tau^*(H)\). A
fractional cover x assigns nonnegative vertex weights with total at least
one on each edge. Isolated vertices are discarded. For convenience set
\[
 \Delta=(D-1)m-D(D-2)r-D,\qquad K_D=D(D-2).                 \tag{1}
\]

**Theorem 1 (finite diffuse optimum).** If \(\Delta>0\), then
\(\tau^*(H)=m/D\). There is an optimal fractional cover x such that
\[
 \boxed{\quad 0\le x_v\le\frac1{\lceil\Delta/K_D\rceil}
              \le K_D/\Delta\quad\hbox{for every vertex }v.\quad}
                                                                    \tag{2}
\]
Every optimal cover has weight zero at vertices of degree less than D,
and total weight exactly one on each edge. The existence of a cover in
(2) is proved by a finite repair and a minimax argument, not numerical
optimization. No pair- or triple-intersection restriction is needed.

Define
\[
 \chi_D=D-1-\frac{2}{3D(D-2)+2(D-1)}.                       \tag{3}
\]
For example, \(\chi_3=24/13\) and \(\chi_4=44/15\).

**Theorem 2 (integer recovery without small pair intersections).** Fix D.
Suppose \(H_j\) are as above, \(r_j\to\infty\),
\(m_j/r_j\to c\in(\chi_D,D-1]\), and
\[
 \lambda_j:=\max_{E,F,G\text{ distinct}}|E\cap F\cap G|=o(r_j).
                                                                    \tag{4}
\]
The maximum is zero if fewer than three edges occur. Then
\[
 \tau^*(H_j)=m_j/D\quad\hbox{eventually},\qquad
 \tau(H_j)=m_j/D+o(r_j),\qquad \tau(H_j)/\tau^*(H_j)\to1.      \tag{5}
\]
For \(D=3\) the interval is \((24/13,2]\). For \(D=4\) it is \((44/15,3]\).
The bound on vertex degree is a real hypothesis. The proof uses Kayll's
published bounded-edge-size rounding theorem and Edmonds's graph matching
polytope theorem, both stated in Section 5.

**Corollary 3 (fractional extremizers in this interval).** Let
\(\sigma_D=D-1-1/(D-1)\). Fix \(c\in(\chi_D,D-1)\). For a simple intersecting
r-uniform sequence with \(m/r\to c\), \(r\to\infty\), and (4), suppose
\[
                         \tau^*/r\to c/D.                    \tag{6}
\]
There is no initial bound on vertex degrees in this corollary. Then
\(\tau/r\to c/D\). Equivalently, the previously proved characterization
by deleting o(r) edges to leave maximum degree at most D now also implies
integer recovery under small triple intersections on this interval.
We specify the precise extraction input in Section 7.

The narrower range in (3) is intentional. We do not claim the entire
strict fractional ramp \((\sigma_D,D-1)\), a general integer frontier, or
a solution of Ryser's conjecture. The present status of Kahn 5.5 is not
settled by our limited literature screen. No first-result claim is made.

## 2. The finite fractional input

We use the following already proved repository theorem. For any simple
intersecting family of m nonempty edges of rank at most \(r\ge2\) and every
integer \(k\ge2\),
\[
 \tau^*\le\max\left\{\frac{(k-1)r+1}{k},\frac{m}{k+1}\right\}.\tag{7}
\]
Its complete proof appears in the attributed predecessor
*The sharp fractional cover frontier at every finite edge/rank ratio*,
commit c5255aaf66f9e894c6cbb0e2d1eb47c738c23765, Sections 2--3. It uses a
maximum dual edge weight, assigns every other edge to exactly one common
vertex, and sums a signed bin inequality. The finite bound is independent
of any design existence, rounding theorem or OpenAI result. Its actual
finite incidence implication has a partial Lean formalization there.

In our setting, uniform dual edge weights 1/D are feasible, because a
vertex belongs to at most D edges. Thus \(\tau^*\ge m/D\). Apply (7) with
k=D-1. The strict inequality \(\Delta>0\) says exactly that
\[
                 \frac{(D-2)r+1}{D-1}<\frac mD.
\]
Consequently \(\tau^*=m/D\).

For any optimal cover x, summing its edge loads gives
\[
 m\le\sum_E\sum_{v\in E}x_v
       =\sum_v d(v)x_v\le D\sum_vx_v=m.                      \tag{8}
\]
All quantities are finite and every summand is nonnegative. Equality
throughout implies edge loads one, and \((D-d(v))x_v=0\) for each vertex.
In particular positive weights are supported on degree-D vertices.
This proves the asserted support and load conditions without using
complementary slackness as an unstated assumption.

The optimal-cover set is nonempty and compact. For completeness, any
nonnegative cover weight may be truncated to one without violating a
cover constraint. Minimize the sum over the resulting finite box. Once
the optimal value is m/D, (8) implies every active coordinate is at most
one; the optimal set is a closed subset of the box. Hence the largest
coordinate has a minimum on it.

## 3. Removing degree-D vertices and repairing intersections

**Lemma 4 (repair).** Let R be any set of vertices, all of degree D, and
let L be an integer such that each original edge contains at most L
vertices of R. There is a simple intersecting hypergraph \(H_R\), on the
same m edge labels, whose maximum vertex degree is at most D and rank at
most \(r+L\). All retained original vertices have their original
incidence sets. Every new vertex has degree strictly less than D.

**Proof.** Delete R. For each removed vertex v, partition its D incident
edge labels into three nonempty groups \(G_{v,1},G_{v,2},G_{v,3}\). This
is possible since \(D\ge3\). Create three fresh vertices \(z_{v,1},z_{v,2},z_{v,3}\),
where \(z_{v,i}\) belongs precisely to the incident labels outside \(G_{v,i}\).
Every incident label receives exactly two of them. The new vertex
\(z_{v,i}\) has degree \(D-|G_{v,i}|\), between two and D-1. All new
vertices are distinct from one another and from all original vertices.

An edge containing t removed vertices loses t vertices and receives
2t new ones. Its size is therefore
\[
                    |E|+t\le r+L.                           \tag{9}
\]
Every original edge pair still meets: a retained common vertex remains,
or at a removed common vertex its two labels together exclude at most
two group indices, so they share at least one of the three new vertices.
Nonempty edges remain nonempty, and old vertex degrees are unchanged.

Simplicity also survives. For distinct original edges E,F, choose an
original vertex belonging to one of them and not the other. If it is
retained it still distinguishes them. If it was removed, its replacement
places two fresh vertices on the incident label and none on the other
label. Thus the repaired edges remain distinct. This proves the lemma.

The three-complement repair is stronger than replacing a removed vertex
by all pairwise intersections: its rank cost is only one per removed
incidence, for every \(D\ge3\). No degree-D replacement vertex is introduced.

If
\[
                  \Delta>K_D L,                             \tag{10}
\]
then (7), applied to \(H_R\) with rank parameter \(r+L\), again gives
\(\tau^*(H_R)=m/D\). Formula (8) for \(H_R\) implies every new vertex of
degree below D has optimal weight zero. Therefore an optimal cover of \(H_R\)
uses only retained degree-D original vertices, and defines an optimal
cover of H avoiding R. This is a finite resilience statement; R need
not be small in total size, only in its incidence count on each edge.

## 4. Proof of the diffuse optimum theorem

Choose an optimal cover x minimizing \(M=\max_v x_v\). We have \(M>0\) because
\(m>0\). Let R be the nonempty set of vertices where \(x_v=M\). They all have
degree D by (8). At an edge, its load one shows
\[
                   |E\cap R|M\le1.
\]
Put \(L=\max_E|E\cap R|\), so \(L\le1/M\). Suppose that
\(M>K_D/\Delta\). Then \(K_DL\le K_D/M<\Delta\). Lemma 4 and (10) provide
another optimal cover x' which is zero on R.

For every coordinate outside R we have \(x_v<M\). There are finitely many
coordinates, so for sufficiently small positive \(\varepsilon\),
\[
              (1-\varepsilon)x_v+\varepsilon x'_v<M
                    \quad(v\notin R).
\]
On R the same convex combination equals \((1-\varepsilon)M<M\).
The combination remains an optimal cover, contradicting minimality of M.
Thus \(M\le K_D/\Delta\). For the sharper rounded version put
\(N=\lceil\Delta/K_D\rceil\ge1\). If \(M>1/N\), then \(L\le1/M<N\), so the integer
L satisfies \(L\le N-1<\Delta/K_D\). The same repair and convex-combination
contradiction applies. Thus \(M\le1/N\), completing Theorem 1. The finite proof covers
nonuniform families as well as uniform ones. It is not a fully
formalized linear-program argument; the exact formal scope is recorded
in the accompanying formal README.

## 5. Imported rounding and matching-polytope facts

Pass to the incidence dual J. Its m points are the edges of H; each
original vertex v determines a block \(B_v\) of its incident edge labels.
The blocks have size at most D. A vertex cover of H is precisely a block
cover of J. Distinct original vertices may give identical blocks. When
needed merge such blocks, summing their fractional weights; any chosen
merged block has an original representative, so integer cover cost does
not increase. All codegrees below count original block occurrences.

For a block-weight vector t, let
\(\alpha_3(t)=\max_{p,q,s\text{ distinct}}\sum_{B\supset\{p,q,s\}}t(B)\).
For S a point set define the local restriction, on subsets A of S, by
\[
 t|_S(A)=\sum_{B\cap S=A}t(B)\quad(|A|\ge2),\qquad
 t|_S(A)=0\quad(|A|<2).                                     \tag{11}
\]
Let MP(S) be the convex hull of incidence vectors of matchings of these
subsets (each matching consists of pairwise disjoint subsets of size at
least two). Let b(t) be the largest integer such that every set S of at
most that size has \(t|_S\in\mathrm{MP}(S)\). Ignoring singleton coordinates
in (11) is part of the Kayll theorem's definition, not a change of the
cover constraints of J.

**Input KQ (Kayll 1995, Theorem 2.1).** For fixed D, a D-bounded
hypergraph J and a fractional block cover t satisfy
\[
                    \rho(J)\le(1+o(1))\sum_Bt(B)             \tag{12}
\]
whenever \(\alpha_3(t)\to0\) and \(b(t)\to\infty\). Here \(\rho\) denotes
minimum integer block cover. The precise readable source is P. M. Kayll,
*Asymptotically Good Covers in Hypergraphs: Extended Abstract of the
Dissertation*, DIMACS Technical Report 95-55 (1995), printed p.5,
Theorem 2.1; definitions appear immediately above it. This theorem
generalizes Kahn 1994 Conjecture 5.6. The later Kahn--Kayll paper has DOI
10.1006/jcta.1997.2761. We read the extended abstract's full primary
statement, not that later paper's inaccessible full text. The rounding
theorem is imported, not reproved or formalized in this package.

**Input E (Edmonds's graph matching polytope).** Nonnegative graph-edge
weights w lie in the convex hull of graph matchings if and only if each
vertex load is at most one and for every odd vertex set T,
\(\sum_{e\subset T}w_e\le(|T|-1)/2\). Consequently, every such vector with
maximum weighted degree at most 2/3 belongs to that polytope: for
odd \(|T|\ge3\), its internal mass is at most \(|T|/3\le(|T|-1)/2\).
The one-point constraints are vacuous. Source: J. Edmonds, *Maximum
matching and a polyhedron with 0,1-vertices*, J. Res. Nat. Bur. Standards
B 69 (1965), 125--130. This standard characterization is another stated
input; the elementary degree-to-odd-set implication is proved here.

## 6. Local control and proof of integer recovery

The argument also gives a finite local certificate. If t is a fractional
tiling on the incidence dual, \(t(B)\le M\), and the maximum triple codegree is
\(\lambda\), then for any integer \(h\ge2\) with
\[
 \epsilon=\binom h3 M\lambda<1,\qquad
 M\{(D-1)r-m+h\}\le\frac23(1-\epsilon),                     \tag{13a}
\]
we have \(b(t)\ge h\). This uses only the stated pair coverage, degree/rank
bounds, and Input E. The following proof establishes this finite
criterion as well as its asymptotic application.

Take the cover x from Theorem 1 and write \(t(B_v)=x_v\). By (8) it is a
fractional tiling of J, meaning each point has load exactly one, with
\(\sum_Bt(B)=m/D\). Every positive block has size D, and \(t(B)\le M\), where
\(M=K_D/\Delta\).

Here is a useful counting inequality independent of these weights. Fix
a set S of h points and p in S. Pair coverage implies
\[
 \sum_{q\notin S}d(p,q)\ge m-h,
 \qquad \sum_{q\ne p}d(p,q)
       =\sum_{B\ni p}(|B|-1)\le(D-1)r.
\]
Subtracting gives the **local pair budget**
\[
             \sum_{q\in S\setminus\{p\}}d(p,q)
                         \le(D-1)r-m+h.                     \tag{13}
\]
Each block at p which meets S at least twice contributes at least one
to the left. Hence the total nontrivial restriction load at p is at most
\[
                  M\{(D-1)r-m+h\}.                         \tag{14}
\]
This uses the actual incidence count, even if a block meets S more than
twice. It is not a claim about an arbitrary optimal cover.

Along the sequence in Theorem 2 set \(\delta=D-1-c\). We have
\[
 rM\longrightarrow C=\frac{D(D-2)}{1-(D-1)\delta},
 \qquad C\delta<2/3,                                        \tag{15}
\]
because (3) is exactly \(\delta<2/\{3D(D-2)+2(D-1)\}\).
The denominator is strictly positive. The original family also satisfies
\(m-1\le(D-1)r\) by pair coverage, explaining \(c\le D-1\).

Moreover \(\alpha_3(t)\le M\lambda\to0\). Choose an integer \(h_j\) tending
to infinity slowly enough that
\[
                  M h_j\to0,\qquad h_j^3M\lambda\to0.       \tag{16}
\]
For example the integer part of \((r/(\lambda+1))^{1/4}\) works
eventually: \(M=O(1/r)\), \(\lambda/r\to0\), and \(h_j/r\) tends to zero.
For every S of size \(h\le h_j\), the total mass
\(\eta=\sum_{|A|\ge3}t|_S(A)\) is bounded uniformly by
\[
                       \eta\le\binom h3 M\lambda=o(1),       \tag{17}
\]
since every block counted there contains a triple of S. Multiple
counting only increases the upper bound.

Let w be the pair coordinates of \(t|_S\). For \(h\ge2\) its weighted degree
is at most the bound in (14). Equations (15)--(17) imply, uniformly over
all such S, that the maximum weighted degree of \(w/(1-\eta)\) is strictly
less than 2/3 eventually. Input E supplies a convex combination of graph
matchings realizing \(w/(1-\eta)\). Multiply this distribution by \(1-\eta\) and,
for each \(|A|\ge3\), add probability \(t|_S(A)\) on the matching containing
the single subset A. The probabilities total one and the resulting
matching-incidence expectation is precisely \(t|_S\). For \(h<2\) the
restriction is zero and the empty matching suffices. Thus
\(b(t)\ge h_j\to\infty\).

This step checks all local higher-subset coordinates: it does not
replace their hypergraph matching polytope by a graph polytope without
accounting for them. It also explains why a degree bound strictly below
2/3 is useful rather than a mere vertex-load bound of one.

Input KQ now gives \(\tau(H)=\rho(J)\le(1+o(1))m/D\).
The lower bound m/D=\(\tau^*(H)\le\tau(H)\) proves (5), since
\(m=\Theta(r)\) and c>0. This completes the proof of Theorem 2.

## 7. Extending to fractional extremizers

The strict-ramp extraction proved at commit c5255a in the predecessor
states: for fixed \(c\in(\sigma_D,D-1]\), intersecting r-uniform families
with \(m/r\to c\) and \(\tau^*/r\to c/D\) admit deletion of o(r) edges to leave
maximum vertex degree at most D. Its proof selects edges of dual weight
greater than 1/(D+1), using the quantitative peak estimate in its
Theorem 4. This is a previously proved repository input, not a new
contribution here. The endpoint \(c=D-1\) is also covered by the earlier
integer-ratio extraction.

For Corollary 3 choose this core. Its edge count is m-o(r), its rank is
at most r, and its triple intersections are still o(r). Apply Theorem 2.
Each deleted nonempty edge can be covered with one extra vertex, so
\(\tau(H)\le m/D+o(r)\). The lower bound (6) proves the corollary. No
control on pair intersections of the original family or the core is
introduced. The same reasoning covers \(c=D-1\) using the stated endpoint
extraction, although integer recovery at that endpoint was already
proved in the predecessor.

## 8. Scope, examples and limitations

Small pair intersections genuinely need not follow from our hypotheses.
For example take the incidence dual of an affine-line design on
\(\mathbb F_3^N\), whose edges have rank \(r_0=(3^N-1)/2\), whose vertices
have degree three, and whose pair intersections are one. For two chosen
edges, add t fresh vertices belonging exactly to that pair. Pad every
other edge with t fresh private vertices. The result is simple,
intersecting and (\(r_0\)+t)-uniform, with maximum degree three, maximum
triple intersection one, and maximum pair intersection t+1. If
\(t/r_0\to\theta\in(0,1/12)\), then
\[
            m/r\to2/(1+\theta)>24/13,
            \max|E\cap F|/r\to\theta/(1+\theta)>0.
\]
It therefore falls within Theorem 2 and outside the small-pair input.
This example is illustrative; its integer recovery also follows from
its underlying design and is not an independent breakthrough.

The finite certificate (2) is not asserted optimal in its constant.
The threshold \(\chi_D\) comes from that constant and the sufficient 2/3
graph condition; neither is asserted sharp. For \(D=3\) the remainder of
the strict ramp, \((3/2,24/13]\), is not settled by this proof. Nor does
the proof settle families without the degree/core condition, or with
triple intersections of order r. Improving the diffuse constant, or
using sharper local odd-set information instead of a degree-only test,
are concrete further questions.

The complete written argument uses finite fractional-cover duality,
compactness, the predecessor finite theorem, Edmonds's theorem, and
Kayll's theorem exactly as disclosed. The rational checker verifies
repair incidences, feasible primal/dual certificates and local matching
distributions on fixed examples; it is not a proof of the infinite
rounding input. The Lean companion proves selected finite inequalities,
not the minimax existence argument, Edmonds/Kayll inputs or the full
asymptotic theorem. Literature comparison remains incomplete.
