# A 10/3 asymptotic lower coefficient through partite saving and linearization

Research continuation, 7 October 2026. This is a continuation of the
repository's partite cover-number programme, not a separate claim of
resolving Ryser's conjecture. All combinatorial arguments are written
below. Two attributed external inputs are identified explicitly.

## 1. The result and its scope

Let \(H\) be a finite simple intersecting \(r\)-partite \(r\)-uniform
hypergraph, \(r\ge2\), with \(m\) distinct edges and cover number
\(t=\tau(H)\). Edges meet every part in exactly one vertex. Empty
hypergraphs have cover number zero, and isolated vertices are irrelevant.

**Theorem 1.** For every \(\delta>0\) there is a finite constant
\(C_\delta\), independent of \(r,H\), such that
\[
 m\ge5\tau(H)-\left(\frac53+\delta\right)r-C_\delta. \tag{1}
\]
Consequently, whenever the defining class is nonempty,
\[
 f(r)=\min_{H:\,\tau(H)\ge r-1}|E(H)|
 \ge\left(\frac{10}{3}-\delta\right)r-C_\delta-5. \tag{2}
\]
In particular, for every \(\varepsilon>0\) and sufficiently large
\(r\), \(f(r)\ge(10/3-\varepsilon)r\).

The preceding complete elementary note proves the finite bound
\(f(r)\ge\lceil13r/4-10\rceil\). The new coefficient \(10/3\)
is greater than \(13/4\), and also greater than the directly applicable
\(293/96\) coefficient of Aharoni--Barát--Wanless [ABW]. This note
does not supply numerical thresholds from Kahn's theorem, determine
\(f(r)\), prove that its defining class is nonempty for every rank, or
settle the inequality \(\tau(H)\le r-1\). No priority claim is made.

The new ingredient is the saving-sensitive linearization estimate
\(e\ge\binom q2-qr/2-3W\), coupled to a cover saving of \(W/r\).
Degree-five peeling and the matching/star strategy follow Sivashankar
[S, Section 4]. The inherited degree-three lemma is proved in the
appendix. The other input is the published small-codegree edge-colouring
theorem of Kahn, precisely stated in Section 2. It is not re-proved or
Lean-formalized here. The theorem is unconditional as a deduction from
that standard theorem, with the dependency made explicit.

## 2. The edge-colouring input

For an auxiliary hypergraph, let \(D\) be its maximum vertex degree,
and let its maximum **codegree** be the greatest number of edges
containing any specified pair of distinct vertices. Its chromatic index
is the minimum number of colours needed to colour edges so that each
colour class is a matching. A hypergraph is **linear** if two distinct
edges meet in at most one vertex, equivalently its maximum codegree is
at most one for a simple hypergraph.

**Input K (Kahn, rank-four consequence).** For every \(\eta>0\)
there is an integer \(D_0\ge1\) such that a linear four-uniform
hypergraph of maximum degree \(D\ge D_0\) has chromatic index at most
\((1+\eta)D\). Hence it has a matching of size at least
\(e/((1+\eta)D)\), where \(e\) is its edge count.

This follows from [KKKMO, Theorem 3.1], attributed there to Kahn [K]:
for fixed rank \(k\) and \(\eta>0\), there is \(\gamma>0\) such
that rank at most \(k\), maximum degree at most \(D\), and maximum
codegree at most \(\gamma D\) imply list chromatic index at most
\((1+\eta)D\). Set \(k=4\) and increase the integer threshold so
that \(1\le\gamma D\). Ordinary colouring follows from list colouring;
the largest colour class gives the stated matching. All uses below
verify uniformity, linearity and the degree threshold.

## 3. Peeling and the two inherited estimates

Select vertices of current degree at least five and delete their incident
edges until the residual \(J\) has maximum degree at most four. Let
\(k\) count selected vertices and \(q=|E(J)|\). As in the preceding
note,
\[
 m\ge q+5k,\quad t\le k+\tau(J),\quad
 m\ge q+5(t-\tau(J)). \tag{3}
\]
For \(q>0\), fix an edge of \(J\) and count its intersections with
the others. Since its \(r\) vertices have degrees at most four,
\(q-1\le3r\). For an empty residual the same inequality holds. Thus
\[
 q\le3r+1. \tag{4}
\]

The degree-three lemma in the appendix implies
\[
 \tau(J)\le(q+r+4)/4. \tag{5}
\]
Indeed, choose a maximal matching of four-point incidence blocks
defined by degree-four vertices of \(J\), say \(a\) blocks. The
corresponding \(a\) vertices cover \(4a\) edges; the remaining
hypergraph has maximum degree at most three by maximality. Applying
the appendix to its \(q-4a\) edges gives
\(a+(q-4a+r+4)/4=(q+r+4)/4\). It remains \(r\)-uniform.
This argument also applies to an empty remaining hypergraph. From
(3)--(5),
\[
 m\ge5t-5r/4-q/4-5. \tag{6}
\]
If \(q\le5r/3\), this already gives
\(m\ge5t-5r/3-5\). The stronger analysis is needed only for
\(q\ge5r/3\).

## 4. A saving-sensitive count of linear four-blocks

Let \(x_i\) count vertices of residual degree \(i\), \(1\le i\le4\),
and put \(W=x_3/2+x_4\). Set
\[
 S=\sum_v\binom{d_J(v)}2=x_2+3x_3+6x_4.
\]
Since every edge pair intersects, the total intersection excess is
\[
 T=S-\binom q2=\sum_{\{A,B\}\subset E(J)}(|A\cap B|-1)\ge0. \tag{7}
\]
Incidence counting gives
\(x_1+2x_2+3x_3+4x_4=qr\).

Form the auxiliary four-uniform multihypergraph \(Q\) on the \(q\)
edge-points of \(J\): each degree-four vertex of \(J\) supplies one
four-point block. Retain repeated blocks initially. Let \(\lambda_{AB}\)
be the number of those blocks containing edge-points \(A,B\). Then
\(\lambda_{AB}\le|A\cap B|\), so
\[
 X:=\sum_{\{A,B\}}(\lambda_{AB}-1)_+\le T. \tag{8}
\]
Whenever some pair has current codegree at least two, delete one
block containing it. This lowers the integer \(X\) by at least one
and cannot increase any pair excess. After at most the original
\(X\) deletions, the retained four-uniform hypergraph \(Q'\) is
linear. It is also simple: two repeated four-blocks would have
codegree at least two. Write \(e=|E(Q')|\). The exact algebra gives
\[
\begin{aligned}
 e\ge x_4-T
 &=\binom q2-qr/2-3W+x_1/2\\
 &\ge\binom q2-qr/2-3W.
\end{aligned} \tag{9}
\]
The lower bounds may be negative; no positivity is assumed here.

Separately, selecting every degree-three and degree-four vertex of one
part covers disjoint edge sets. If their counts in part \(c\) are
\(a_c,b_c\), pairing the remaining edges gives
\[
 \tau(J)\le a_c+b_c+\lceil(q-3a_c-4b_c)/2\rceil
 \le q/2+1/2-a_c/2-b_c.
\]
The part savings have total \(W\), so one is at least \(W/r\).
Define a shifted cover saving
\[
 s=q/2+1-\tau(J).
\]
The pairing cover shows \(s\ge0\), and the part cover gives
\[
 W\le rs. \tag{10}
\]

## 5. A uniform matching/star bound, including small degrees

Fix \(\eta>0\) and take \(D_0\) from Input K. Let \(D\) be the
maximum degree of \(Q'\), taking \(D=0\) if it is empty.

If \(D\ge D_0\), Input K gives a matching of at least
\(e/((1+\eta)D)\) blocks. Their original defining vertices cover
four edges each, and pairing the rest gives
\[
 s\ge e/((1+\eta)D).
\]
For a second cover, take the \(D\) blocks through a maximum-degree
edge-point. Their other points are disjoint by linearity, so they
cover exactly \(1+3D\) original edges. The corresponding \(D\)
vertices together with a pairing of the remaining edges give
\[
 \tau(J)\le D+\lceil(q-1-3D)/2\rceil\le q/2-D/2,
 \qquad s\ge D/2.
\]
Multiplication of these nonnegative bounds yields
\(e\le2(1+\eta)s^2\).

If \(D<D_0\), incidence counting in \(Q'\) instead gives
\(4e\le qD<qD_0\). Consequently in both cases
\[
 e\le2(1+\eta)s^2+qD_0/4. \tag{11}
\]
This explicit small-degree case avoids applying an asymptotic theorem
outside its threshold.

Combining (9)--(11) gives, with
\(B=1/2+D_0/4\),
\[
 2(1+\eta)s^2+3rs\ge q(q-r)/2-qB. \tag{12}
\]

## 6. The 5/3 transition and all error terms

Assume \(q\ge5r/3\), and set
\[
 b=(1+\eta)s,\qquad \ell=3q/10-r/3,\qquad E=qB/(3r).
\]
All three are nonnegative. Since \(\eta,s,r\ge0\), (12) implies
\[
 2b^2+3rb\ge q(q-r)/2-3rE. \tag{13}
\]
The exact factorization
\[
 q(q-r)/2-(2\ell^2+3r\ell)
       =\frac{(3q-5r)(24q-35r)}{225}\ge0 \tag{14}
\]
is valid in this range: the second factor is at least \(5r\).
It follows that
\[
 b+E\ge\ell. \tag{15}
\]
For if \(b+E<\ell\), then \(\ell-b>E\) and
\[
 (2\ell^2+3r\ell)-(2b^2+3rb)
  =(\ell-b)(2(\ell+b)+3r)>3rE,
\]
contradicting (13)--(14).

From (4) and \(r\ge2\), \(q\le7r/2\). Therefore
\[
 0\le\ell\le r,\qquad 0\le E\le C:=7B/6. \tag{16}
\]
Equations (15)--(16) imply
\[
 s\ge\ell-\eta r-C. \tag{17}
\]
If \(s>r\), this is immediate. If \(s\le r\), use
\((1+\eta)s+E\le s+\eta r+C\) in (15).

Finally (3) and the definition of \(s\) give
\[
 m\ge5t-3q/2+5s-5
 \ge5t-\left(5/3+5\eta\right)r-5C-5. \tag{18}
\]
The \(q\) terms cancel exactly since \(5\ell=3q/2-5r/3\).
For \(q\le5r/3\), (6) gives a stronger bound than (18).
Taking \(\eta=\delta/5\) proves Theorem 1 with
\[
 C_\delta=5+\frac{35}{6}\left(\frac12+
                       \frac{D_0(\delta/5)}4\right). \tag{19}
\]
To obtain the final \(\varepsilon\) formulation, take
\(\delta=\varepsilon/2\) and then choose \(r\) so large that
\((C_\delta+5)/r\le\varepsilon/2\). This threshold is existential,
matching the nature of Input K. \(\square\)

## 7. Verification limits and next structural problem

The proof handles arbitrary part widths, repeated pair intersections,
empty residuals, and the small-degree alternative in the auxiliary graph.
Deleting repeated original edges preserves all hypotheses and the cover
number, so the bounds also apply to the number of distinct edges in a
hypergraph originally presented with multiplicities.

The exact checker verifies the identities coefficientwise and checks the
linearization procedure and its inequality on all intersecting binary-width
families in ranks two and three, and selected larger exact examples.
These are diagnostics. Lean checks the scalar transitions with explicit
hypotheses; it does not formalize the combinatorics or Input K. The written
proof, together with that precisely cited standard theorem, is the proof
of the universal result. No numerical experiment supplies a general step.

The transition here is \(q/r=5/3\). A further improvement requires
beating the simultaneous cover savings \(W/r\) and the linearized
matching/star bound. The method retains a precise obstruction: large
intersection excess destroys many four-blocks, whereas larger \(W\)
already saves cover vertices through the parts. Investigating which
extremal degree distributions and intersection patterns are actually
realizable is the next substantive step.

## References

[ABW] R. Aharoni, J. Barát and I. M. Wanless, *Multipartite hypergraphs
achieving equality in Ryser's conjecture*, Graphs and Combinatorics 32
(2016), 1--15, [DOI:10.1007/s00373-015-1575-9](https://doi.org/10.1007/s00373-015-1575-9),
[arXiv:1409.4833v2](https://arxiv.org/abs/1409.4833v2).

[S] V. Sivashankar, *An Improved Lower Bound for the Erdős--Lovász
Cover Number Problem*, [arXiv:2606.24878v2](https://arxiv.org/abs/2606.24878v2).
Its Section 4 supplies the peeling, linearization philosophy and
matching/star combination for the nonpartite class. Its Lemma 2 is
restated with proof in the appendix below. The saving-sensitive
estimate (9) and its coupling to the part cover are the contribution
of the present continuation.

[K] J. Kahn, *Asymptotically good list-colorings*, Journal of
Combinatorial Theory, Series A 73 (1996), 1--59.

[KKKMO] D. Y. Kang, T. Kelly, D. Kühn, A. Methuku and D. Osthus,
*Solution to a problem of Erdős on the chromatic index of hypergraphs
with bounded codegree*, Proceedings of the London Mathematical Society
129 (2024), no. 6, e70011, [arXiv:2110.06181](https://arxiv.org/abs/2110.06181).
Theorem 3.1 states Input K's parent theorem. The statement was checked
in the primary manuscript, including its rank and codegree hypotheses.

## Appendix. Full proof of the inherited degree-three lemma


**Lemma A (Sivashankar [S, Lemma 2]).** For an intersecting
\(r\)-uniform hypergraph \(L\) with \(q\) edges and maximum degree at
most three,
\[
 4\tau(L)\le q+r+4. \tag{15}
\]
The proof below restates its maximum-matching argument in our notation;
this lemma and its local coloured-graph claim are not claimed as our
contribution.

**Proof.** The empty case is immediate. Fixing one edge and counting its
intersections with all other edges gives
\[
 q-1\le\sum_{v\in e}(d(v)-1)\le2r,\qquad q\le2r+1. \tag{16}
\]
Treat the \(q\) edges as points. Each original vertex defines the block
of points containing it, of size at most three. Every point pair is
contained in a block. Take a maximum matching of the distinct
three-point blocks; let its size be \(s\), its covered points \(C\),
and its unmatched points \(U\), with \(|U|=u\). Thus \(q=3s+u\).
There is no three-block inside \(U\). The defining vertices of the
matching, followed by a pairing of \(U\), give a cover of size at most
\(s+\lceil u/2\rceil\). It suffices to show
\[
 r\ge u+s-2. \tag{17}
\]
Put \(\alpha=r-u-s+2\), an integer. If \(u=0\), (16) gives
\(\alpha\ge(r+5)/3>0\). Assume \(u>0\).

Select one witness vertex for each pair in \(U\). These witnesses are
distinct: witnesses for disjoint pairs cannot coincide because the
maximum degree is three; witnesses for overlapping pairs cannot
coincide because that would create a three-block inside \(U\).
Each selected witness contributes exactly two incidences with \(U\);
its block is the selected pair, possibly together with one point of
\(C\). The witnesses contribute \(u(u-1)\) such incidences in total.

We need the following coloured-graph observation, setting
\(K=\max\{12,u+4\}\). In a simple graph on \(u\) vertices, colour each
edge with one of at most three colours. If two disjoint edges never
have different colours, the sum of the three colour support sizes is
at most \(K\). Here a colour support consists of the vertices incident
with edges of that colour.

To prove the observation, suppose first that colour one contains two
disjoint edges \(e,f\), and put \(W=e\cup f\). Every edge of the other
colours must meet both, so its endpoints belong to \(W\). If no other
colour is used, the assertion holds. If their combined edge family has
no common vertex, each colour-one edge must also have both endpoints
in \(W\): an edge with an endpoint outside \(W\) would force its
other endpoint to be common to that family. All three support sizes
are then at most four, giving twelve. Otherwise the combined family
has a common vertex \(c\in W\). Its edges must join \(c\) to one of
the two endpoints of the edge among \(e,f\) not containing \(c\).
There are at most two such edges, and simplicity makes their combined
colour-support sum at most four. Adding the first support gives
\(u+4\).

Now assume each colour class is pairwise intersecting. A simple
pairwise-intersecting graph is a star or is contained in a triangle:
take two edges \(ab,ac\); any edge avoiding \(a\) must be \(bc\),
which in turn forces every edge into that triangle. If all supports
have size at most four, their sum is at most twelve. Otherwise one
class is a star with at least four leaves. Every edge of the other
colours must contain its centre, since two endpoints cannot meet four
distinct leaves. Simplicity ensures each noncentral vertex belongs
to at most one support. The centre belongs to at most three, giving
a sum at most \(u+2\). This proves the observation.

For each matching triple \(M_i\), form a coloured graph on \(U\):
the selected pair \(xy\) is given colour \(z\in M_i\) when its
witness block is \(\{x,y,z\}\). Two disjoint pairs with different
colours would allow replacing \(M_i\) by two disjoint three-blocks,
increasing the matching. Thus the observation applies. The colour
support sum counts the distinct pairs between \(U\) and \(M_i\)
covered by selected witnesses, so at most \(K\) such pairs are covered.
Across the \(s\) triples, at least \(3su-sK\) of the \(U\)--\(C\)
pairs are uncovered by selected witnesses.

For a nonselected vertex let \(a\) count its block points in \(U\)
and \(c\) those in \(C\). Since \(a+c\le3\), one has \(ac\le2a\).
All remaining pairs have nonselected witnesses, so their incidence
contribution to \(U\) is at least \((3su-sK)/2\). Counting the total
\(ur\) incidences with \(U\) yields
\[
 ur\ge u(u-1)+\frac{3su-sK}{2}. \tag{18}
\]
This reasoning remains valid if the displayed lower bound is negative.

Equation (16) with \(r=u+s-2+\alpha\) gives
\(s\le u-3+2\alpha\). Dividing (18) by \(u>0\) gives
\[
 \alpha\ge1-\frac{(K-u)s}{2u}. \tag{19}
\]
If \(\alpha<0\), its integrality implies \(\alpha\le-1\) and
\(0\le s\le u-5\), hence \(u\ge5\). As \(K-u\ge0\), (19) implies
\(\alpha\ge1-(K-u)(u-5)/(2u)\). This is greater than \(-1\).
Indeed, for \(5\le u\le8\) one has \(K=12\) and
\[
 4u-(12-u)(u-5)=u^2-13u+60
               =(u-13/2)^2+71/4>0.
\]
For \(u\ge8\), one has \(K=u+4\), giving \(-1+10/u>-1\).
This contradiction proves \(\alpha\ge0\), hence (17). Finally
\[
 4\tau(L)\le4s+4\lceil u/2\rceil
 \le4s+2u+2\le q+r+4.
\]
The lemma follows. \(\square\)

