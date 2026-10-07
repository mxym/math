# Intersection excess controls partite cover numbers

Research continuation, 7 October 2026. This develops the same partite
cover-number programme beyond its finite \(13/4\) and asymptotic
\(10/3\) bounds. The new result records the intersection structure,
not only another numerical bound.

## 1. Definitions and main theorem

Let \(H\) be a finite simple intersecting \(r\)-partite \(r\)-uniform
hypergraph, \(r\ge2\). Its edges contain exactly one vertex in each of
the specified \(r\) parts. Write \(m=|E(H)|\), \(t=\tau(H)\), and
define its **intersection excess** by
\[
 I(H)=\sum_{\{A,B\}\subset E(H)}(|A\cap B|-1)\ge0. \tag{1}
\]
The sum is over unordered pairs of distinct edges. In particular
\(I(H)=0\) precisely when every distinct edge pair meets in exactly
one vertex. This is the linear intersecting class. For an empty family,
both the cover number and the excess are zero.

Put
\[
 d=\frac{27-5\sqrt{17}}{20},\qquad
 a=5d=\frac{27-5\sqrt{17}}4,\qquad
 c=5-a=\frac{5\sqrt{17}-7}{4}>\frac{10}{3}. \tag{2}
\]
The strict comparison follows from \(15\sqrt{17}>61\), verified by
squaring positive sides: \(225\cdot17=3825>3721=61^2\).

**Theorem 1 (cover number with intersection-excess penalty).** For every
\(\delta>0\) there is a finite constant \(C_\delta\), independent of
\(r,H\), such that
\[
 m\ge5\tau(H)-(a+\delta)r-\frac{10I(H)}r-C_\delta. \tag{3}
\]
Equivalently this bounds \(\tau(H)\) by
\(m/5+(d+\delta/5)r+2I(H)/r+C_\delta/5\).

**Corollary 2 (linear and near-linear families).** Suppose
\(r_j\to\infty\), \(H_j\) satisfies the hypotheses,
\(\tau(H_j)\ge r_j-1\), and \(I(H_j)=o(r_j^2)\). Then
\[
 \liminf_j\frac{|E(H_j)|}{r_j}\ge
             c=\frac{5\sqrt{17}-7}4=3.403882\ldots. \tag{4}
\]
In particular, the minimum edge count \(f_{\rm lin}(r)\) under the
additional linearity hypothesis satisfies
\(f_{\rm lin}(r)\ge(c-\varepsilon)r\) for every fixed
\(\varepsilon>0\) and all sufficiently large ranks at which its
defining class is nonempty.

**Corollary 3 (quadratic excess required near the 10/3 coefficient).**
If instead \(|E(H_j)|/r_j\to10/3\) and
\(\tau(H_j)\ge r_j-1\), then
\[
 \liminf_j\frac{I(H_j)}{r_j^2}\ge
           \frac{15\sqrt{17}-61}{120}>0. \tag{5}
\]
This is a necessary lower bound supplied by the proof;
optimality or existence of such sequences is not asserted.

These statements do not solve Ryser's conjecture. The class
\(\tau\ge r-1\) includes both equality examples and hypothetical
\(\tau=r\) counterexamples. No existence for every rank, numerical
asymptotic threshold or priority is claimed. The finite literature screen
is recorded separately. The new step here is the simultaneous weighted
linearization of degree-three and degree-four blocks, and its coupling
to the part cover and a degree-four star bound. The peeling, pair-excess
deletion framework and matching/star tools have explicit predecessors
in Sivashankar [S, Section 4].

## 2. Attributed inputs

We use Kahn's small-codegree edge-colouring theorem in the form stated
in [KKKMO, Theorem 3.1]. For every \(\eta>0\) there is an integer
\(D_0\ge1\) such that every linear hypergraph of rank at most four
and maximum degree \(D\ge D_0\) admits a proper edge-colouring with
at most \((1+\eta)D\) colours. Here rank is maximum edge size;
linearity means codegree at most one. This follows by fixing rank four
in Kahn's theorem and choosing \(D_0\) so that its small-codegree
condition includes codegree one. It applies both to four-uniform and
mixed three/four-uniform hypergraphs used below. We do not re-prove
this standard theorem or formalize it in Lean.

We also use Sivashankar's degree-three lemma: if \(L\) is intersecting
and \(r\)-uniform, has \(h\) edges and maximum degree at most three,
then \(4\tau(L)\le h+r+4\). Its full attributed proof is included
in the appendix. No OpenAI/math theorem is used.

## 3. Residual notation and exact counts

Peel vertices of current degree at least five, recording each selected
vertex and deleting all its current incident edges. Stop at a residual
\(J\) of maximum degree at most four. If \(k\) vertices were selected
and \(q=|E(J)|\), then
\[
 m\ge q+5k,\quad t\le k+\tau(J),\quad
 m\ge q+5(t-\tau(J)). \tag{6}
\]
Fixing one residual edge and counting its intersections gives
\(q\le3r+1\); this also holds for an empty residual. Thus
\[
 q\le7r/2 \quad(r\ge2). \tag{7}
\]
The intersection excess of the residual is
\(T=I(J)\le I(H)\), because the sum omits some nonnegative summands
and intersections themselves do not change under edge deletion.

Write \(x_i\) for its degree-\(i\) vertex counts, and put
\(W=x_3/2+x_4\), \(K=q(q-r)/2\). Incidence and pair counting give
\[
 x_1+2x_2+3x_3+4x_4=qr,\qquad
 T=x_2+3x_3+6x_4-\binom q2.
\]
Consequently
\[
 x_4+3W=K-q/2+T+x_1/2\ge K-q/2+T. \tag{8}
\]
Set \(s=q/2+1-\tau(J)\). Pairing residual edges proves \(s\ge0\).
Selecting the degree-three/four vertices of a single part, followed by
pairing the remaining edges, saves \(a_c/2+b_c\) in that part. Their
sum across parts is \(W\), hence
\[
 W\le rs. \tag{9}
\]
This is the same part-cover argument as in the preceding notes: the
incident edge sets are disjoint within a part, and
\(\lceil n/2\rceil\le n/2+1/2\) for integer \(n\ge0\).

## 4. Degree-four linearization and its uniform bound

View the edges of \(J\) as points. A residual vertex defines its
incidence block. In the multihypergraph of degree-four blocks, pair
codegrees are bounded by the original intersection sizes. Therefore
their total positive pair excess is at most \(T\). Delete a block
containing a pair of codegree at least two until all codegrees are at
most one. Each deletion lowers that integer excess by at least one;
at most \(T\) blocks are deleted. The retained simple linear
four-uniform hypergraph has at least \(x_4-T\) blocks.

For a retained graph of maximum degree \(D\ge D_0\), Kahn's colouring
gives a matching of at least \(e/((1+\eta)D)\) blocks, so
\(s\ge e/((1+\eta)D)\). A star through a maximum-degree point
has exactly \(1+3D\) points by linearity. Its defining vertices and
a pairing of the rest give \(s\ge D/2\). Thus
\(e\le2(1+\eta)s^2\). For \(D<D_0\), incidence counting instead
gives \(4e\le qD_0\). These include empty retained graphs. In either
case
\[
 x_4\le T+2(1+\eta)s^2+qD_0/4. \tag{10}
\]
Combining (8)--(10), with \(B_0=1/2+D_0/4\), yields
\[
 K\le2(1+\eta)s^2+3rs+qB_0. \tag{11}
\]
The \(T\) terms cancel in this first inequality.

## 5. Weighted three/four-block linearization

Now form the mixed multihypergraph of all degree-three and degree-four
incidence blocks. Give the former weight \(1/2\) and the latter weight
one. The total weight is \(W\). Its pair excess is at most \(T\),
again because its pair codegrees are at most \(|A\cap B|\). The same
deletion procedure produces a simple linear rank-four hypergraph
\(G\), whose edges have sizes three or four. Each deletion loses weight
at most one, so its total retained weight \(U\) satisfies
\[
 U\ge W-T. \tag{12}
\]
The right-hand side need not be positive. Let \(D\) be the maximum
degree of \(G\). Through one point, all other points in its incident
blocks are disjoint, and each block supplies at least two such points.
Therefore \(2D\le q-1\) whenever \(G\) is nonempty.

If \(D\ge D_0\), a proper colouring with at most \((1+\eta)D\)
colours has a colour class of weight at least \(U/((1+\eta)D)\).
It is a matching. If it contains \(a_3\) three-blocks and \(a_4\)
four-blocks, its defining vertices and a pairing cover give
\[
 \tau(J)\le a_3+a_4+
       \lceil(q-3a_3-4a_4)/2\rceil
 \le q/2+1/2-a_3/2-a_4.
\]
Hence \(s\) is at least that colour-class weight, and
\(U\le(1+\eta)Ds\le(1+\eta)qs/2\).
If \(D<D_0\), total weight is at most the number of blocks, and
each block has at least three points. Thus \(U\le qD_0/3\).
Both cases, including empty \(G\), give
\[
 W\le T+(1+\eta)qs/2+qD_0/3. \tag{13}
\]
Use (8), (10) and (13) to obtain the second inequality
\[
 K\le2(1+\eta)s^2+\tfrac32(1+\eta)qs+3T+qB_1,
 \qquad B_1=1/2+5D_0/4. \tag{14}
\]

## 6. A piecewise scalar certificate and the defect penalty

The constant \(d\) in (2) obeys
\[
 3/10\le d\le1/3,\quad
 d^2-27d/10+19/25=0,\quad d^2\le1/9<13/100. \tag{15}
\]
For the lower interval use \(\sqrt{17}\le21/5\); for the upper
interval use \(\sqrt{17}\ge61/15\); both follow by squaring positive
sides. Substitution verifies the quadratic identity.

If \(q\le r\), the inherited degree-three lemma, applied after a
maximal matching of four-blocks, gives
\(\tau(J)\le(q+r+4)/4\). Equation (6) then yields
\(m\ge5t-5r/4-q/4-5\ge5t-3r/2-5\). As \(5d\ge3/2\), this
is stronger than (3). Thus assume \(q\ge r\).

Set
\[
 b=(1+\eta)s,\quad\kappa=\min\{r,q/2\},\quad
 L=3T+qB_1,\quad E=2L/(3r),\quad \ell=3q/10-dr.
\]
Since \(b\ge s\ge0\), (11) and (14) imply
\[
 2b^2+3\kappa b\ge K-L. \tag{16}
\]
Also \(\kappa\ge r/2\) and \(E\ge0\). Two exact factorizations,
using the quadratic identity in (15), prove
\[
 K\ge2\ell^2+3\kappa\ell. \tag{17}
\]
For \(r\le q\le2r\), the difference equals
\[
 (2r-q)(13q/100-d^2r)\ge0.
\]
For \(q\ge2r\), it equals
\[
 (q-2r)\left(8q/25+(6d/5-19/25)r\right)\ge0.
\]
The second factor here is at least \((6d/5-3/25)r\ge6r/25\).
The first factorization uses \(q\ge r\) and \(d^2<13/100\).

It follows that \(b+E\ge\ell\). Otherwise \(\ell-b>E\), with
\(\ell>b\ge0\), and
\[
 (2\ell^2+3\kappa\ell)-(2b^2+3\kappa b)
 = (\ell-b)(2(\ell+b)+3\kappa)
 >3\kappa E\ge(3r/2)E=L,
\]
contradicting (16)--(17). This also handles a negative \(\ell\),
when the asserted lower bound is immediate.

By (7), \(\ell\le r\) and
\(E\le2T/r+7B_1/3\). If \(s\le r\), the inequality
\((1+\eta)s+E\ge\ell\) implies
\(s\ge\ell-\eta r-E\); if \(s>r\), that conclusion follows from
\(\ell\le r\) and \(E\ge0\). Hence (6) gives
\[
\begin{aligned}
 m&\ge5t-3q/2+5s-5\\
  &\ge5t-(5d+5\eta)r-10T/r-35B_1/3-5\\
  &\ge5t-(5d+5\eta)r-10I(H)/r-35B_1/3-5.
\end{aligned} \tag{18}
\]
Set \(\eta=\delta/5\). This proves Theorem 1 with the finite,
possibly ineffective constant
\[
 C_\delta=5+\frac{35}{3}\left(\frac12+
                              \frac{5D_0(\delta/5)}4\right). \tag{19}
\]
An empty original hypergraph satisfies the result immediately.

For Corollary 2, divide (3) by \(r_j\), use
\(5\tau(H_j)/r_j\ge5-5/r_j\), take the lower limit, and let
\(\delta\downarrow0\). For Corollary 3, the same inequality gives
\[
 \frac{10I(H_j)}{r_j^2}\ge
     c-\delta-\frac{|E(H_j)|}{r_j}-\frac{C_\delta+5}{r_j}.
\]
Take the lower limit and then \(\delta\downarrow0\), noting
\((c-10/3)/10=(15\sqrt{17}-61)/120\). \(\square\)

## 7. Verification and contribution limits

The new global excess penalty follows from weighted block matching, not
from a finite search. The exact checker replays both block deletions and
weighted matching covers, and checks the quadratic-field identities
without floating point. Lean formalizes scalar identities and inequalities
under their explicit hypotheses. The finite combinatorics, Kahn's theorem
and the coloured-graph classification in the appendix remain written
arguments. No complete Lean formalization or external human review is
claimed. Priority has not been determined.

The result separates possible near-minimal families from the linear
regime through an explicit intersection-excess obstruction. It does not
classify the nonlinear configurations or prove the constants optimal.
Those are the remaining mathematical gaps.

## References

[S] V. Sivashankar, *An Improved Lower Bound for the Erdős--Lovász
Cover Number Problem*, [arXiv:2606.24878v2](https://arxiv.org/abs/2606.24878v2).
The degree-three lemma is Lemma 2; Section 4 supplies the existing peeling,
pair-excess linearization and matching/star framework. The present weighted
three/four-block estimate and its global defect consequence are distinguished
from that framework.

[K] J. Kahn, *Asymptotically good list-colorings*, Journal of Combinatorial
Theory, Series A 73 (1996), 1--59.

[KKKMO] D. Y. Kang, T. Kelly, D. Kühn, A. Methuku and D. Osthus,
*Solution to a problem of Erdős on the chromatic index of hypergraphs with
bounded codegree*, Proceedings of the London Mathematical Society 129
(2024), no. 6, e70011, [arXiv:2110.06181](https://arxiv.org/abs/2110.06181),
Theorem 3.1. Its rank bound covers mixed three/four-block hypergraphs.

[ABW] R. Aharoni, J. Barát and I. M. Wanless, *Multipartite hypergraphs
achieving equality in Ryser's conjecture*, Graphs and Combinatorics 32
(2016), 1--15, [arXiv:1409.4833v2](https://arxiv.org/abs/1409.4833v2),
[DOI:10.1007/s00373-015-1575-9](https://doi.org/10.1007/s00373-015-1575-9).
The directly applicable general coefficient there is \(293/96\).

## Appendix. Full proof of the inherited degree-three lemma



**Lemma A (Sivashankar [S, Lemma 2]).** For an intersecting
\(r\)-uniform hypergraph \(L\) with \(q\) edges and maximum degree at
most three,
\[
 4\tau(L)\le q+r+4. \tag{A.1}
\]
The proof below restates its maximum-matching argument in our notation;
this lemma and its local coloured-graph claim are not claimed as our
contribution.

**Proof.** The empty case is immediate. Fixing one edge and counting its
intersections with all other edges gives
\[
 q-1\le\sum_{v\in e}(d(v)-1)\le2r,\qquad q\le2r+1. \tag{A.2}
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
 r\ge u+s-2. \tag{A.3}
\]
Put \(\alpha=r-u-s+2\), an integer. If \(u=0\), (A.2) gives
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
 ur\ge u(u-1)+\frac{3su-sK}{2}. \tag{A.4}
\]
This reasoning remains valid if the displayed lower bound is negative.

Equation (A.2) with \(r=u+s-2+\alpha\) gives
\(s\le u-3+2\alpha\). Dividing (A.4) by \(u>0\) gives
\[
 \alpha\ge1-\frac{(K-u)s}{2u}. \tag{A.5}
\]
If \(\alpha<0\), its integrality implies \(\alpha\le-1\) and
\(0\le s\le u-5\), hence \(u\ge5\). As \(K-u\ge0\), (A.5) implies
\(\alpha\ge1-(K-u)(u-5)/(2u)\). This is greater than \(-1\).
Indeed, for \(5\le u\le8\) one has \(K=12\) and
\[
 4u-(12-u)(u-5)=u^2-13u+60
               =(u-13/2)^2+71/4>0.
\]
For \(u\ge8\), one has \(K=u+4\), giving \(-1+10/u>-1\).
This contradiction proves \(\alpha\ge0\), hence (A.3). Finally
\[
 4\tau(L)\le4s+4\lceil u/2\rceil
 \le4s+2u+2\le q+r+4.
\]
The lemma follows. \(\square\)

