# A 13/4 lower coefficient for partite intersecting cover numbers

Research note, 7 October 2026. This note gives complete written proofs.
The accompanying Lean file checks selected scalar steps, not the entire
hypergraph argument. No mathematical priority claim is made.

## 1. Definitions and results

A finite hypergraph is **simple** if its edges are distinct nonempty sets.
It is **intersecting** if every two distinct edges meet. An
**\(r\)-partite \(r\)-uniform** hypergraph has a specified partition of its
vertex set into \(r\) parts and each edge contains exactly one vertex in
each part. Isolated vertices can be discarded. Write \(m=|E(H)|\) and let
\(\tau(H)\) be the minimum size of a vertex set meeting every edge; the
empty hypergraph has cover number zero. Degrees always refer to the
currently specified hypergraph. All results below concern finite
hypergraphs and integer \(r\ge2\).

**Theorem 1 (partite cover inequality).** Every simple intersecting
\(r\)-partite \(r\)-uniform hypergraph satisfies
\[
 m\ge 5\tau(H)-\frac74r-5. \tag{1}
\]
Equivalently, \(\tau(H)\le m/5+7r/20+1\).

Define, whenever the class is nonempty,
\[
 f(r)=\min\{|E(H)|: H\text{ is simple, intersecting, }r\text{-partite}
 \ r\text{-uniform},\ \tau(H)\ge r-1\}.
\]
This definition does not assume the intersecting case of Ryser's
conjecture, \(\tau(H)\le r-1\). A counterexample with \(\tau(H)=r\)
also belongs to the class. Theorem 1 gives
\[
 f(r)\ge\left\lceil\frac{13}{4}r-10\right\rceil. \tag{2}
\]
For the hypothetical subclass with \(\tau(H)=r\), it gives
\(m\ge\lceil13r/4-5\rceil\). These inequalities do not settle Ryser's
conjecture or determine \(f(r)\).

The proof of Theorem 1 uses the maximum-degree-three cover lemma of
Sivashankar [S, Lemma 2]. For completeness its full proof is restated,
with attribution, in the appendix. We also prove a bound requiring none
of that lemma:

**Theorem 2 (independent elementary branch).** Under the same hypotheses,
\[
 m\ge5\tau(H)-\frac{289}{160}r-\frac{57}{16}-\frac{5}{32r}. \tag{3}
\]
Consequently
\[
 f(r)\ge\left\lceil\frac{511}{160}r-\frac{137}{16}
                   -\frac{5}{32r}\right\rceil. \tag{4}
\]
Its leading coefficient is \(511/160=3.19375\).

The contribution of this note is the partite residual estimate (6) and
its combination with the inherited residual estimate (12), after
degree-five peeling. The estimate (12) and this peeling framework also
appear in [S, Section 4]; they are not claimed as new here. In the sources
examined, Aharoni--Barát--Wanless [ABW, Corollary 2.6] prove
\(f(r)\ge293r/96+O(1)\), with a related degree-counting and greedy-cover
method. Our coefficient \(13/4\) is greater than \(293/96\). A finite
literature check is not a determination of priority.

## 2. Degree-five peeling

Put \(t=\tau(H)\). Repeatedly select a vertex of current degree at least
five, record it, and delete all current edges containing it. Stop when
the residual hypergraph \(J\) has maximum degree at most four. Let \(k\)
be the number of recorded vertices and \(q=|E(J)|\). Each deletion removes
at least five previously undeleted edges. The recorded vertices together
with any cover of \(J\) cover \(H\). Thus
\[
 m\ge q+5k,\qquad t\le k+\tau(J),\qquad
 m\ge q+5(t-\tau(J)). \tag{5}
\]
The last inequality remains valid when \(t-\tau(J)<0\). The residual
retains the original parts and uniformity and is intersecting unless
empty. For \(J=\varnothing\), set \(\tau(J)=0\); all residual bounds
below still hold.

## 3. A partite residual estimate

**Lemma 3.** If \(J\) is intersecting, \(r\)-partite, \(r\)-uniform
and has \(q\) edges and maximum degree at most four, then
\[
 \tau(J)\le\frac q2+\frac12-
                 \frac{q(q-r-1)}{8r}. \tag{6}
\]

**Proof.** Write \(x_i\) for the number of vertices of degree \(i\),
\(1\le i\le4\), and put \(W=x_3/2+x_4\). Incidence counting gives
\[
 x_1+2x_2+3x_3+4x_4=qr. \tag{7}
\]
Every unordered edge pair has at least one common vertex, so
\[
 \binom q2\le x_2+3x_3+6x_4
 =\frac{qr}{2}+4W-\frac{x_1+x_3}{2}
 \le\frac{qr}{2}+4W.
\]
In particular
\[
 W\ge\frac{q(q-r-1)}8. \tag{8}
\]
We do not presume that this right-hand side is positive.

In part \(c\), let \(a_c,b_c\) count vertices of degrees three and four.
The incident edge sets of distinct vertices of that part are disjoint,
since an edge has exactly one vertex in the part. Selecting all these
vertices therefore covers exactly \(3a_c+4b_c\) edges. Pair the remaining
edges arbitrarily and choose one common vertex per pair; for a singleton,
choose any of its vertices. These are vertices of the original \(J\),
regardless of its degrees after removing covered edges. This proves
\[
 \tau(J)\le a_c+b_c+
          \left\lceil\frac{q-3a_c-4b_c}{2}\right\rceil
 \le\frac q2+\frac12-\frac{a_c}{2}-b_c. \tag{9}
\]
The saving \(a_c/2+b_c\) has sum \(W\) across the \(r\) parts, so
some part has saving at least \(W/r\). Equations (8)--(9) give (6).
For \(q=0\), (6) is simply \(0\le1/2\). \(\square\)

Substituting (6) in (5) yields
\[
 m\ge 5t-\frac{17q}{8}+\frac{5q(q-1)}{8r}-\frac52.
                                                        \tag{10}
\]
This bound uses only the partite structure and elementary counting.
The identity
\[
\begin{aligned}
5t-\frac{17q}{8}+\frac{5q(q-1)}{8r}-\frac52
={}&5t-\frac{289r}{160}-\frac{57}{16}-\frac{5}{32r}\\
 &+\frac{5}{8r}\left(q-\frac{17r+5}{10}\right)^2
\end{aligned} \tag{11}
\]
proves Theorem 2, since \(r>0\). The appendix is not used in this proof.

## 4. A second residual estimate and the 13/4 coefficient

**Lemma 4 (Sivashankar [S, Section 4]).** If \(J\) is intersecting and \(r\)-uniform, with \(q\)
edges and maximum degree at most four, then
\[
 4\tau(J)\le q+r+4. \tag{12}
\]
No partite hypothesis is required for this lemma.

**Proof.** View edges of \(J\) as points and, for every degree-four
vertex, form its four-point incidence block. Choose a maximal matching
of these blocks, consisting of \(s\) disjoint blocks. Their defining
vertices cover exactly \(4s\) edges. On deleting those edges, no
degree-four vertex remains in the residual \(L\): such a vertex would
have a block disjoint from the matching and would augment it. Thus
\(\Delta(L)\le3\) and \(L\) has \(q-4s\) edges. Appendix Lemma A gives
\[
 \tau(J)\le s+\tau(L)
 \le s+\frac{q-4s+r+4}{4}=
                       \frac{q+r+4}{4}.
\]
This also covers an empty \(L\), with its cover number zero. \(\square\)

Combining Lemma 4 and (5) gives
\[
 m\ge 5t-\frac54r-\frac14q-5. \tag{13}
\]
If \(q\le2r\), (13) immediately gives (1). If \(q\ge2r\), use (10).
Subtracting its value at \(q=2r\) gives the exact factorization
\[
\begin{aligned}
 &\left(5t-\frac{17q}{8}+\frac{5q(q-1)}{8r}-\frac52\right)
 -\left(5t-\frac74r-\frac{15}{4}\right)\\
 &\hspace{18mm}=\frac{(q-2r)(5q-7r-5)}{8r}\ge0.
\end{aligned} \tag{14}
\]
Indeed \(5q-7r-5\ge3r-5\ge1\), since \(r\ge2\). Therefore in this
case \(m\ge5t-7r/4-15/4\), which is stronger than (1). This proves
Theorem 1 and its consequences. It uses no asymptotic threshold and no
edge-colouring theorem. \(\square\)

## 5. Boundaries, scope and further questions

For an empty hypergraph both theorems are immediate. Repeated edges may
be deleted without changing the cover number, intersection or partite
properties. Applying the simple result to the distinct edges gives the
same lower bounds for the number of distinct edges, and therefore also
for a larger count that includes multiplicities. No bound on the size of
the parts is assumed. The proof does not assume linearity (at most one
common vertex per edge pair); repeated intersection is permitted.

For small \(r\), the additive constants make (2) weak. In particular
this does not replace the repository's separate nineteen-edge necessary
bound for a rank-six Ryser counterexample. The new advance here is a
uniform leading coefficient for the nonempty extremal class
\(\tau\ge r-1\), not an existence result for \(\tau=r\).

The possible improvements are concrete. At \(q\approx2r\), the two
residual estimates meet at leading order. Raising the coefficient above
\(13/4\) by this route requires a stronger cover estimate there, or a
structural restriction on residuals surviving the peeling process.
The slack \((x_1+x_3)/2\) in the pair count is available when many
vertices have those degrees. Nearly sharp configurations would instead
concentrate incidence in degrees two and four and distribute their
four-blocks across the parts. Determining whether these configurations
can coexist with a large cover number is a substantive next problem.

## Appendix. The attributed degree-three lemma

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

## References and provenance

[ABW] Ron Aharoni, János Barát and Ian M. Wanless,
*Multipartite hypergraphs achieving equality in Ryser's conjecture*,
Graphs and Combinatorics **32** (2016), 1--15,
DOI [10.1007/s00373-015-1575-9](https://doi.org/10.1007/s00373-015-1575-9),
[arXiv:1409.4833v2](https://arxiv.org/abs/1409.4833v2).
In particular, Theorem 2.5 and Corollary 2.6 supply the comparison bound.

[S] Varun Sivashankar, *An Improved Lower Bound for the Erdős--Lovász
Cover Number Problem*,
[arXiv:2606.24878v2](https://arxiv.org/abs/2606.24878v2), 29 July 2026.
Lemma 2 supplies the degree-three residual inequality and its proof.
Theorem 1(i) states \(g(r)\ge3r-4\) for the different, nonpartite
class with \(\tau=r\). Its asymptotic Theorem 1(ii) uses an additional
edge-colouring theorem; neither that theorem nor its formal assumptions
are needed here.

The dated repository literature report records the limited search scope.
No OpenAI/math theorem is needed for either theorem of this note.
The new partite estimate, its independent consequence and the stronger
combination are written explicitly. Lemma 4 and the appendix identify the
inherited estimates and proofs separately.
