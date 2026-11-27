# Power-of-two cycles for free abelian actions on three orbits

**Theorem.** A finite simple graph of minimum degree at least three, with
a free action of an abelian group on at most three vertex orbits,
contains a cycle of length \(4\), \(8\), or \(16\).
The upper bound \(16\) is sharp even for an infinite family of connected
cubic graphs with exactly three orbits under the displayed action.

This does **not** extend the vertex-wise assertion of the
[one- and two-orbit theorem](FactorErdosGyarfasAbelianTwoOrbits.md).
There is a connected cubic graph on 18 vertices with a free abelian
action on three orbits and an entire orbit on no cycle of any
power-of-two length.

These are restricted symmetry classes in the open Erdős–Gyárfás
problem. For context, [Ducoffe–Dumitru](https://arxiv.org/abs/2609.28594)
treat a variety of finite orders and properties of minimal
counterexamples, and [Ghaffari–Mostaghim](https://doi.org/10.1007/S00010-017-0518-3)
prove short power-of-two cycle results for certain Cayley graphs.
The symmetry assumption here does not require the graph itself to be
vertex-transitive.

## 1. Quotient reduction

Write \(G\) for the abelian group, additively. Choosing an origin in
each free orbit identifies it with a labelled copy of \(G\).
For two different orbits \(A,B\), every cross edge lies in a whole
translation matching \(A_v\sim B_{v+s}\) for some step \(s\).
For edges within an orbit the step set consists of nonzero elements
and is invariant under \(s\mapsto -s\).
We say an orbit has an internal edge when its step set is nonempty.

We can restrict to three orbits by the previous two-orbit theorem.
If some orbit has two internal steps \(x,y\) with \(y\ne\pm x\),
the commuting square \(0,x,x+y,y\) in that orbit settles the claim.
If an orbit pair has at least three distinct cross matchings, retain
three; they alone give a cubic two-orbit graph, and the previous theorem
applies. If two orbits have internal edges and are joined by at least
one matching, retain one matching and normalize its shift to zero.
An internal step \(x\) in the first, and \(y\) in the second, give a
square if \(y=\pm x\); otherwise the two internal steps commute to give
the simple cycle
\[
              A_0,A_x,B_x,B_{x+y},A_{x+y},A_y,B_y,B_0,A_0.
\]

Suppose next that two different orbit pairs each have two matchings.
They share an orbit, say \(A\), with other endpoints \(B,C\).
Normalize one matching to each of \(B\) and \(C\) to have shift zero.
The matchings give a two-edge path \(A_0\leadsto A_d\) through \(B\)
and a two-edge path \(A_0\leadsto A_e\) through \(C\), with \(d,e\ne0\).
If \(d=\pm e\), two such paths make a square. Otherwise, the
commuting rectangle on \(A\) using \(d,e\) lifts to an 8-cycle.
The two intermediate \(B\)-vertices differ by \(e\), and the two
intermediate \(C\)-vertices differ by \(d\), so the lift is simple.

After these cases, each pair has at most two matchings and at
most one pair is double. If none is double, every orbit has at
most two cross neighbors, so the minimum degree forces each to
have an internal edge. Either an adjacent internal pair settles the
claim, or the internal graphs each already have minimum degree three.
We may therefore name the unique double pair \(A,B\).
If the third orbit \(C\) is not joined to either, its internal
degree is at least three. If joined to both, both added matchings
are single and \(C\) has an internal step \(x\).
The two \(C\)-matchings can be normalized to shift zero, leaving
two distinct shifts \(a,b\) on \(A,B\).
A nonzero one, say \(a\), gives a length-three path
\(C_0,A_0,B_a,C_a\).
If \(a=\pm x\), close it by the internal edge to get a square.
Otherwise the two translates of that path joined by parallel
\(x\)-edges give a simple 8-cycle. Their intermediate vertices in
\(A,B\) are distinct since \(x\ne0\), and the four endpoints in
\(C\) are distinct since \(a\ne0,\pm x\).

The remaining case, after swapping the names \(A,B\) if necessary,
has the double \(A,B\) pair and one \(A,C\) matching only.
The minimum degree forces an internal step in \(B\) and at least
two internal neighbors per vertex of \(C\). If \(A\) also has
internal edges the adjacent internal-pair case applies.
If \(C\) has no step of order at least three, it has two distinct
involutions and an internal square. We can therefore choose a
\(C\)-step \(x\) of order at least three. In \(B\), choose a step
\(y\) of order at least three if possible; otherwise either two
distinct involutions give a square or there is just one involution
\(y\). Normalize the \(A,B\) matchings to shifts \(0,d\) and
the \(A,C\) matching to shift zero, with \(d\ne0\).

## 2. The remaining path-shaped quotient

The shift-zero matchings give disjoint links \(B_v,A_v,C_v\) of
length two. For positive integers \(a,b\), suppose the \(y\)-path
of length \(a\) and the \(x\)-path of length \(b\) have distinct
vertices. Write \(Y=ay,\ X=bx\).
If
\[
               X\notin\{jy:-a\le j\le a\},\qquad
               Y\notin\{jx:-b\le j\le b\},                 \tag{1}
\]
a simple cycle of length \(8+2(a+b)\) follows.
In \(B\), use the two length-\(a\) paths \(0\leadsto Y\) and
\(X\leadsto X+Y\); in \(C\), use the two length-\(b\) paths
\(0\leadsto X\) and \(Y\leadsto Y+X\). Join by the four links.
The conditions (1) separate each pair of paths, and the four
link coordinates are distinct.

If both \(x,y\) have order at least three, first try \(a=b=2\),
giving a 16-cycle if (1) holds. Otherwise one of
\(2x=\pm2y\), \(2x=\pm y\), \(2y=\pm x\) holds, since neither
\(2x\) nor \(2y\) is zero. If \(2x=\pm2y\), take paths of length
two in the two orbits to the same endpoint, joining by just two
links. This is a simple 8-cycle. For the other relations we may
interchange \(x,y\) in the shift-zero subgraph and change signs to
assume \(x=2y\). If \(r=\operatorname{ord}(y)\), then \(r=4\)
is impossible, and \(r=3,6\) give \(2x=\pm2y\).
At \(r=5\) the length-three \(y\)-path reaches \(-x\), and at
\(r=7\) the length-three \(x\)-path reaches \(-y\).
Together with the single step on the other orbit and two links
these give length 8. For \(r\ge8\), use \(a=1,b=3\): then
\(3x=6y\notin\{0,\pm y\}\) and \(y\notin\{jx:-3\le j\le3\}\),
since none of the corresponding nonzero integers is divisible
by \(r\). Both paths are simple. This yields 16.

If \(y\) is an involution and \(x\) has order at least four, again
try \(a=1,b=3\). Failure of (1) means that \(y=\pm jx\) for
\(1\le j\le3\); here \(3x\ne0\) by the order assumption.
Since \(y\) has order two, the only possibilities are
\(\operatorname{ord}(x)=4,\ y=2x\) or
\(\operatorname{ord}(x)=6,\ y=3x\).
The former has an internal square in \(C\), and the latter gives
an 8-cycle with the single \(y\)-edge, the three \(x\)-edges to
the same endpoint, and two links.

Finally let \(\operatorname{ord}(x)=3\) and \(\operatorname{ord}(y)=2\).
Then \(K=\langle x,y\rangle\cong\mathbb Z/3\times\mathbb Z/2\).
If \(d\in K\), either \(d=y\) and the two matchings between \(A,B\)
give a square, or \(2d=\pm x\) and \(d\) has order 3 or 6.
In the latter case the alternating path
\[
                        A_0,B_0,A_{-d},B_{-d},A_{-2d}
\]
is simple. Its endpoints are joined through \(C\) by the two-step
path around the other side of an \(x\)-triangle and by the two
\(A,C\) edges. This is an 8-cycle.
If \(d\notin K\), use the length-five path
\[
                P:\quad A_0,B_0,A_{-d},B_{-d},B_{-d+y},A_{-d+y}.
\]
Write \(t=-d+y\). Join \(P\) to its translate by \(x\) using the
length-three \(C\)-paths from \(A_0\) to \(A_x\) and from \(A_t\)
to \(A_{t+x}\). The result has length 16 and is simple:
\(K\) and \(-d+K\) are distinct cosets; within the second coset
\(0,y,x,y+x\) have distinct offsets. Thus \(P\) and its
translate share no vertex, and the two \(C\)-paths are in
different cosets. This exhausts the quotient reduction.

## 3. Sharpness and the vertex obstruction

For each integer \(m\ge5\), take
\[
       G=\mathbb Z/3\times\mathbb Z/m\times\mathbb Z/2,\qquad
       x=(1,0,0),\quad d=(0,1,0),\quad y=(0,0,1).
\]
Use the path-shaped quotient of §2, including both \(A,B\)
matchings. The graph is connected because the available paths
realize the generators \(x,d,y\); every orbit vertex has degree
three. By §2 it has a 16-cycle. There is no 4- or 8-cycle:
* A cycle involving \(C\) is either an \(x\)-triangle or has
  excursions from \(A\) through \(C\) back to \(A\).
  An excursion has length at least three and changes the first
  coordinate, while edges in \(A,B\) preserve it. Hence there
  cannot be just one excursion. Between any two consecutive
  excursions there must be a nonempty path in \(A,B\) of length
  at least two: an immediate next excursion would reuse the
  same \(A,C\) edge. Consequently such a cycle has length at least
  ten (or already at least nine with three excursions), not 4 or 8.
* Inside \(A,B\), suppress each degree-two \(A\)-vertex.
  For each fixed first coordinate the result is a prism with
  \(m\) positions on each of two rails; horizontal edges have
  weight two and vertical matching edges have weight one.
  With no vertical edges, a cycle has weight \(2m\).
  With two, its length is \(2+2(h_1+h_2)\), where the horizontal
  path lengths between the same two distinct positions are each
  one of \(h,m-h\). Their sum is even or \(m\), so cannot be
  1 or 3 for \(m\ge5\). Four or more vertical edges are disjoint,
  so there are at least as many horizontal edges and length at
  least 12.

For the vertex obstruction, take \(G=\mathbb Z/3\times\mathbb Z/2\)
with \(x=(1,0),\ d=y=(0,1)\) in the same path-shaped quotient.
This is a connected cubic graph with 18 vertices. At each first
coordinate \(i\), the \(A,B\) vertices form a \(K_{2,2}\) plus the
edge between the two \(B\) vertices. This cell meets \(C\) only at
the two \(C\)-vertices at \(i\), one on each of two triangles.
A simple cycle containing a \(C\)-vertex is either one of those
triangles or uses an even positive number of the cells as rungs
between the triangles. At each used cell, the path inside the
cell has length two or three, giving rung length four or five
including the two attachments. The cycle cannot reuse a cell,
since its two attachment edges have already been used.
There are only three cells, so exactly two are used. The two
horizontal paths have lengths one or two each, so the cycle
length is between ten and fourteen. Such a vertex is therefore
on no power-of-two cycle, although the \(K_{2,2}\) cells contain
squares.

The [exact verifier](verify_factor_erdos_gyarfas_three_orbits.py)
checks the quotient reduction and the finite small-order cases,
and independently replays examples of the sharp family and the
18-vertex obstruction. The proof above establishes the claims
for every finite abelian group without a bound on its order.
