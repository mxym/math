# Fractional covering spectra and stability of intersecting extremizers

mxym/math research project. AI-assisted manuscript, 7 October 2026.

We determine the sharp asymptotic fractional vertex-cover frontier at every
finite edge/rank ratio, characterize the near-extremizers at its integer
design boundaries, and determine the entire frontier with any fixed matching
bound. A finite allocation formula also identifies the limit when the matching
number diverges. The finite upper bounds require no linearity or small-codegree
assumption. The near-design statement requires uniform edges; that hypothesis
is retained throughout Part D. These are fractional assertions except for the
explicitly designated integer-cover corollaries.

The paper has three connected parts, each with a complete proof. Definitions,
theorems, equations and sections are prefixed F, D or S. References within a part
use its own prefix; the common finite LP duality argument is included rather
than left to an external computational solver. The repeated local conventions
make the changes in hypotheses visible. Part S needs an anchored inequality,
not a partition into intersecting subfamilies: arbitrary pairs of edges in an
anchor group may be disjoint. Its common-rank constructions work at every
sufficiently large integer rank, which is essential for both sharpness claims.

Classical inputs are Wilson's fixed-block design existence theorem and Kahn's
small-intersection covering corollary, stated precisely in the proof. They enter
the sharpness constructions and designated integer-cover corollaries, not the
finite signed-counting upper bounds. Füredi--Kahn--Seymour is prior context and
is not claimed to be resolved in its general weighted nonuniform formulation.
The results neither settle Ryser's conjecture nor Kahn's triple-intersection
question. An exact finite maximum for every arithmetic pair of rank and edge
count is also outside the statements.

The accompanying reproduction guide pins the three source papers and their
checkers. Lean establishes the indicated finite incidence/anchor/extraction
lemmas, not Wilson's theorem, the LP duality appendix, all constructions, or the
asymptotic spectrum. The written proofs supply these remaining steps.
Literature comparison is provisional; no historical priority claim is made.


## Part F: The intersecting frontier

## F.1. Definitions and the finite bound

Let H be a finite simple intersecting hypergraph with \(m\ge1\) nonempty
edges of size at most r, where \(r\ge2\) is an integer. Its fractional vertex
cover number \(\tau^*(H)\) is the minimum sum of nonnegative vertex
weights whose sum on every edge is at least one. By finite LP duality,
it equals the maximum \(Y=\sum_E y_E\) over weights satisfying
\[
                y_E\ge0,\qquad\sum_{E\ni v}y_E\le1
                  \quad\hbox{for every vertex }v.            \tag{F.1}
\]
Appendix F.A specifies the finite duality fact used. Every edge is
nonempty, so feasible edge weights lie in [0,1] and an optimum exists.

**Theorem F.1 (finite bound, without additional intersection restrictions).** For
every integer \(k\ge2\),
\[
 \boxed{\displaystyle
 \tau^*(H)\le\max\left\{\frac{(k-1)r+1}{k},\frac{m}{k+1}\right\}.}
                                                               \tag{F.2}
\]
For \(m\ge2\) we also have \(\tau^*(H)\le m/2\); for \(m=1\) the value is one.
No partite, linearity, uniformity, or small-codegree condition is needed.
The finite maximum in (F.2) is not asserted to be the exact optimum for
every arithmetic pair (r,m).

## F.2. A signed bin inequality

**Lemma F.2.** Suppose \(k\ge2\), \(1/(k+1)<b\le1/k\), and a bin contains
\(\ell\in\mathbb Z_{\ge0}\) weights in [0,b] of total \(W\le1-b\). Then
\[
 W-(1-kb)\ell\le(k-1)\{(k+1)b-1\}.                          \tag{F.3}
\]
This is an inequality about the weights assigned to the bin, not
all edges incident at the bin's vertex.

**Proof.** Put \(p=(k+1)b-1>0\) and \(B=1-kb\ge0\).
If \(\ell\le k-1\), use \(W\le\ell b\) to get
\[
 W-B\ell\le\ell\{(k+1)b-1\}\le(k-1)p.
\]
If \(\ell\ge k\), use \(W\le1-b\) and \(B\ge0\) to get
\[
 W-B\ell\le1-b-kB
              =(k^2-1)b-(k-1)=(k-1)p.
\]
The empty bin belongs to the first case. This proves the lemma.
The signed cost is essential: individual bin scores \(W-B\ell\) need
not be positive. We will sum them only over a genuine partition.

## F.3. Proof of the finite theorem

Fix any feasible vector (F.1), choose a maximum-weight edge P, and
write \(b=y_P\), \(Y=\sum_Ey_E\). Choose any v in P; feasibility gives
\(b\le1\). Nonnegative weights and intersectingness imply the weighted-star
inequality
\[
 Y-b\le\sum_{v\in P}\sum_{E\ne P,\ v\in E}y_E
                         \le|P|(1-b)\le r(1-b).
 \qquad Y\le r-(r-1)b.                                     \tag{F.4}
\]
Multiple intersections do not invalidate this inequality.

Fix k and put \(g=(k-1)r+1\). If \(b\le1/(k+1)\), then
\(Y\le m/(k+1)\), proving (F.2). If \(b>1/k\), (F.4) gives
\(Y\le r-(r-1)/k=g/k\), again proving (F.2).

It remains to consider \(1/(k+1)<b\le1/k\). For every edge E other
than P, choose **one** vertex \(v(E)\in E\cap P\). This is possible
by intersectingness. Assign its weight \(y_E\) to that vertex's bin.
Each edge is assigned exactly once, even if it meets P repeatedly.
At a vertex v of P the assigned weights are a subset of the other
incident edge weights; therefore their total \(W_v\) is at most 1-b.
Each individual weight is at most b. Let \(\ell_v\) count the assigned
edges. We have the exact partition identities
\[
                \sum_{v\in P}W_v=Y-b,\qquad
                \sum_{v\in P}\ell_v=m-1.                    \tag{F.5}
\]
Lemma F.2 can now be summed, even though its summands have signs:
\[
       (Y-b)-(1-kb)(m-1)
          \le |P|(k-1)\{(k+1)b-1\}
          \le r(k-1)\{(k+1)b-1\}.                          \tag{F.6}
\]
The last factor is positive. Rearranging yields
\[
          Y\le m-g+b\{(k+1)g-km\}.                        \tag{F.7}
\]
The right side is affine in b. At the endpoints b=\(1/(k+1)\) and
b=\(1/k\) its values are respectively \(m/(k+1)\) and \(g/k\). Therefore (F.7)
is at most their maximum throughout the closed interval. This
proves (F.2) for every feasible vector and hence for the optimum.

For \(m\ge2\), each pair of distinct edges has a common vertex, so
\(y_E+y_F\le1\). Summing over all unordered edge pairs gives
\((m-1)Y\le\binom m2\), hence \(Y\le m/2\). For \(m=1\), a unit vertex weight
and a unit dual edge weight show \(\tau^*=1\).

This upper-bound proof uses no design theorem, rounding result,
numerical experiment or claim in OpenAI/math.

## F.4. The exact limiting curve

Define the continuous nondecreasing function
\[
 \psi(c)=c/2\quad(0\le c\le1),\qquad
 \psi(c)=\max\left\{\frac{a}{a+1},\frac{c}{a+2}\right\}
               \quad(a\le c\le a+1,\ a=1,2,\ldots).         \tag{F.8}
\]
The formulas agree at integer endpoints. On [a,\(a+1\)] the switch is
\(c=a(a+2)/(a+1)=a+1-1/(a+1)\): a plateau is followed by a linear
ramp. In particular \(\psi(3/2)=1/2\), \(\psi(7/4)=7/12\), and
\(\psi(5/2)=2/3\).

**Theorem F.3 (sharp frontier at every real ratio).** If \(r_j\) tends to
infinity, \(H_j\) is as in Theorem F.1, and \(m_j/r_j\to c<\infty\), then
\[
                   \limsup_j\tau^*(H_j)/r_j\le\psi(c).       \tag{F.9}
\]
For every real \(c\ge0\) there is a sequence of **simple intersecting
\(r_j\)-uniform** hypergraphs with \(m_j/r_j\to c\) for which
\[
                         \tau^*(H_j)/r_j\to\psi(c).         \tag{F.10}
\]
Thus the same sharp limiting curve holds whether uniformity is
required or only the rank bound is imposed.

**Upper bound.** For \(c\ge1\) choose the fixed \(k=a+1\) corresponding to
an interval [a,\(a+1\)] containing c, and apply (F.2). Dividing by \(r_j\)
and taking limsup gives (F.9). At shared endpoints either formula
works. For \(c\le1\) use the pair bound, with the single-edge cases
contributing at most \(1/r_j\). This also handles \(c=0\).

The next section proves (F.10) and states every imported theorem.

## F.5. Sharpness and classical inputs

A Steiner 2-(v,k,1) design is a family of k-point blocks on a
v-point set, such that every pair of distinct points belongs to
exactly one block. Each point belongs to
\(r_0=(v-1)/(k-1)\) blocks. For replication at least two, its incidence dual has v distinct edges
of size \(r_0\) and is simple and intersecting, and every active vertex has
degree k. Uniform dual weights \(1/k\) and uniform primal weights
\(1/r_0\) give matching values \(v/k\), since there are \(v r_0/k\) blocks.
Thus its fractional cover number is exactly \(v/k\).

**Input W (Wilson 1975, fixed-block design existence).** For every
fixed \(k\ge2\) and all sufficiently large v satisfying
\[
             k-1\mid v-1,\qquad k(k-1)\mid v(v-1),          \tag{F.11}
\]
a Steiner 2-(v,k,1) design exists. In particular one can take an
unbounded sequence \(v=1+k(k-1)N\), with replication \(r_0=kN\).
This classical existence theorem is used only for sharpness,
not for the finite upper bound.

**Input K (Kahn 1994, Corollary F.5.4, printed p.140).** For fixed \(C>0\),
intersecting \(r\)-uniform families with at most \(Cr\) edges and maximum
distinct-edge intersection \(o(r)\) have integer cover number at most
\((C/(C+1)+o(1))r\). Again this is used only in a construction step.

### F.5.1 Plateau construction

Fix \(a\ge1\) and \(k=a+1\). Apply Input W and let \(H_0\) be a design dual
with \(r_0\to\infty\) and \(v=(k-1)r_0+1\). It is linear, with
\(v/r_0\to a\). Applying Input K first with \(C=a+\eta\) and then decreasing
\(\eta\) to zero gives an integer cover \(C_0\) of size
\[
                  |C_0|\le(a/(a+1)+o(1))r_0<r_0           \tag{F.12}
\]
for all sufficiently large \(r_0\). \(C_0\) is nonempty. All its vertices
are original design blocks. The number of original vertices is
\(n_0=v r_0/k=\Theta(r_0^2)\).

For any fixed \(c\ge a\) choose \(L=\max\{0,\lfloor c r_0\rfloor-v\}\).
This is \(O(r_0)\). Enlarge \(C_0\) to a fixed set T of \(r_0-1\) original
vertices. For each of L distinct original vertices p outside T,
add the edge \(T\cup\{p\}\), avoiding edges already in \(H_0\). There
are \(n_0-r_0+1\) candidates and at most v forbidden originals,
so enough remain. The new edges are distinct \(r_0\)-sets; they meet
one another through T and meet every original edge through \(C_0\).
Thus the enlarged hypergraph is simple and intersecting.

Put dual weight \(1/k\) on the old edges and zero on the new ones.
It remains feasible. Put primal weight \(1/r_0\) on every original
vertex; every edge, including every new one, has exactly \(r_0\)
original vertices, so its primal sum is one. Both objectives
are \(v/k\). Therefore the enlarged family has exactly
\[
                    \tau^*=v/k,\qquad m=v+L,
       m/r_0\to c,\qquad\tau^*/r_0\to a/(a+1).             \tag{F.13}
\]
No explicit algorithm to find Wilson's designs or \(C_0\) is asserted;
their existence follows from the two named published inputs.
For prime-power k, affine-line designs give explicit design instances.

### F.5.2 Linear-ramp construction

For c in (0,1] use the complete pair design on v points (block size
two). For c in [a,\(a+1\)], \(a\ge1\), use Input W with block size \(a+2\).
Let \(r_0\) be its replication and set \(r=\lceil v/c\rceil\).
In both cases \(r\ge r_0\). Pad each original edge with \(r-r_0\) distinct
private vertices, different across edges. Uniformity becomes r;
all original pair intersections remain exactly one, so simplicity
and intersectingness are preserved.

Keep uniform dual weights \(1/k\), where k is the block size, and
primal weights \(1/r_0\) on old vertices and zero on the padding.
These are feasible with equal value \(v/k\). Hence
\[
                  m/r\to c,\qquad\tau^*/r\to c/k.           \tag{F.14}
\]
This gives c/2 below one and c/(\(a+2\)) on [a,\(a+1\)]. Choose between
(F.13) and (F.14) according to the larger term in (F.8), proving
sharpness. For \(c=0\) take one r-edge with \(r\to\infty\); its value
one divided by r tends to zero. Theorem F.3 is proved.

### F.5.3 Explicit partite sharpness by shifting a partial pencil

The preceding all-integer construction inputs are unnecessary when
the block size is a prime power. We now give an explicit construction
that additionally preserves a partition into as many parts as the rank.

**Proposition F.3.1.** Every plateau for which \(a+1\) is a prime power,
and every ramp for which \(a+2\) is a prime power, is attained by simple
intersecting partite uniform families with **equal integer and fractional
cover numbers**. In particular the entire curve (F.8) is sharp within
partite uniform families for \(0\le c\le4\).

**Proof.** Fix a prime power \(q\), let \(V=\mathbb F_q^N\) with
\(N\ge3\), and put \(v=q^N\), \(r_0=(v-1)/(q-1)\).
Vertices of the hypergraph are affine lines; its original edge at
\(p\in V\) is the set of all lines through p. For each one-dimensional
linear direction D, the lines of that direction form one part.
There are \(r_0\) parts and each original edge uses exactly one vertex
of each part. Any two original edges meet at their unique common
line. Every line belongs to q original edges. Uniform old-edge
weights \(1/q\) have value \(v/q\). All \(v/q\) vertices in a fixed part form
an integer cover with the same value.

For each two-dimensional linear subspace W choose
\(z_W\in W\setminus\{0\}\). Define a new edge \(Q_W\) by choosing,
for each direction D, the line
\[
 \begin{cases}
      z_W+D,&D\subset W,\\
      D,&D\not\subset W.
 \end{cases}                                                \tag{F.14a}
\]
This still uses one old vertex per part. These lines cover all
points of V: a point in W lies on a line through \(z_W\) of a direction
inside W; a point outside W lies on its line through zero of a
direction outside W. Thus \(Q_W\) meets every original edge.
Two such new edges share the zero-line in any direction outside
both subspaces. Such a direction exists because
\[
             r_0>2(q+1)\qquad(N\ge3,q\ge2).
\]
Indeed \(r_0\) is at least \(q^2+q+1\), and \(q^2-q-1\) is positive.
Therefore all new edges are pairwise intersecting.

The new edge changes precisely the q directions in W other than
\(\langle z_W\rangle\). At least two changed directions span W;
hence different subspaces give different new edges. Each new edge
also retains at least two distinct lines through zero, since
\(r_0-(q+1)\ge q^2\). If it were an original point-pencil, that
point would be zero, contradicting the changed directions. Thus
all old and new edges are distinct.

The number of two-dimensional linear subspaces is
\[
          \frac{(v-1)(v-q)}{(q^2-1)(q^2-q)}=\Theta(v^2).
                                                               \tag{F.14b}
\]
This follows by counting ordered independent vector pairs and
then ordered bases of a fixed two-dimensional space. For any fixed
\(c\ge q-1\), add
\(L=\max\{0,\lfloor cr_0\rfloor-v\}\) different new edges.
There are more than enough choices since \(L=O(r_0)\).
Extend the old dual weights by zero. A whole original part remains
an integer cover for every new edge, so
\[
                  \tau(H)=\tau^*(H)=v/q,
       \qquad m/r_0\to c,\qquad \tau^*(H)/r_0\to(q-1)/q.
                                                               \tag{F.14c}
\]
Here \(\tau\) denotes the ordinary minimum number of vertices
meeting every edge. This proves the claimed plateau sharpness.

For a ramp, use just the original affine-line design dual and pad
its edges privately to rank \(r=\lceil v/c\rceil\), where
\(0<c\le q-1\). Put the private vertex in position j of every edge
into its own new part j, distinct across edges. There is exactly
one vertex in each old or new part on every edge. One old part
is still an integer cover, and the old dual weights remain feasible.
Thus \(\tau=\tau^*=v/q\) and \(\tau^*/r\to c/q\). For q=2 this
covers the interval below one; for q=\(a+2\) it gives the ramp in (F.8).
The adjacent block-size pairs (2,3), (3,4) and (4,5) cover all
intervals up to c=4. At c=0 a single edge with singleton parts
suffices. This proves the final claim. Finite fields of
prime-power order are the standard algebraic input; Wilson and
Kahn are not used in this explicit proposition.

These plateau examples permit very large repeated intersections.
If \(c>q-1\), the new edges alone give
\[
 I(H)=\sum_{\{E,F\}}(|E\cap F|-1)
   \ge {L\choose2}\{r_0-2(q+1)-1\},
\]
so \(I(H)/r_0^2\to\infty\). The sharp fractional result therefore
covers families outside any small-intersection regime. These examples
supply integer lower constructions; they do not give an integer upper
bound for arbitrary families.

## F.6. Exact equality and deletion stability inside the linear phases

Fix an integer \(k\ge2\), put \(g=(k-1)r+1\), and suppose
\[
                 A=km-(k+1)g>0.                            \tag{F.15}
\]
Thus the second term in (F.2) is strictly larger than the first.

**Theorem F.4 (finite equality).** Under (F.15),
\[
        \tau^*(H)=m/(k+1)
          \quad\Longleftrightarrow\quad
        \max_v\deg_H(v)\le k+1.                            \tag{F.16}
\]

**Proof.** Choose an optimal feasible vector. If its maximum b exceeds
\(1/k\), the weighted-star bound gives a value at most \(g/k\), strictly
smaller than \(m/(k+1)\). If \(1/(k+1)<b\le1/k\), (F.7) rewrites as
\[
           Y\le m/(k+1)-A\{b-1/(k+1)\}<m/(k+1).           \tag{F.17}
\]
Thus equality requires b at most \(1/(k+1)\). Since m such weights sum
to \(m/(k+1)\), every weight equals \(1/(k+1)\). Vertex feasibility implies
the degree cap. Conversely that cap makes the uniform edge weights
\(1/(k+1)\) feasible, attaining the finite upper bound. This proves (F.16).

**Theorem F.5 (explicit deletion bound).** Under (F.15), write
\(d=m/(k+1)-\tau^*(H)\ge0\). If
\[
                   d< A/\{k(k+1)\},                        \tag{F.18}
\]
there is a set of s edges whose deletion leaves maximum degree at
most \(k+1\), where
\[
          s\le (k+1)(k+2)(1+m/A)d.                         \tag{F.19}
\]
The number s is an integer, so the displayed real upper bound also
bounds it after rounding down.

**Proof.** Again use an optimal vector with maximum b. Condition (F.18)
means \(Y>g/k\), so b cannot exceed \(1/k\). If b exceeds \(1/(k+1)\),
(F.17) implies
\[
                       b-1/(k+1)\le d/A.                  \tag{F.20}
\]
Delete precisely the edges with \(y_E\le1/(k+2)\). Each retained
edge has weight strictly above that threshold, so feasibility
allows at most \(k+1\) retained edges at any vertex.
If b is at most \(1/(k+1)\), the nonnegative deficits
\(1/(k+1)-y_E\) sum to d. Each deleted edge contributes at least
\(1/\{(k+1)(k+2)\}\); hence s is at most \((k+1)(k+2)d\).
If b exceeds \(1/(k+1)\), sum the nonnegative peak deficits instead:
\[
          \sum_E(b-y_E)=mb-Y
            =m\{b-1/(k+1)\}+d\le (1+m/A)d.
\]
Each deleted edge again contributes at least
\(1/\{(k+1)(k+2)\}\). This proves (F.19) in both cases. Empty cores
are allowed. No assumption about zero-weight edges is made.

**Corollary F.6 (complete stability criterion on a strict ramp).**
Fix \(k\ge2\) and a real \(c\in(k-1/k,k]\). For any sequence as in
Theorem F.3 with \(m_j/r_j\to c\),
\[
 \frac{\tau^*(H_j)}{r_j}\longrightarrow\frac{c}{k+1}
 \quad\Longleftrightarrow\quad
 \text{deleting }o(r_j)\text{ edges leaves maximum degree at most }k+1.
                                                               \tag{F.21}
\]
For the forward direction, \(A_j/r_j\to kc-k^2+1>0\), while
\(d_j/r_j\to0\). Therefore (F.18) holds eventually and (F.19) is o(\(r_j\)).
For the converse, put weight \(1/(k+1)\) on retained edges and zero on
all deleted edges. This is feasible on the original family and
has value \((m_j-o(r_j))/(k+1)\). The finite upper bound and (F.8)
complete the squeeze. All parameters k,c remain fixed in this limit.

The phase-switch point c=\(k-1/k\) is excluded: \(A_j\) need not be of
linear order there, and (F.19) does not give a uniform coefficient.
The exclusion is essential, already for \(k=2\). More generally let k
be a prime power and take Proposition F.3.1 at \(c=k-1/k\). Then
\(L/r_0\to1-1/k\), and the fractional value is asymptotically sharp.
Any \(k+2\) new edges retain a common zero-line outside all their
selected two-spaces once \(r_0>(k+2)(k+1)\). Therefore any core of
maximum degree at most \(k+1\) retains at most \(k+1\) new edges. It must
delete at least \(L-(k+1)=\Theta(r_0)\) edges. This disproves the
forward implication in (F.21) if the switch is included.

This corollary does not assert integer-cover recovery. Unlike at
integer design ratios, the degree cap alone here need not make
intersection excess \(o(r_j^2)\). A global rounding theorem
requires a separate argument. For an explicit illustration, take the
\(q=3\) affine design dual and clone every vertex in one parallel
class t times, with each copy assigned to its own new part. Every
edge now has rank \(r=r_0+t\), every active degree remains three,
and a whole old part still gives \(\tau=\tau^*=v/3\). Exactly v/3
point triples have their pair intersections increased by t, so
\(I=tv\). If \(t/r_0\to2/c-1\) for fixed \(c\in(3/2,2)\), then
\(m/r\to c\), \(\tau^*/r\to c/3=\psi(c)\), but
\(I/r^2\to c(1-c/2)>0\). This verifies why near-linearity of the
retained core cannot simply be inferred on a strict noninteger ramp.

## F.7. Comparison, verification and remaining questions

This replaces the previous repository's nonlinear fractional
envelope \(\phi\) and its conservative noninteger gap by the exact
asymptotic frontier \(\psi\). The previous frozen package remains a
correct historical proof. At integer ratios the new curve agrees
with the known design values; at nonintegers it supplies the
complete value rather than an unspecified gap. The separate
fractional design-stability theorem and its integer recovery
corollary are unchanged.

This is not an integer-cover theorem. No unrestricted Ryser
solution, journal acceptance, first-result claim or prize-level
assessment is made. The finite optimal value at each arithmetic
pair (r,m) and a full classification of noninteger extremizers
remain open within this project.

The finite upper bound for a feasible edge-weight vector, including
the genuine hypergraph-to-bin assignment and all partition sums, is
proved in the pinned Lean project and supported by exact rational replay. Formal coverage
is recorded separately; it does not include design existence,
published rounding, LP duality or all real-limit arguments. Fixed
primal/dual certificates illustrate both finite phases, and no
solver output is used as evidence for a theorem. The exploratory
LP searches helped select the conjectured curve; the proof above
is independent of them.

## Appendix F.A. Finite duality

For the finite vertex-by-edge incidence matrix \(A\), weak duality
follows by summing the feasibility constraints. A primal vector can
be clipped coordinatewise into \([0,1]\) without destroying
feasibility. Every nonempty edge bounds its dual coordinate by one.
Thus both extrema exist. Let \(\alpha\) be the primal minimum.
For \(\beta<\alpha\), the point \((\mathbf1,\beta)\) lies outside the
finitely generated closed cone
\[
 \{(A^Tz-s,\mathbf1^Tz+t):z,s,t\ge0\}\subset\mathbb R^{m+1}.
\]
Finite-dimensional strict separation gives \((u,b)\) whose value
is nonnegative on the cone and negative at this point. The coordinate
generators give \(u\le0\) and \(b\ge0\). Put \(y=-u\ge0\).
The vertex generators give \(Ay\le b\mathbf1\), while negativity
at the separated point gives \(\sum_Ey_E>b\beta\). If \(b=0\),
nonempty edges force \(y=0\), contradicting strict separation.
Thus \(y/b\) is feasible with value greater than \(\beta\).
Let \(\beta\uparrow\alpha\) and use dual compactness. Weak duality
then proves equality of the two extrema.

For completeness, the cone is closed as follows. Any representation
on a dependent support can lose one generator: move its coefficients
along a linear relation until one becomes zero, preserving
nonnegativity. Iterate to an independent support. A cone on linearly
independent generators is closed because the inverse map on their
span is continuous. There are only finitely many such subsets, so
the original cone is a finite union of closed cones. The standard
finite-dimensional separation theorem is the background input.

## References and provenance

[W] R. M. Wilson, *An existence theory for pairwise balanced designs,
III: Proof of the existence conjectures*, J. Combin. Theory Ser. A
**18** (1975), 71--79, DOI
<https://doi.org/10.1016/0097-3165(75)90067-9>.
The primary abstract states the existence theorem and both divisibility
conditions. Its published theorem is an explicitly named construction input.

[K] J. Kahn, *On a Problem of Erdős and Lovász. II: n(r)=O(r)*,
J. Amer. Math. Soc. **7** (1994), 125--143, Corollary F.5.4,
DOI <https://doi.org/10.1090/S0894-0347-1994-1224593-5>.
The primary Section F.5 text was read; the integer covering theorem
is prior work, not a contribution of this note.

[FKS] Z. Füredi, J. Kahn and P. D. Seymour,
*On the fractional matching polytope of a hypergraph*,
Combinatorica **13** (1993), 167--180,
DOI <https://doi.org/10.1007/BF01303202>. Its rank-dependent weighted
matching results are classical context, not a proof input for (F.2).
The limited comparison does not certify historical novelty.


## Part D: Design-boundary stability

## D.1. Conventions and statements

Let H be a finite simple intersecting r-uniform hypergraph, \(r\ge2\),
with \(m\ge1\) edges. Vertices outside all edges are ignored. A vertex
cover meets every edge, and its minimum size is \(\tau(H)\). A
fractional vertex cover has nonnegative vertex weights of sum at
least one on each edge; its minimum total is \(\tau^*(H)\).
Equivalently, by finite LP duality, \(\tau^*(H)\) is the maximum of
\(Y=\sum_E y_E\) over nonnegative edge weights satisfying
\[
                       \sum_{E\ni v}y_E\le1
                       \quad\hbox{for every vertex }v.       \tag{D.1}
\]
The optimum exists. Appendix D.A records the duality justification.

For any intersecting subfamily J put
\[
 I(J)=\sum_{\{E,F\}\subset E(J)}(|E\cap F|-1).                  \tag{D.2}
\]
Pairs are unordered and distinct. Set \(I=0\) for an empty subfamily.
Every summand is nonnegative; \(I=0\) means linearity.

**Theorem D.1 (general finite extraction).** Fix an integer \(k\ge2\) and
any feasible weights (D.1). If \(Y>m/(k+1)\), retain exactly the edges
with \(y_E>1/(k+1)\). Let J be this core, q its edge count, and
\(s=m-q\) the number deleted. Then every active vertex of J has degree
at most k and
\[
 s\le \frac{m(k+1)\{mr-(m+r-1)Y\}}
              {(r-1)\{(k+1)Y-m\}}.                          \tag{D.3}
\]
Both factors in the denominator are positive. Independently of the
mass condition, this same threshold core has maximum degree at most k.
It satisfies
\[
 \sum_v d_J(v)(k-d_J(v))
       =q\{(k-1)r-q+1\}-2I(J)\ge0,                          \tag{D.4}
\]
including \(q=0\). In particular \(I(J)\le q\{(k-1)r-q+1\}/2\).

**Theorem D.2 (linear deletion stability at a design boundary).** Suppose
\(m=(k-1)r+1\), \(k\ge2\), and put
\[
                     d=m/k-\tau^*(H)\ge0.                  \tag{D.5}
\]
There is a core J, obtained by the threshold above from any optimal
dual vector, for which
\[
 s\le\frac{2k^2(k+1)r}{r-1}\,d\le4k^2(k+1)d,
 \qquad \max_v d_J(v)\le k,\qquad I(J)\le qs/2.             \tag{D.6}
\]
If n counts its active vertices, then
\[
 \sum_v d_J(v)(k-d_J(v))=qs-2I(J),\qquad
                     0\le kn-qr\le qs.                    \tag{D.7}
\]
The dependence on d cannot be replaced by o(d) uniformly, already
for \(k=2\); Section D.5 gives a family whose minimum deletion count is 2d.
No optimality of the coefficient in (D.6) is claimed.

**Theorem D.3 (complete asymptotic characterization at integer ratios).**
Fix a positive integer a and a sequence of such hypergraphs with
\(r_j\to\infty\) and \(m_j/r_j\to a\). The following are equivalent:

1. \(\tau^*(H_j)/r_j\to a/(a+1)\).
2. Deleting o(\(r_j\)) edges leaves a core with maximum vertex degree
   at most a+1.

For the cores in either condition, \(q_j/r_j\to a\),
\[
 I(J_j)=o(r_j^2),\quad
 n_j/r_j^2\to a/(a+1),\quad
 \sum_v(d_{J_j}(v)-a-1)^2=o(r_j^2).                          \tag{D.8}
\]
Moreover
\[
              \tau(H_j)/r_j\to a/(a+1),\qquad
                         \tau(H_j)/\tau^*(H_j)\to1.        \tag{D.9}
\]
Only (D.9) uses the published rounding input stated in Section D.4.
The hypotheses impose no bound on intersections in the whole family.
In fact (D.8) can fail for the whole family even when (D.9) holds exactly,
as Section D.5 demonstrates.

## D.2. The weighted estimate and finite extraction

Choose an edge P of maximum weight b. Every other edge meets P,
so nonnegative weights and (D.1) give
\[
 Y-b\le\sum_{v\in P}\sum_{E\ne P,\ v\in E}y_E\le r(1-b).
 \quad\hbox{Thus }Y\le r-(r-1)b.                            \tag{D.10}
\]
Multiple intersections only increase the middle sum. Since \(Y\le mb\),
\[
             Y\le\frac{mr}{m+r-1},\qquad
 (r-1)(mb-Y)\le mr-(m+r-1)Y=:\Psi.                         \tag{D.11}
\]
In particular \(\Psi\ge0\). These facts hold for every feasible vector.

For a deleted edge, \(b-y_E\ge b-1/(k+1)\). Thus
\[
 s\{b-1/(k+1)\}\le\sum_{E\text{ deleted}}(b-y_E)
                           \le mb-Y.                      \tag{D.12}
\]
Here all peak deficits b-y_E are nonnegative. Since \(b\ge Y/m\) and
\(Y/m>1/(k+1)\), combining (D.11)--(D.12) proves (D.3).

If a vertex belonged to at least k+1 retained edges, their weights
would sum to more than one. Hence the retained degree is at most k.
For the core, double counting incidences and edge-pair intersections
gives
\[
 \sum_v d_J(v)=qr,\qquad
 \sum_v\binom{d_J(v)}2=\binom q2+I(J).
\]
Consequently \(\sum_v d_J(v)^2=qr+q(q-1)+2I(J)\).
Subtracting this from kqr proves (D.4); all summands on its left
are nonnegative. This proves Theorem D.1, including empty cores.

## D.3. The design boundary and the iff statement

At \(m=(k-1)r+1\), equation (D.11) gives \(\tau^*\le m/k\), proving
\(d\ge0\). For an optimal dual vector, \(Y=m/k-d\) and \(\Psi=krd\).
If \(d\le m/[2k(k+1)]\), then
\[
              (k+1)Y-m=m/k-(k+1)d\ge m/(2k)>0.
\]
Insert these estimates into (D.3) to obtain the first bound in (D.6).
If d is larger instead, the trivial bound \(s\le m\) gives
\(s\le2k(k+1)d\), which is stronger. This proves (D.6) for every d,
with no small-deficit hypothesis. Formula (D.4) becomes the first
identity of (D.7). For each active degree \(1\le d_J(v)\le k\),
\(0\le k-d_J(v)\le d_J(v)(k-d_J(v))\). Summing proves the second
claim of (D.7). This completes Theorem D.2.

For Theorem D.3 put \(k=a+1\). Under condition 1,
\[
 \Psi_j/r_j^2
 =m_j/r_j-(m_j/r_j+1-1/r_j)Y_j/r_j\longrightarrow0.
\]
Also \(Y_j/m_j\to1/k>1/(k+1)\). Applying (D.3) shows \(s_j/r_j\to0\).
This proves condition 2, with an actual threshold core.

Conversely, if a core of size \(q_j=m_j-o(r_j)\) has degree at most k,
put weight 1/k on each core edge and zero on each deleted edge.
These weights are feasible for the original family, giving
\(\tau^*(H_j)\ge q_j/k\). The harmonic upper bound (D.11) proves
condition 1. This argument is valid for any such core.

For any core as in condition 2, (D.4) implies
\[
 0\le\sum_v d_J(v)(k-d_J(v))\le q\{(k-1)r-q+1\}=o(r^2),
 \qquad 0\le2I(J)\le q\{(k-1)r-q+1\}=o(r^2).
\]
The bracket is nonnegative for nonempty cores, by (D.4).
Summing k-d_J as above shows \(kn-qr=o(r^2)\). Finally, for
\(1\le d_J\le k\), \((k-d_J)^2\le(k-1)d_J(k-d_J)\); summation proves
the variance assertion (D.8). This proves every structural part of
Theorem D.3 without a rounding theorem.

## D.4. Integer rounding and what is imported

**Input K (Kahn 1994, Corollary D.5.4, printed p.140).** For fixed C>0,
an intersecting r-uniform sequence with at most Cr edges and
maximum intersection of distinct edges o(r) satisfies
\[
                    \tau/r\le C/(C+1)+o(1).                \tag{D.13}
\]
This is a published input, not an assertion proved or formalized
in this note. We explain precisely how its hypotheses are reached.

Let J be a core from Theorem D.3 and write \(\epsilon=I(J)/r^2\to0\).
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
The lower bound \(\tau(H)\ge\tau^*(H)\) proves (D.9).

One consequence is a uniform separation statement: for each fixed
integer a and \(\eta>0\) there exist \(\delta>0\) and R such that, if \(r\ge R\),
\(|m/r-a|\le\delta\) and \(\tau/r\ge a/(a+1)+\eta\), then
\(\tau^*/r\le a/(a+1)-\delta\). If this failed, for \(\delta=1/j\) and
\(R=j\) one could choose a violating family with \(m/r\to a\), integer
cover ratio bounded above the endpoint, and fractional ratio tending
to the endpoint by (D.11). This contradicts Theorem D.3.
No explicit value of \(\delta\), no rate in Input K, and no resolution
of unrestricted Ryser's conjecture are asserted.

## D.5. Sharp deletion order and unavoidable exceptional edges

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
             \tau=\tau^*=n/2,\qquad d=m/2-n/2=t/2.         \tag{D.14}
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
                         I(H)=\binom t2(r-2).              \tag{D.15}
\]
For the exact integer sequence \(n=2j^4\) and \(t=j^3\), \(j\ge2\), we have
\(t=o(r)\), \(m/r\to1\) and fractional ratio tending to 1/2, but
\(I(H)/r^2\to\infty\). Even the integer ratio agrees with its
fractional counterpart exactly. Thus Theorem D.3 cannot require the
whole original family to have \(I=o(r^2)\), nor can it omit deletion.

## D.6. Verification scope and significance limits

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

## Appendix D.A. The finite duality fact

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
<https://doi.org/10.1090/S0894-0347-1994-1224593-5>, Corollary D.5.4.
The harmonic integer bound and rounding theorem are prior work.

[F] Repository note *A universal fractional cover envelope and its
design equality cases*, commit 4ae9051, 7 October 2026. Its stronger
noninteger envelope and exact equality classification are preserved.
The present deletion estimate uses only the weighted-star inequality
and supplies a separate quantitative stability theorem.

The limited literature screen also identifies Kayll's DIMACS Report
95-55, Theorem D.2.1, as an existing resolution of Kahn's Conjecture
5.6. That theorem is not an input here. The new finite extraction
and fixed-ratio characterization remain subject to further novelty
comparison; no first-result wording is used.


## Part S: The complete matching spectrum

## S.1. Definitions and statements

A hypergraph here is a finite simple family of nonempty finite sets.
Its rank is at most an integer \(r\ge2\); its edge count is m. Its
matching number \(\nu(H)\) is the largest number of pairwise disjoint
edges. Its fractional vertex-cover number \(\tau^*(H)\) is the
minimum sum of nonnegative vertex weights with sum at least one on
an edge. Finite LP duality identifies this with the maximum
\(Y=\sum_E y_E\) under
\[
             y_E\ge0,\qquad \sum_{E\ni v}y_E\le1.           \tag{S.1}
\]
The complete finite separation argument is given in Appendix S.A of
[F]. Empty families have both numbers zero and are allowed below.

Recall the continuous nondecreasing function
\[
 \psi(x)=x/2\quad(0\le x\le1),\qquad
 \psi(x)=\max\{a/(a+1),x/(a+2)\}
            \quad(a\le x\le a+1,\ a=1,2,\ldots).           \tag{S.2}
\]
It is the sharp intersecting fractional frontier proved in [F].
For an integer \(s\ge1\), define
\[
 \boxed{\displaystyle
 \Psi_s(c)=\max\left\{\sum_{i=1}^s\psi(c_i):
              c_i\ge0,\ \sum_{i=1}^sc_i=c\right\}.}        \tag{S.3}
\]
This is an attained maximum on a compact simplex. For \(s=1\), it
is exactly \(\psi\).

**Theorem S.1 (finite and sharp bounded-packing law).** Every H with
\(\nu(H)\le s\) satisfies
\[
                  \tau^*(H)\le r\Psi_s(m/r)+s/2.           \tag{S.4}
\]
If s is fixed, \(r_j\to\infty\), \(\nu(H_j)\le s\), and
\(m_j/r_j\to c<\infty\), then
\[
                  \limsup_j\tau^*(H_j)/r_j\le\Psi_s(c).    \tag{S.5}
\]
For every real \(c\ge0\), a sequence of simple uniform hypergraphs
of ranks tending to infinity attains equality in this limit and
has matching number **exactly s**. The result imposes no partite,
regularity, linearity or intersection-size assumption.

Here and below fixed-matching sharpness is an asymptotic statement,
not an assertion that (S.4) is the best bound for every finite (r,m,s).

**Theorem S.2 (finite closed formula).** Put \(c=Q+\theta\), where
\(Q=\lfloor c\rfloor\) and \(0\le\theta<1\). For \(s\ge2\) set
\(u=s-1\). For integers \(0\le a\le Q\), write
\(Q-a=ub+t\), with \(0\le t<u\). Then
\[
 \boxed{\displaystyle
 \Psi_s(c)=\max_{0\le a\le Q}
 \left\{\psi(a+\theta)
       +(u-t)\frac{b}{b+1}+t\frac{b+1}{b+2}\right\}.}      \tag{S.6}
\]
In particular, \(\Psi_2(3)=7/6\), \(\Psi_2(7/2)=7/6\), and
\(\Psi_2(15/4)=5/4\). This formula involves a finite list, not a
numerical optimization or an unverified solver assumption.

Define h by linear interpolation of its nonnegative integer values
\(h(a)=a/(a+1)\). Thus
\[
 h(x)=\frac{a}{a+1}+
       \frac{x-a}{(a+1)(a+2)}\quad(a\le x\le a+1).          \tag{S.7}
\]

**Theorem S.3 (arbitrary and diverging matching numbers).** For every
nonempty H, putting \(s=\nu(H)\),
\[
 \frac{\tau^*(H)}{r s}\le h\!\left(\frac{m}{r s}\right)
                                      +\frac1{2r}.         \tag{S.8}
\]
For all fixed \(c\ge0\),
\[
            h(c)-\frac1{2s}\le\frac{\Psi_s(sc)}s\le h(c).   \tag{S.9}
\]
Consequently when \(r_j\to\infty\), \(\nu(H_j)\to\infty\), and
\(m_j/(r_j\nu(H_j))\to c<\infty\), the sharp upper limit of
\(\tau^*(H_j)/(r_j\nu(H_j))\) is h(c). Uniform families attain
this for any prescribed integer sequences of ranks and matching
numbers tending to infinity.

## S.2. The anchored finite inequality

The key point is that the earlier signed-bin proof does not require
all pairs of edges in a group to intersect. It only requires an edge
of maximum weight that meets every edge of that group.

**Lemma S.4 (anchored bound).** Let G have \(t\ge1\) edges of rank at most r,
and let y be a vector satisfying (S.1) on G. Suppose \(P\in G\),
every other edge meets P, and \(b=y_P\ge y_E\) for all E in G.
Then, for every integer \(k\ge2\),
\[
 \sum_{E\in G}y_E\le
       \max\{((k-1)r+1)/k,t/(k+1)\}.                      \tag{S.10}
\]
If \(t\ge2\), the same sum is at most t/2. If \(t=1\) it is at most one.
In all cases,
\[
              \sum_{E\in G}y_E\le r\psi(t/r)+1/2.          \tag{S.11}
\]

**Proof.** Write \(Y_G=\sum_{E\in G}y_E\). The nonnegative incidence
count on P gives \(Y_G\le r-(r-1)b\). If \(b\le1/(k+1)\), use
\(Y_G\le tb\); if \(b>1/k\), use that star bound. Both give (S.10).
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
reciprocal endpoints. This proves (S.10), without any assumption
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
and apply (S.10) with k=a+1. Its first term differs from
\(r a/(a+1)\) by \(1/k\le1/2\), proving (S.11). For \(t=1\),
\(r\psi(1/r)+1/2=1\); this also verifies (S.11).

## S.3. Greedy partition and the finite law

Fix any feasible y on H. Among the remaining edges choose one of
maximum weight, P_1, and let G_1 consist of every remaining edge
meeting P_1, including P_1 itself. Remove G_1. Repeat until no edge
remains. At every step the selected edge meets all edges of its group
and has maximum weight there. Its group's restricted vector is feasible.

All selected anchors are pairwise disjoint: a later selected edge
was not removed as a neighbor of an earlier anchor. Hence the number
l of groups is at most \(\nu(H)\le s\). Their edge sets partition H;
write \(t_i=|G_i|\), and pad the list to s groups with empty groups.
Applying (S.11) to each nonempty group gives
\[
 Y\le r\sum_{i=1}^s\psi(t_i/r)+l/2
       \le r\Psi_s(m/r)+s/2.
\]
The exact partition identity \(\sum_i t_i=m\) is what permits (S.3).
This holds for every feasible vector, proving (S.4) by finite duality.
Empty families cause no difficulty. The universal additive constant s/2
cannot be reduced: s disjoint r-edges have \(m=s\), \(\tau^*=s\),
and \(\Psi_s(s/r)=s/(2r)\), so (S.4) holds with exact equality.

Both psi and \(\Psi_s\) are nondecreasing and 1/2-Lipschitz.
For psi, this follows from its piecewise slopes, all between zero
and 1/2. For \(\Psi_s\), increasing total mass by delta can only
increase the maximum: add delta to a coordinate of a maximizing
allocation. Conversely trim delta from coordinates of any allocation
at the larger total mass; the sum changes by at most delta/2.
Taking the maximum proves the Lipschitz bound. Dividing (S.4) by r
and passing to the limit now proves (S.5).

## S.4. Sharpness with a common rank

One must not silently combine unrelated rank subsequences. We prove
the following common-rank construction explicitly.

**Lemma S.5.** For every fixed \(x\ge0\) and every sufficiently large integer
R, there is a simple intersecting R-uniform family \(H_R(x)\) with
\[
            |H_R(x)|/R\to x,\qquad
            \tau^*(H_R(x))/R\to\psi(x).                   \tag{S.12}
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
Corollary S.5.4 states that an intersecting \(r_0\)-uniform family with
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
still yields (S.12); thus Kahn is unnecessary at integer x.

If x>0 lies on a ramp, choose its block size k=a+2, or k=2 below
one. Choose the largest admissible
\(v=1+k(k-1)N\le xR\). Then \(v=xR+O(1)\), and its replication
\(r_0=(v-1)/(k-1)\le R\) because \(x\le k-1\). Pad every edge privately
to R. The same exact certificates give value v/k and (S.12).
At a switch either construction works. For x=0 take one R-edge.
This completes the common-rank lemma. The prime-power alternatives in [F] give additional explicit
subsequences; they are not used to assert construction at every
large integer R.

Choose a maximizing allocation \((c_1,\ldots,c_s)\) in (S.3). For each
large R take the disjoint union of the s families \(H_R(c_i)\), on
disjoint vertex sets. It is simple and R-uniform. Each component is
nonempty and intersecting, so its matching number is one; the union
has matching number exactly s. Fractional cover is additive across
disjoint components, by summing separate feasible primal and dual
certificates. Formula (S.12) then attains (S.5). This proves Theorem S.1.

## S.5. Reduction to a finite formula

On each integer unit interval psi is convex: it is the maximum of a
constant and an affine function, or the affine function x/2 below one.
Take a maximizing allocation in (S.3). If two coordinates are noninteger,
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
u-t equal b and t equal b+1, where \(Q-a=ub+t\). This proves (S.6),
including \(\theta=0\). Zero integer coordinates contribute zero and
are allowed. No unbounded search remains in that formula.

## S.6. Concave limit and an exact gap distinction

The slopes in (S.7) decrease, so h is concave and 1/2-Lipschitz.
Also \(\psi\le h\), with equality on [0,1] and at integer points,
and strict inequality at every noninteger point greater than one.
To check this directly on [a,a+1], h lies above its constant left
endpoint and its chord to the right endpoint; each of the two terms
in (S.2) touches it at only its respective integer endpoint.
Jensen's inequality gives
\[
                         \Psi_s(c)\le s h(c/s).             \tag{S.13}
\]
At integer total c=Q, balanced integer coordinates attain equality
in (S.13), by the preceding unit-transfer argument. At arbitrary
c=Q+\(\theta\), increasing one coordinate in this integer allocation
shows \(\Psi_s(c)\ge s h(Q/s)\). Consequently
\[
       0\le s h(c/s)-\Psi_s(c)\le(c-Q)/2<1/2.              \tag{S.14}
\]
This proves (S.9), and (S.8) follows from (S.4) and (S.13).
For \(c\le s\), choose all coordinates in [0,1], giving \(\Psi_s(c)=c/2\).
For noninteger \(c>s\) the inequality in (S.13) is strict: equality in
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
in Theorem S.3. The case c=0 uses s disjoint R-edges.

## S.7. Dependencies, verification and scope

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
JAMS 7 (1994), 125--143, Corollary S.5.4, printed p.140,
DOI <https://doi.org/10.1090/S0894-0347-1994-1224593-5>.

[Fu] Z. Füredi, *Maximum degree and fractional matchings in uniform
hypergraphs*, Combinatorica 1 (1981), 155--162. The classical
rank/matching-number bound is prior context. The present spectrum
also fixes the edge/rank ratio; no priority conclusion is drawn.

[FKS] Z. Füredi, J. Kahn and P. D. Seymour, *On the fractional matching
polytope of a hypergraph*, Combinatorica 13 (1993), 167--180,
DOI <https://doi.org/10.1007/BF01303202>.
