# The sharp fractional cover frontier at every finite edge/rank ratio

Research continuation, 7 October 2026. We determine the entire limiting
fractional-cover curve for intersecting hypergraphs with a bounded
edge/rank ratio. The upper bound is an elementary finite theorem using
signed counting. Sharpness uses explicitly stated classical design
existence and small-intersection covering inputs. All cover values here
are fractional unless marked otherwise.

## 1. Definitions and the finite bound

Let H be a finite simple intersecting hypergraph with \(m\ge1\) nonempty
edges of size at most r, where \(r\ge2\) is an integer. Its fractional vertex
cover number \(\tau^*(H)\) is the minimum sum of nonnegative vertex
weights whose sum on every edge is at least one. By finite LP duality,
it equals the maximum \(Y=\sum_E y_E\) over weights satisfying
\[
                y_E\ge0,\qquad\sum_{E\ni v}y_E\le1
                  \quad\hbox{for every vertex }v.            \tag{1}
\]
Appendix A specifies the finite duality fact used. Every edge is
nonempty, so feasible edge weights lie in [0,1] and an optimum exists.

**Theorem 1 (finite bound, without additional intersection restrictions).** For
every integer \(k\ge2\),
\[
 \boxed{\displaystyle
 \tau^*(H)\le\max\left\{\frac{(k-1)r+1}{k},\frac{m}{k+1}\right\}.}
                                                               \tag{2}
\]
For \(m\ge2\) we also have \(\tau^*(H)\le m/2\); for \(m=1\) the value is one.
No partite, linearity, uniformity, or small-codegree condition is needed.
The finite maximum in (2) is not asserted to be the exact optimum for
every arithmetic pair (r,m).

## 2. A signed bin inequality

**Lemma 2.** Suppose \(k\ge2\), \(1/(k+1)<b\le1/k\), and a bin contains
\(\ell\in\mathbb Z_{\ge0}\) weights in [0,b] of total \(W\le1-b\). Then
\[
 W-(1-kb)\ell\le(k-1)\{(k+1)b-1\}.                          \tag{3}
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

## 3. Proof of the finite theorem

Fix any feasible vector (1), choose a maximum-weight edge P, and
write \(b=y_P\), \(Y=\sum_Ey_E\). Choose any v in P; feasibility gives
\(b\le1\). Nonnegative weights and intersectingness imply the weighted-star
inequality
\[
 Y-b\le\sum_{v\in P}\sum_{E\ne P,\ v\in E}y_E
                         \le|P|(1-b)\le r(1-b).
 \qquad Y\le r-(r-1)b.                                     \tag{4}
\]
Multiple intersections do not invalidate this inequality.

Fix k and put \(g=(k-1)r+1\). If \(b\le1/(k+1)\), then
\(Y\le m/(k+1)\), proving (2). If \(b>1/k\), (4) gives
\(Y\le r-(r-1)/k=g/k\), again proving (2).

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
                \sum_{v\in P}\ell_v=m-1.                    \tag{5}
\]
Lemma 2 can now be summed, even though its summands have signs:
\[
       (Y-b)-(1-kb)(m-1)
          \le |P|(k-1)\{(k+1)b-1\}
          \le r(k-1)\{(k+1)b-1\}.                          \tag{6}
\]
The last factor is positive. Rearranging yields
\[
          Y\le m-g+b\{(k+1)g-km\}.                        \tag{7}
\]
The right side is affine in b. At the endpoints b=\(1/(k+1)\) and
b=\(1/k\) its values are respectively \(m/(k+1)\) and \(g/k\). Therefore (7)
is at most their maximum throughout the closed interval. This
proves (2) for every feasible vector and hence for the optimum.

For \(m\ge2\), each pair of distinct edges has a common vertex, so
\(y_E+y_F\le1\). Summing over all unordered edge pairs gives
\((m-1)Y\le\binom m2\), hence \(Y\le m/2\). For \(m=1\), a unit vertex weight
and a unit dual edge weight show \(\tau^*=1\).

This upper-bound proof uses no design theorem, rounding result,
numerical experiment or claim in OpenAI/math.

## 4. The exact limiting curve

Define the continuous nondecreasing function
\[
 \psi(c)=c/2\quad(0\le c\le1),\qquad
 \psi(c)=\max\left\{\frac{a}{a+1},\frac{c}{a+2}\right\}
               \quad(a\le c\le a+1,\ a=1,2,\ldots).         \tag{8}
\]
The formulas agree at integer endpoints. On [a,\(a+1\)] the switch is
\(c=a(a+2)/(a+1)=a+1-1/(a+1)\): a plateau is followed by a linear
ramp. In particular \(\psi(3/2)=1/2\), \(\psi(7/4)=7/12\), and
\(\psi(5/2)=2/3\).

**Theorem 3 (sharp frontier at every real ratio).** If \(r_j\) tends to
infinity, \(H_j\) is as in Theorem 1, and \(m_j/r_j\to c<\infty\), then
\[
                   \limsup_j\tau^*(H_j)/r_j\le\psi(c).       \tag{9}
\]
For every real \(c\ge0\) there is a sequence of **simple intersecting
\(r_j\)-uniform** hypergraphs with \(m_j/r_j\to c\) for which
\[
                         \tau^*(H_j)/r_j\to\psi(c).         \tag{10}
\]
Thus the same sharp limiting curve holds whether uniformity is
required or only the rank bound is imposed.

**Upper bound.** For \(c\ge1\) choose the fixed \(k=a+1\) corresponding to
an interval [a,\(a+1\)] containing c, and apply (2). Dividing by \(r_j\)
and taking limsup gives (9). At shared endpoints either formula
works. For \(c\le1\) use the pair bound, with the single-edge cases
contributing at most \(1/r_j\). This also handles \(c=0\).

The next section proves (10) and states every imported theorem.

## 5. Sharpness and classical inputs

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
             k-1\mid v-1,\qquad k(k-1)\mid v(v-1),          \tag{11}
\]
a Steiner 2-(v,k,1) design exists. In particular one can take an
unbounded sequence \(v=1+k(k-1)N\), with replication \(r_0=kN\).
This classical existence theorem is used only for sharpness,
not for the finite upper bound.

**Input K (Kahn 1994, Corollary 5.4, printed p.140).** For fixed \(C>0\),
intersecting \(r\)-uniform families with at most \(Cr\) edges and maximum
distinct-edge intersection \(o(r)\) have integer cover number at most
\((C/(C+1)+o(1))r\). Again this is used only in a construction step.

### 5.1 Plateau construction

Fix \(a\ge1\) and \(k=a+1\). Apply Input W and let \(H_0\) be a design dual
with \(r_0\to\infty\) and \(v=(k-1)r_0+1\). It is linear, with
\(v/r_0\to a\). Applying Input K first with \(C=a+\eta\) and then decreasing
\(\eta\) to zero gives an integer cover \(C_0\) of size
\[
                  |C_0|\le(a/(a+1)+o(1))r_0<r_0           \tag{12}
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
       m/r_0\to c,\qquad\tau^*/r_0\to a/(a+1).             \tag{13}
\]
No explicit algorithm to find Wilson's designs or \(C_0\) is asserted;
their existence follows from the two named published inputs.
For prime-power k, affine-line designs give explicit design instances.

### 5.2 Linear-ramp construction

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
                  m/r\to c,\qquad\tau^*/r\to c/k.           \tag{14}
\]
This gives c/2 below one and c/(\(a+2\)) on [a,\(a+1\)]. Choose between
(13) and (14) according to the larger term in (8), proving
sharpness. For \(c=0\) take one r-edge with \(r\to\infty\); its value
one divided by r tends to zero. Theorem 3 is proved.

### 5.3 Explicit partite sharpness by shifting a partial pencil

The preceding all-integer construction inputs are unnecessary when
the block size is a prime power. We now give an explicit construction
that additionally preserves a partition into as many parts as the rank.

**Proposition 3.1.** Every plateau for which \(a+1\) is a prime power,
and every ramp for which \(a+2\) is a prime power, is attained by simple
intersecting partite uniform families with **equal integer and fractional
cover numbers**. In particular the entire curve (8) is sharp within
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
 \end{cases}                                                \tag{14a}
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
                                                               \tag{14b}
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
                                                               \tag{14c}
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
covers the interval below one; for q=\(a+2\) it gives the ramp in (8).
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

## 6. Exact equality and deletion stability inside the linear phases

Fix an integer \(k\ge2\), put \(g=(k-1)r+1\), and suppose
\[
                 A=km-(k+1)g>0.                            \tag{15}
\]
Thus the second term in (2) is strictly larger than the first.

**Theorem 4 (finite equality).** Under (15),
\[
        \tau^*(H)=m/(k+1)
          \quad\Longleftrightarrow\quad
        \max_v\deg_H(v)\le k+1.                            \tag{16}
\]

**Proof.** Choose an optimal feasible vector. If its maximum b exceeds
\(1/k\), the weighted-star bound gives a value at most \(g/k\), strictly
smaller than \(m/(k+1)\). If \(1/(k+1)<b\le1/k\), (7) rewrites as
\[
           Y\le m/(k+1)-A\{b-1/(k+1)\}<m/(k+1).           \tag{17}
\]
Thus equality requires b at most \(1/(k+1)\). Since m such weights sum
to \(m/(k+1)\), every weight equals \(1/(k+1)\). Vertex feasibility implies
the degree cap. Conversely that cap makes the uniform edge weights
\(1/(k+1)\) feasible, attaining the finite upper bound. This proves (16).

**Theorem 5 (explicit deletion bound).** Under (15), write
\(d=m/(k+1)-\tau^*(H)\ge0\). If
\[
                   d< A/\{k(k+1)\},                        \tag{18}
\]
there is a set of s edges whose deletion leaves maximum degree at
most \(k+1\), where
\[
          s\le (k+1)(k+2)(1+m/A)d.                         \tag{19}
\]
The number s is an integer, so the displayed real upper bound also
bounds it after rounding down.

**Proof.** Again use an optimal vector with maximum b. Condition (18)
means \(Y>g/k\), so b cannot exceed \(1/k\). If b exceeds \(1/(k+1)\),
(17) implies
\[
                       b-1/(k+1)\le d/A.                  \tag{20}
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
\(1/\{(k+1)(k+2)\}\). This proves (19) in both cases. Empty cores
are allowed. No assumption about zero-weight edges is made.

**Corollary 6 (complete stability criterion on a strict ramp).**
Fix \(k\ge2\) and a real \(c\in(k-1/k,k]\). For any sequence as in
Theorem 3 with \(m_j/r_j\to c\),
\[
 \frac{\tau^*(H_j)}{r_j}\longrightarrow\frac{c}{k+1}
 \quad\Longleftrightarrow\quad
 \text{deleting }o(r_j)\text{ edges leaves maximum degree at most }k+1.
                                                               \tag{21}
\]
For the forward direction, \(A_j/r_j\to kc-k^2+1>0\), while
\(d_j/r_j\to0\). Therefore (18) holds eventually and (19) is o(\(r_j\)).
For the converse, put weight \(1/(k+1)\) on retained edges and zero on
all deleted edges. This is feasible on the original family and
has value \((m_j-o(r_j))/(k+1)\). The finite upper bound and (8)
complete the squeeze. All parameters k,c remain fixed in this limit.

The phase-switch point c=\(k-1/k\) is excluded: \(A_j\) need not be of
linear order there, and (19) does not give a uniform coefficient.
The exclusion is essential, already for \(k=2\). More generally let k
be a prime power and take Proposition 3.1 at \(c=k-1/k\). Then
\(L/r_0\to1-1/k\), and the fractional value is asymptotically sharp.
Any \(k+2\) new edges retain a common zero-line outside all their
selected two-spaces once \(r_0>(k+2)(k+1)\). Therefore any core of
maximum degree at most \(k+1\) retains at most \(k+1\) new edges. It must
delete at least \(L-(k+1)=\Theta(r_0)\) edges. This disproves the
forward implication in (21) if the switch is included.

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

## 7. Comparison, verification and remaining questions

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

## Appendix A. Finite duality

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
J. Amer. Math. Soc. **7** (1994), 125--143, Corollary 5.4,
DOI <https://doi.org/10.1090/S0894-0347-1994-1224593-5>.
The primary Section 5 text was read; the integer covering theorem
is prior work, not a contribution of this note.

[FKS] Z. Füredi, J. Kahn and P. D. Seymour,
*On the fractional matching polytope of a hypergraph*,
Combinatorica **13** (1993), 167--180,
DOI <https://doi.org/10.1007/BF01303202>. Its rank-dependent weighted
matching results are classical context, not a proof input for (2).
The limited comparison does not certify historical novelty.
