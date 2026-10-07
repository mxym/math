# Near-linear Ryser equality families require superlinear edge counts

Research continuation, 7 October 2026. This proves a structural limit
theorem for the same partite cover-number programme. The deduction uses
a precisely cited published edge-colouring theorem. No priority claim,
full Lean formalization or solution of Ryser's conjecture is asserted.

## 1. The structural conclusion

Throughout, \(H\) is a finite simple intersecting \(r\)-partite
\(r\)-uniform hypergraph, \(r\ge2\), with \(m\) distinct edges and
cover number \(t=\tau(H)\). Each edge contains exactly one vertex of
each specified part. Set
\[
 I(H)=\sum_{\{A,B\}\subset E(H)}(|A\cap B|-1)\ge0,
\]
where the sum is over unordered pairs of distinct edges. Empty families
have both cover number and excess zero. Linearity of an intersecting
family is equivalent to \(I(H)=0\).

**Theorem 1 (superlinear edge necessity).** Let \(r_j\to\infty\)
and let \(H_j\) satisfy these hypotheses, with
\(\tau(H_j)\ge r_j-1\) and \(I(H_j)=o(r_j^2)\). Then
\[
 \frac{|E(H_j)|}{r_j}\longrightarrow+\infty. \tag{1}
\]
In particular, no infinite family of linear intersecting partite
hypergraphs with \(\tau\ge r-1\) can have a bounded edge/rank ratio.

Define \(f_{\rm lin}(r)\) as the minimum edge count in this linear
class, with value \(+\infty\) when the class is empty. Then
\[
 f_{\rm lin}(r)/r\longrightarrow+\infty. \tag{2}
\]
This gives no rate such as \(r\log r\), and does not establish
nonemptiness at all ranks. It does not determine the minimum in the
larger nonlinear class or prove \(\tau(H)\le r-1\).

The quantitative theorem behind this limit is the following. For every
fixed integer \(D\ge4\), put
\[
 L=D+1,\qquad c_D=\frac12+\sqrt{2D},\qquad
 y_D=\frac{(D-3)(D-2)}2,\qquad A_D=\frac{L(y_D-1)}3.
\]

**Theorem 2 (degree-parameter cover inequality).** For every \(D\ge4\)
and \(\delta>0\), a finite constant \(C_{D,\delta}\) exists,
independent of \(H,r\), such that
\[
 m\ge L\tau(H)-(L-c_D+\delta)r
                  -\frac{A_D I(H)}r-C_{D,\delta}. \tag{3}
\]
Thus under \(\tau(H)\ge r-1\),
\[
 \frac mr\ge c_D-\delta-
              A_D\frac{I(H)}{r^2}-\frac{C_{D,\delta}+L}{r}. \tag{4}
\]
The parameter \(D\) is fixed before taking \(r\to\infty\).
There is no claim of uniform control of \(C_{D,\delta}\) as \(D\)
grows. This order of quantifiers suffices for Theorem 1, because
\(c_D\to\infty\).

The new mechanism replicates a block of size \(d\ge4\) exactly
\(d-3\) times and weights each copy by \((d-2)/2\). This aligns
the weighted matching gain with the star degree and an exact pair-count
identity. The preceding notes use degrees at most four and weighted
three/four blocks; the arbitrary fixed-degree replication here gives
the superlinear conclusion. Degree peeling, pair-excess deletion and
matching/star tools have predecessors in Sivashankar [S, Section 4].

## 2. The published input and parallel copies

We use Kahn's small-codegree edge-colouring theorem, in the form stated
by Kang--Kelly--Kühn--Methuku--Osthus [KKKMO, Theorem 3.1]. For each
fixed rank \(D\) and \(\eta>0\), there is \(\gamma>0\) such that
a hypergraph of rank at most \(D\), maximum degree at most \(a\),
and maximum pair codegree at most \(\gamma a\) has list chromatic
index at most \((1+\eta)a\). Ordinary colouring is a consequence.

Their convention explicitly allows parallel edge copies: edges have
identities, and distinct edges may have equal vertex sets. Two such
copies cannot receive the same colour. Degrees and codegrees count
copies. This convention is essential below and was checked in the
primary manuscript, Section 1.2, as well as Theorem 3.1.

Choose an integer \(a_0=a_0(D,\eta)\ge1\) so large that
\(D-3\le\gamma a\) for all \(a\ge a_0\). Thus Input K applies
to rank at most \(D\), codegree at most \(D-3\), and maximum degree
\(a\ge a_0\). We do not re-prove or formalize that published theorem.
Every application below satisfies these hypotheses. No OpenAI/math
theorem or degree-three residual lemma is needed for this note.

## 3. Peeling and an exact residual identity

Select a vertex of current degree at least \(L=D+1\), record it and
delete its current incident edges. Continue until the residual \(J\)
has maximum degree at most \(D\). If \(k\) vertices are recorded and
\(q=|E(J)|\), then
\[
 m\ge q+Lk,\quad t\le k+\tau(J),\quad
 m\ge q+L(t-\tau(J)). \tag{5}
\]
It remains intersecting and \(r\)-uniform unless empty, and retains
the original parts. Fixing a nonempty residual edge gives
\(q-1\le r(D-1)\); an empty residual also satisfies this. Therefore
\[
 q\le(D-1)r+1\le Dr. \tag{6}
\]
Let \(T=I(J)\le I(H)\); deleting edges only omits nonnegative
summands. Write \(x_d\) for residual degree counts, \(1\le d\le D\),
and define
\[
 W=\sum_{d=3}^D\frac{d-2}{2}x_d,\qquad
 Y=\sum_{d=4}^D\frac{(d-3)(d-2)}2x_d,\qquad
 K=\frac{q(q-r)}2.
\]
Incidence and intersection counting give
\(\sum d x_d=qr\) and
\(\sum\binom d2x_d=\binom q2+T\). Subtracting half the incidence
count gives the exact identity
\[
 3W+Y=K-q/2+T+x_1/2. \tag{7}
\]
The degree-one term has been retained with its correct sign; the
degree-two term is zero.

Set \(s=q/2+1-\tau(J)\). Pairing the residual edges shows \(s\ge0\).
In any fixed part, select every vertex of degree at least three.
Their incident edge sets are disjoint. A degree-\(d\) selection uses
one vertex in place of the \(d/2\) pairing cost, saving \((d-2)/2\).
Pair the remaining edges, at a rounding cost at most \(1/2\). Summing
these savings over all parts gives \(W\), so one part saves at least
\(W/r\). Hence
\[
 W\le rs. \tag{8}
\]

## 4. Linearize first, then replicate

View edges of \(J\) as \(q\) points. Each original residual vertex
of degree \(d\ge4\) gives a \(d\)-point incidence block. Initially
allow repeated blocks. Their pair codegrees \(\lambda_{AB}\) satisfy
\(\lambda_{AB}\le|A\cap B|\), so
\[
 X=\sum_{\{A,B\}}(\lambda_{AB}-1)_+\le T.
\]
Whenever a pair has codegree at least two, delete one block containing
it. The integer pair excess decreases by at least one and cannot
increase elsewhere. After at most \(T\) such deletions the retained
original-block graph is simple and linear, with sizes in \([4,D]\).
Only auxiliary blocks are deleted here; original residual edges and
the counts \(x_d\) stay fixed.

Give a size-\(d\) original block weight
\(y_d=(d-3)(d-2)/2\). Each deletion loses at most \(y_D\), so the
retained weight \(Y'\) satisfies
\[
 Y'\ge Y-y_D T. \tag{9}
\]
This is valid even when its right-hand side is negative.

Now replicate each retained block of size \(d\) exactly \(d-3\)
times, giving each copy weight \(w_d=(d-2)/2\). The total copy weight
is precisely \(Y'\). The replicated graph has rank at most \(D\)
and maximum codegree at most \(D-3\): every pair lies in at most
one retained original block, with at most \(D-3\) copies. Let \(a\)
be its maximum degree, zero for an empty graph.

If \(a\ge a_0\), Input K colours its copies with at most
\((1+\eta)a\) colours. A colour class has weight at least
\(Y'/((1+\eta)a)\). It is a matching and contains no two copies of
one original block. Select each class member's defining original
vertex and pair all uncovered residual edges. The matching's cover
saving is its sum of \((d-2)/2\), giving
\[
 s\ge Y'/((1+\eta)a). \tag{10}
\]

For a second cover, choose a point of replicated degree \(a\).
Suppose it lies in \(n_d\) distinct retained size-\(d\) blocks.
The other points of those original blocks are disjoint by linearity.
Selecting their defining vertices covers exactly
\(1+\sum(d-1)n_d\) edges at cost \(\sum n_d\). Pairing the remainder
gives
\[
 \tau(J)\le q/2-\frac12\sum(d-3)n_d=q/2-a/2,
 \qquad s\ge a/2. \tag{11}
\]
The star uses each original block once, not its parallel copies.
Multiplying (10)--(11) yields \(Y'\le2(1+\eta)s^2\).

If \(a<a_0\), each copy has at least four points, so there are at
most \(qa_0/4\) copies. Each weight is at most \((D-2)/2\), giving
\(Y'\le q(D-2)a_0/8\). Both cases and (9) imply
\[
 Y\le y_D T+2(1+\eta)s^2+q(D-2)a_0/8. \tag{12}
\]
In particular the colouring theorem is never used below its threshold.

Put \(B=1/2+(D-2)a_0/8\). Combining (7), (8), (12) and \(x_1\ge0\)
gives
\[
 2(1+\eta)s^2+3rs\ge K-(y_D-1)T-qB. \tag{13}
\]
Since \(D\ge4\), \(y_D-1\ge0\).

## 5. The general scalar square and its errors

Define
\[
 z=\sqrt{2D},\quad \alpha=\frac{D-1}{2(D+1)},\quad
 d=1-\frac{1/2+z}{D+1},\quad
 \ell=\alpha q-dr,\quad \beta=\frac12+\frac{D-1}{z}.
\]
Here \(0<d<1\) and \(0<\alpha<1/2\). Indeed
\((D+1/2)^2-2D=(D-1/2)^2>0\). The exact square identity is
\[
 K-(2\ell^2+3r\ell)
 =\frac{2D}{(D+1)^2}(q-\beta r)^2\ge0. \tag{14}
\]
It can be verified by coefficient comparison using \(z^2=2D\).
The accompanying Lean file verifies a denominator-cleared identity
for arbitrary real parameters and its implication.

Let \(b=(1+\eta)s\), \(Z=(y_D-1)T+qB\), and \(E=Z/(3r)\).
Since \(r,s,\eta\ge0\), (13) gives \(2b^2+3rb\ge K-Z\).
Equations (14) and this inequality imply
\[
 b+E\ge\ell. \tag{15}
\]
Otherwise \(\ell-b>E\) and \(\ell>b\ge0\), so
\[
 (2\ell^2+3r\ell)-(2b^2+3rb)
 = (\ell-b)(2(\ell+b)+3r)>3rE=Z,
\]
a contradiction. A negative \(\ell\) is covered automatically.

By (6), \(\ell\le Dr\) and
\(E\le(y_D-1)T/(3r)+DB/3\). If \(s\le Dr\), use
\((1+\eta)s\le s+\eta Dr\) in (15); if \(s>Dr\), the same
conclusion is immediate. Thus \(s\ge\ell-\eta Dr-E\).
Rewrite (5) using the definition of \(s\), and substitute this bound:
\[
\begin{aligned}
 m&\ge Lt-(L/2-1)q+Ls-L\\
  &\ge Lt-(L-c_D+LD\eta)r
             -\frac{L(y_D-1)T}{3r}-\frac{LDB}{3}-L.
\end{aligned} \tag{16}
\]
The \(q\) terms cancel since \(L\alpha=L/2-1\), and
\(Ld=L-c_D\). Set \(\eta=\delta/(LD)\), replace \(T\) by
\(I(H)\), and take
\[
 C_{D,\delta}=L+LDB/3,\qquad
 B=1/2+(D-2)a_0(D,\delta/(LD))/8. \tag{17}
\]
This proves Theorem 2, including empty families and residuals. The
constants may be ineffective through the colouring input.

## 6. Consequences and quantifiers

For Theorem 1, fix any integer \(D\ge4\) and any \(\delta>0\).
Under its hypotheses, (4) gives \(\liminf m_j/r_j\ge c_D-\delta\).
Letting \(\delta\downarrow0\) gives \(\liminf m_j/r_j\ge c_D\).
This holds for every fixed \(D\); their \(c_D\) are unbounded.
Therefore \(m_j/r_j\to+\infty\). No threshold is required to be
uniform in \(D\). For (2), any contrary subsequence with bounded
\(f_{\rm lin}(r)/r\) would supply actual minimizing linear examples
and contradict Theorem 1.

There is a quantitative complementary obstruction. If
\(\tau(H_j)\ge r_j-1\), \(r_j\to\infty\) and
\(m_j/r_j\to C<\infty\), then for each \(D\ge5\), (4) gives
\[
 \liminf I(H_j)/r_j^2\ge\frac{(c_D-C)_+}{A_D}.
\]
Taking the supremum over fixed integers \(D\ge5\) yields a strictly
positive lower bound, because some \(c_D>C\). No optimality is claimed.
Thus every bounded-edge/rank family in this cover class must have
quadratic intersection excess.

This conclusion distinguishes the linear class from the conjectured
\(f(r)=O(r)\) behaviour of the full partite class in [ABW,
Conjecture 2.11]. It does not refute that full-class conjecture. The
random truncated-projective-plane construction in [ABW, Theorem 1.3]
gives a linear \(O(r\log r)\) upper bound on suitable prime-power
subsequences, consistent with our superlinear lower bound. Whether
the correct linear growth is \(r\log r\), or substantially smaller,
is not settled here. The dated comparison report is a limited search,
not a claim of priority.

There is also an explicit cover gap for a bounded edge budget.

**Corollary 3 (bounded-budget cover gap).** Fix a real \(C\ge1\).
There is a constant \(K_C\) such that every linear hypergraph in our
class with \(m\le Cr\) satisfies
\[
 \tau(H)\le\left(1-\frac1{2(C+1)}\right)r+K_C. \tag{18}
\]
More generally the same bound holds with the extra term
\((y_D-1)I(H)/(3r)\), where \(D=\lceil2(C+1)^2\rceil\).

**Proof.** Set this \(D\), \(L=D+1\), and use Theorem 2 with
\(\delta=1/2\). Since
\(2(C+1)^2\le D\le2(C+1)^2+1\), we have
\(c_D\ge2C+5/2\) and \(L\le2(C+1)^2+2\). Consequently
\[
 \frac{c_D-C-1/2}{L}\ge\frac{C+2}{L}
 \ge\frac1{2(C+1)}.
\]
The last inequality follows from
\(L/(2(C+1))\le C+1+1/(C+1)\le C+3/2<C+2\).
Rearrange (3) with \(m\le Cr\), and take
\(K_C=C_{D,1/2}/L\). The excess coefficient is
\(A_D/L=(y_D-1)/3\), proving both statements. \(\square\)

## References and verification

[K] J. Kahn, *Asymptotically good list-colorings*, Journal of
Combinatorial Theory, Series A 73 (1996), 1--59.

[KKKMO] D. Y. Kang, T. Kelly, D. Kühn, A. Methuku and D. Osthus,
*Solution to a problem of Erdős on the chromatic index of hypergraphs
with bounded codegree*, Proceedings of the London Mathematical Society
129 (2024), no. 6, e70011, [arXiv:2110.06181](https://arxiv.org/abs/2110.06181).
Section 1.2 fixes the parallel-copy convention; Theorem 3.1 supplies
the Kahn theorem. The primary statement was inspected.

[S] V. Sivashankar, *An Improved Lower Bound for the Erdős--Lovász
Cover Number Problem*, [arXiv:2606.24878v2](https://arxiv.org/abs/2606.24878v2),
Section 4, for the preceding peeling, linearization and matching/star
framework. Its degree-three lemma is not needed by this theorem.

[ABW] R. Aharoni, J. Barát and I. M. Wanless, *Multipartite hypergraphs
achieving equality in Ryser's conjecture*, Graphs and Combinatorics 32
(2016), 1--15, [arXiv:1409.4833v2](https://arxiv.org/abs/1409.4833v2),
[DOI:10.1007/s00373-015-1575-9](https://doi.org/10.1007/s00373-015-1575-9).

The standard-library checker verifies denominator-cleared polynomial
identities, exact square-root constants and finite replication, matching
and star diagnostics. These diagnostics are not the general proof.
Partial Lean exports check the scalar implications, not the finite
hypergraph reductions or the published colouring theorem. The audit
states the exact scope, and no external mathematician has reviewed it.
