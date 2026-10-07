# A nineteen-edge necessary condition for rank-six Ryser counterexamples

7 October 2026. Complete written proof with three Lean scalar certificates
and independent exact degree-pattern replay. No unrestricted resolution or
priority claim is made.

## 1. Statement

All hypergraphs here are finite and simple: duplicate edges are discarded,
since they do not change a cover or a matching. An $r$-partite $r$-uniform
hypergraph has $r$ disjoint vertex parts and exactly one vertex of each part
in every edge. It is intersecting if every two edges meet. A vertex cover
meets every edge, and $\tau(H)$ is its minimum size. Only vertices appearing
in some edge are counted in a part. Write $N=|E(H)|$ and $d(v)$ for a vertex
degree, the number of edges containing it.

**Theorem.** Every intersecting six-partite six-uniform hypergraph with
at most eighteen distinct edges has a vertex cover of size at most five.
Equivalently, any rank-six counterexample to the intersecting Ryser bound
must have at least nineteen distinct edges. There is no restriction on the
number of vertices in a part.

For an empty hypergraph the conclusion is immediate. For a nonempty
intersecting hypergraph, any one edge covers every edge, so $\tau(H)\leq6$.
We therefore assume $\tau(H)=6$ and derive a contradiction when $N\leq18$.

This theorem does not prove the rank-six conjecture. The bound concerns
the six-partite subclass, not all six-uniform intersecting hypergraphs.
In particular, it is not a statement that the general Erdős--Lovász
cover-number function $q(6)$ is at least nineteen.

## 2. Degrees and repeated intersections

**Lemma 1.** Every active vertex has degree at least two, and every part
has at least six active vertices. Consequently $N\geq12$ and a part has
at most $\lfloor N/2\rfloor$ active vertices.

**Proof.** All vertices in one part form a cover, proving the second
assertion. If $v$ has degree one and belongs to edge $e$, the five vertices
$e\setminus\{v\}$ cover $e$. Every other edge intersects $e$ and cannot
contain $v$, so it meets those same five vertices. This contradicts
$\tau=6$. Degrees in any one part sum to $N$, proving the remaining claims.

**Lemma 2.** For any two distinct vertices $v,w$,
\[
 |E(v)\cup E(w)|\leq N-7,\qquad
 |E(v)\cap E(w)|\geq\max(0,d(v)+d(w)-N+7),
\]
where $E(v)$ denotes the edges containing $v$.

**Proof.** If at most six edges remain uncovered by $v,w$, pair up those
edges. Each pair has a common vertex, which covers both; if one edge is
left over, choose a vertex in it. At most three further vertices cover
the remainder. Along with $v,w$ this is a cover of size at most five.
Hence at least seven edges remain. Inclusion--exclusion gives the second
assertion.

For each part, its nonincreasing degree sequence is an integer partition
of $N$ into at least six integers, all at least two. Define
\[
 S=\sum_v\binom{d(v)}2,
\]
and, summing unordered pairs of different parts and all their vertex pairs,
\[
 B_0=\sum_{i<j}\ \sum_{v\in V_i,w\in V_j}
           \binom{\max(0,d(v)+d(w)-N+7)}2.
\]
Here $\binom t2=t(t-1)/2$ for every nonnegative integer $t$, including
$t=0,1$.

**Lemma 3 (necessary degree inequality).**
\[
 F:=5\big(S-\binom N2\big)-2B_0\geq0.
\]

**Proof.** For different edges $e,f$, set $s_{ef}=|e\cap f|$.
Intersection and simplicity imply $1\leq s_{ef}\leq5$. Double-counting
a pair of edges and a common vertex gives
\[
 S=\sum_{e<f}s_{ef}.
\]
Double-counting two edges and two common vertices gives
\[
 \sum_{v<w}\binom{|E(v)\cap E(w)|}2
       =\sum_{e<f}\binom{s_{ef}}2.
\]
Vertex pairs in a single part have codegree zero. By Lemma 2 and
monotonicity of the integer binomial coefficient, the left side is at
least $B_0$. Since $s(s-1)\leq5(s-1)$ for $1\leq s\leq5$,
\[
 2B_0\leq2\sum_{e<f}\binom{s_{ef}}2
    \leq5\sum_{e<f}(s_{ef}-1)=5\big(S-\binom N2\big).
\]
This proves the inequality. No linearity assumption is imposed on $H$.

## 3. Excluding twelve through seventeen edges

For a part with $q\geq6$ active vertices, write $d_i=2+a_i$, with
$a_i\geq0$ and $\sum a_i=N-2q$. Convexity of $\binom d2$ shows that
its sum is largest when all excess is assigned to one vertex:
\[
 \sum_i\binom{d_i}2\leq\binom{N-2q+2}2+q-1.
\]
One can verify this directly by moving one unit of excess from a smaller
positive $a_i$ to a largest $a_j$: the sum does not decrease. The displayed
maximum decreases when $q$ increases within its feasible range. Indeed,
with $D=N-2q+2$, its change on replacing $q$ by $q+1$ is $4-2D\leq0$.
Hence it is at most $\binom{N-10}2+5$.

For $N=12,13,14,15$ the respective partwise maxima are $6,8,11,15$.
Their sixfold sums $36,48,66,90$ are smaller than
$\binom N2=66,78,91,105$. This contradicts even $S\geq\binom N2$,
which follows from intersection.

### 3.1 Sixteen edges

When $N=16$, a part has six, seven or eight vertices. The six-vertex case
has four units of excess over degree two. Its partitions are
$(4)$, $(3,1)$, $(2,2)$, $(2,1,1)$ and $(1,1,1,1)$.
Thus, if its maximum degree is six, its degree-pair sum is at most 20;
otherwise that sum is at most 17. The seven- and eight-vertex cases have
two and zero excess units and also satisfy the latter bound.

Let $k$ be the number of parts with maximum degree six. Then
$S\leq102+3k$. Select one degree-six vertex in each such part. Lemma 2
gives codegree at least $12-16+7=3$ for every selected pair, so
$B_0\geq3\binom k2$. Therefore
\[
 F\leq5(102+3k-120)-6\binom k2
      =-63-3(k-3)^2<0,
\]
contradicting Lemma 3.

### 3.2 Seventeen edges

For $N=17$, the maximum degree $D$ in any part is in $\{3,4,5,6,7\}$.
The following partwise bounds follow by partitioning the five excess
units in the six-vertex case; seven or eight vertices give only three
or one excess units and no larger values:

| Maximum degree $D$ | 3 | 4 | 5 | 6 | 7 |
| --- | --- | --- | --- | --- | --- |
| Maximum $\sum\binom{d_i}2$ | 16 | 18 | 20 | 22 | 26 |

For clarity, the seven partitions of five are
$(5),(4,1),(3,2),(3,1,1),(2,2,1),(2,1,1,1),(1,1,1,1,1)$;
adding two to each entry and padding to length six verifies the table.
Let $k,l,t,s$ be the numbers of parts with maxima $7,6,5,4$, respectively;
the remaining parts have maximum three. Then
\[
 S\leq96+10k+6l+4t+2s.
\]
Select a maximum-degree vertex in each part. The positive contributions
from pairs of selected vertices give
\[
 B_0\geq6\binom k2+3kl+kt+\binom l2.
\]
Here Lemma 2 has threshold $N-7=10$: maxima $7+7,7+6,7+5,6+6$ give
codegree lower bounds $4,3,2,2$, respectively. Hence
\[
 \begin{split}
 F\leq{}&-200+50k+30l+(20-2k)t+10s\\
        &-12\binom k2-6kl-2\binom l2.
 \end{split}
\]
For $k\leq5$, use $20-2k\geq10$ and $t+s\leq6-k-l$ to replace both
terms by $(20-2k)(6-k-l)$. For $k=6$, necessarily $l=t=s=0$, and the
same replacement is valid. Simplification gives
\[
 F\leq-80+24k+11l-(2k+l)^2
      =-44-(2k+l-6)^2-l<0.
\]
Again Lemma 3 is contradicted.

## 4. Eighteen edges: six sufficient degree patterns

When $N=18$, every part has $q=6,7,8$ or 9 vertices and hence
$6,4,2$ or zero excess units above degree two. There are exactly nineteen
possible nonincreasing degree patterns. We reduce them to the following
six patterns for the purpose of maximizing the necessary expression $F$:

| Type | Degree pattern | Degree-pair sum $S_i$ |
| --- | --- | --- |
| A | $(8,2,2,2,2,2)$ | 33 |
| B | $(7,3,2,2,2,2)$ | 28 |
| C | $(6,4,2,2,2,2)$ | 25 |
| D | $(5,5,2,2,2,2)$ | 24 |
| E | $(5,4,3,2,2,2)$ | 22 |
| F | $(4,4,4,2,2,2)$ | 21 |

For degree patterns $P,Q$, define their mutual contribution
\[
 b(P,Q)=\sum_{x\in P,y\in Q}\binom{\max(0,x+y-11)}2.
\]
If a pattern is replaced by another with no smaller $S_i$ and no larger
$b$ against every possible partner, the value $F$ cannot decrease.
This replacement need not be realizable as a hypergraph; it is an upper
bound on the purely numerical necessary expression.

Here is the complete justification of the reduction. If the maximum
degree is eight or seven, A or B is the only pattern. If it is six,
the possibilities are $(6,4,2,2,2,2)$,
$(6,3,3,2,2,2)$ or $(6,2,2,2,2,2,2)$; C has largest $S_i$ and their
$b$ rows agree against every partner. Indeed the other entries are at
most four, and $4+8-11=1$ contributes zero. If the maximum is five and
occurs twice, D is the only possibility. If it occurs once, E has the
largest $S_i$, equal to 22, and the other entries, again at most four,
do not affect $b$. Finally, if the maximum is at most four then every
$b$ contribution is zero, and F has largest $S_i$, equal to 21. The
latter maximum follows from the partitions of six into entries at most
two (for six vertices), with smaller sums for seven through nine vertices.
This covers all nineteen patterns.

The symmetric $b$ matrix for A through F is
\[
 \begin{pmatrix}
 10&6&3&2&1&0\\
 6&3&1&0&0&0\\
 3&1&0&0&0&0\\
 2&0&0&0&0&0\\
 1&0&0&0&0&0\\
 0&0&0&0&0&0
 \end{pmatrix}.
\]
For example, A versus D contains two degree-eight/degree-five pairs,
each with codegree lower bound two, giving entry 2.

Let $a,b,c,d,e,f$ count the six reduced types, so they are nonnegative
integers with sum six. Within each type use $\binom a2$, etc., to count
pairs of parts. Combining the displayed sums and matrix gives
\[
 \begin{split}
 F\leq{}&-10a^2-12ab-6ac-4ad-2ae+70a\\
         &-3b^2-2bc+38b+20c+15d+5e-135.
 \end{split}
\]

**Lemma 4 (integer certificate).** This polynomial is at most $-1$ for
all nonnegative integer $a,b,c,d,e,f$ with sum six.

**Proof.** Substitute $d=6-a-b-c-e-f$. The polynomial becomes
\[
 G(a,b)+(5-2a-2b)c+(-10+2a)e+(-15+4a)f,
\]
where
\[
 G(a,b)=-6a^2-8ab+31a-3b^2+23b-45.
\]
If $a\leq3$, the coefficients of $e,f$ are negative. When $a+b\geq3$,
the coefficient of $c$ is also negative. In that case drop all three
terms and use the exact completion of squares
\[
 G(a,b)=-\tfrac78
      -3\big(b-\tfrac72+\tfrac43(a-\tfrac14)\big)^2
      -\tfrac23(a-\tfrac14)^2<0.
\]
When $a+b\leq2$, take $c\leq6-a-b$ and bound the nonnegative coefficient
of $c$ by its maximum. The six possibilities
$(a,b)=(0,0),(0,1),(0,2),(1,0),(1,1),(2,0)$ give respective upper bounds
$-15,-10,-7,-5,-4,-3$.

For $a=4$, the coefficients of $c,e$ are negative and that of $f$ is
one; $b+f\leq2$. Directly
\[
 G(4,b)+f=-17-9b-3b^2+f\leq-15.
\]
For $a=5$, only $f$ can have a positive coefficient, now five, and
$b+f\leq1$. Thus $G(5,b)+5f=-40-17b-3b^2+5f\leq-35$.
For $a=6$ every other count is zero and the value is $-75$.
The polynomial is integer-valued and always negative, so it is at most
$-1$. Equality in the scalar bound occurs at $b=4,d=2$ with all other
counts zero. This is a numerical degree-pattern equality only, not a
hypergraph satisfying the necessary conditions.

Lemma 4 makes the necessary expression $F$ negative, contradicting
Lemma 3. This finishes the theorem.

## 5. Exact and formal verification, and scope

`check_degree_bound.py` independently enumerates all nineteen part-degree
partitions and their 134,596 unordered six-part combinations. It expands
the mutual degree contributions directly and verifies that the maximum
necessary expression is $-1$. A separate pass uses the six reduced types
and all 462 type-count combinations, checking the domination reduction
and the polynomial formula. It also replays the smaller-edge tables and
includes deliberately corrupted certificate controls. These finite
enumerations are exact integers, not graph search or solver output.

The written proof does not require the 134,596-case enumeration: Lemma 4
provides a small-case and sum-of-squares certificate. Three exported Lean
theorems verify the sixteen-, seventeen- and eighteen-edge scalar
inequalities for every input in their stated domains. The hypergraph
double-counting and degree-pattern reduction are written proofs, not
formalized hypergraph theorems. The Lean exports have no `sorryAx` or
new postulated axiom. No external human review is claimed.

The [preliminary source comparison](../novelty-assessment/2026-10-07-ryser-nineteen-edge-precedent.md)
records a 2026 general lower bound $q(r)\geq3r-4$, giving $q(6)\geq14$,
from Varun Sivashankar, *An Improved Lower Bound for the Erdős--Lovász
Cover Number Problem*, [arXiv:2606.24878v2](https://arxiv.org/abs/2606.24878v2).
The separate known $f(6)=13$ for the six-partite class concerns
$\tau\geq5$, with a $\tau=5$ construction. Neither statement is the
nineteen-edge theorem above. Limited comparison does not establish
priority or absence of a more specialized prior theorem.

The unrestricted rank-six question remains unresolved here. For nineteen
edges the present necessary degree inequalities admit numerical patterns,
so the same argument cannot simply be repeated to claim twenty edges.
Those patterns are not known hypergraphs or counterexamples. Searching
for an actual realization, or identifying a stronger structural
obstruction, is the next mathematical task.
