# Best-first OR trees: an exact worst-case comparison

## 1. Model and statement

Let \(L\) be a labeled \(n\)-element leaf set, \(n\ge2\). Each leaf
\(i\) has a set \(A_i\) of keywords. Relabeling the same keyword set on
different leaves is allowed: the leaves remain distinct. For a nonempty
\(C\subseteq L\) let
\[
 w(C)=\Pr_{q\sim\mathcal Q}\!\left[q\!\left(\bigcup_{i\in C}A_i\right)=1\right],
\]
where each \(q\) is a monotone Boolean formula. Thus \(w\) is
inclusion-monotone with values in \([0,1]\). The label of an internal
node in a full rooted binary OR tree is the union of its descendant
leaf labels. Its cost is \(w(C)\) for its descendant leaf set \(C\).
Write \(C_w(T)\) for the sum over internal nodes, including the root,
and \(W=w(L)\). Best-first starts with singleton blocks and repeatedly
joins a pair of distinct current blocks minimizing \(w(C\cup D)\).
Each merge creates one internal node. It breaks ties arbitrarily.

Set \(m=\lfloor n/2\rfloor\). For any best-first tree \(G\) and any
full binary comparison tree \(T\) on these leaves, we prove
\[
 C_w(G)-C_w(T)\le (m-1)W. \tag{1}
\]
This additive assertion holds for any nonnegative inclusion-monotone cost
function, not only probabilities. In the probability model, let
\(O=\min_T C_w(T)\). Then best-first has internal-sum approximation
factor at most \(m\) (with zero cost if \(O=0\)). With the root
counted as a visit, its expected-visits approximation factor is at most
\((2m+1)/3\). Section 3 proves these constants are sharp for each
\(n\), including when performance is measured using the best
tie-breaking of the greedy procedure.

## 2. Threshold proof

Fix \(\lambda\ge0\). Call a merge cheap when its output cost is at most
\(\lambda\). At any time, if the smallest available merge cost is
\(\mu\), merging a minimizing pair preserves every candidate not
involving that pair. Any newly available candidate has an output
containing the union just merged, so by monotonicity its cost is at
least \(\mu\). Thus best-first's merge costs never decrease. In
particular, its cheap merges form an initial segment, followed only by
merges of cost greater than \(\lambda\). At the end of that segment,
let \(g\) be the number of current blocks. No pair of these blocks can
merge cheaply (including vacuously when \(g=1\)). Consequently the
number of greedy merges having cost greater than \(\lambda\) is exactly
\(g-1\).

In \(T\), retain every cheap internal node and every leaf, even a leaf
whose own weight exceeds \(\lambda\). If a cheap internal node is
retained, its entire descendant subtree is retained by monotonicity.
The maximal retained subtrees therefore partition \(L\) into \(r\)
blocks. The contraction of these subtrees removes every cheap internal
node, leaving a full binary tree with \(r\) leaves and \(r-1\)
internal nodes. Thus exactly \(r-1\) internal nodes cost more than
\(\lambda\).

Each of these \(r\) blocks contains at most one element that is still
a singleton in the greedy partition. Indeed, if it contained two, it
would have a cheap internal root containing those leaves. Their pair
would also be cheap by monotonicity and would still be available to
greedy, a contradiction. This reasoning also covers comparison blocks
that are single leaves, whether cheap or not. If greedy has \(s\)
singleton blocks, then \(s\le r\) and
\[
 n\ge s+2(g-s),\qquad
 g\le\left\lfloor\frac{n+r}{2}\right\rfloor. \tag{2}
\]
If \(r=1\), the comparison root is cheap, hence every union is cheap
and \(g=1\). Otherwise subtracting \(r\) in (2) gives
\[
 (g-1)-(r-1) \le \left\lfloor\frac{n-r}{2}\right\rfloor \le m-1 .
\]
The latter case occurs exactly at \(0\le\lambda<W\).
The sum of nonnegative internal weights equals the integral of the
number of weights strictly greater than \(\lambda\) over
\([0,\infty)\), since \(a=\int_0^\infty 1_{\lambda<a}\,d\lambda\).
Integration proves (1).

Taking an optimal comparison, \(W\le O\) because the root is internal,
so \(C_w(G)\le mO\). For visits, the root is tested once, and every
internal node satisfying the query causes precisely its two children
to be visited. Such a node is always reached, as its ancestors'
labels contain its label and the query is monotone. Therefore expected
visits equal \(1+2C_w(T)\). Since \(W\le1\) and \(W\le O\),
\[
 \frac{1+2C_w(G)}{1+2O}
 \le 1+\frac{2(m-1)W}{1+2O}
 \le 1+\frac{2(m-1)}3
 =\frac{2m+1}3.
\]
Here \(W/(1+2O)\le W/(1+2W)\le1/3\), including \(W=0\).

## 3. Sharpness without reliance on tie-breaking

For \(n=2\) there is one merge, so both ratios are 1. For \(n\ge3\)
partition the leaves into \(A,B\), with \(|A|=\lceil n/2\rceil\) and
\(|B|=m\). Each leaf is labeled with a single distinct keyword; identify
the keyword with its leaf. Choose a cross matching \(M\subset A\times B\)
of size \(m-1\) if \(n=2m\), or \(m\) if \(n=2m+1\).
The following formulas are monotone disjunctions of two-keyword
conjunctions:
- \(q_0\): OR of \(a\land b\) over every \((a,b)\in A\times B\setminus M\),
  i.e. over the cross pairs not in the matching.
- \(q_1\): OR of \(u\land v\) over distinct pairs wholly inside \(A\)
  or wholly inside \(B\).

Both formulas are nonempty for \(n\ge3\). Draw \(q_1\) with probability
\(\epsilon\), otherwise \(q_0\), where \(0<\epsilon<1/n\).
A set of at least two leaves has cost zero exactly when it is one pair
of \(M\): \(q_1=0\) allows at most one leaf from each side, and then
\(q_0=0\) is precisely the matching condition. As long as an edge of
\(M\) is still unmerged, both of its leaves remain singleton blocks
throughout the zero-cost stage. Therefore every greedy run merges all
\(|M|\) of these legal pairs before paying anything. There are then
exactly \(m+1\) blocks: the matched pairs and the two unmatched
singletons in the even case, or the pairs and one unmatched singleton
in the odd case.

At that stage, the union of any two blocks contains a cross pair not in
\(M\). If there is a matched pair in the union, any third leaf is joined
to its opposite-side endpoint by an edge outside \(M\); otherwise the
two remaining singleton leaves are unmatched on opposite sides. This
property persists under later merges by monotonicity. The \(m\)
remaining merges consequently have cost at least \(1-\epsilon\). In
the even case, precisely the initial pair of unmatched singletons is a
candidate realizing cost \(1-\epsilon\), so it is selected first and
every other positive merge costs 1. In the odd case any union of two
remaining blocks contains at least three leaves hence also satisfies
\(q_1\); every positive merge costs 1. Thus the exact greedy cost is
\(m-\epsilon\) for even \(n\ge4\), or \(m\) for odd \(n\ge3\).

For a comparison, build one tree on \(A\) and one on \(B\), then join
at the root. This costs \(1+(n-2)\epsilon\), since every non-root
internal node is pure-side. Optimality of this value for \(n\ge4\)
can also be checked directly: a tree with at least two \(q_0\)-true
nodes costs at least \(2(1-\epsilon)>1+(n-2)\epsilon\). With only the
root \(q_0\)-true, its two children must each be pure-side or a matched
pair (a mixed \(q_0\)-false set has exactly its one matched pair). A
matched pair cannot occur as such a child: its complement contains
both sides and at least three leaves if \(n\ge5\), or the two
unmatched leaves if \(n=4\), so the complement satisfies \(q_0\).
Thus the root children are \(A,B\), proving the cost. For \(n=3\)
the matched pair and the remaining leaf can join directly and have
optimal cost 1.

As \(\epsilon\downarrow0\), the optimum tends to 1 (the root costs
1), while every greedy cost tends to \(m\). These examples approach
the additive and both multiplicative upper bounds for each \(n\).
Taking \(\epsilon=1/(2n)\), for example, gives an unbounded linear
ratio in the number of leaves, with no choice of tie-breaking able to
avoid it. Using instead only \(q_0\), the same optimum is exactly 1.
A legal tie-breaking can select every matched pair at cost zero first,
then necessarily pays 1 for each of the \(m\) remaining merges; this
attains both upper bounds exactly (this last claim is not for every
tie-breaking).

## 4. Restricted workloads and scope

For disjunctive queries, each query corresponds to a subset of the
leaves: those whose own labels contain at least one of the queried
keywords. The query is true on a cluster exactly when the two subsets
intersect. Consequently the cost is a weighted coverage function,
and the worst-case construction of Section 3 is not of that type.
The standard SmallestOutput analysis for BINARYMERGING already implies
a logarithmic bound for this restricted case, as follows. Set
\(L_0=\sum_i w(\{i\})\). A query with \(s>0\) satisfying leaves
has at least \(s-1\) satisfying internal nodes in every tree: the
minimal rooted subtree containing the root and all these leaves is
connected and has at most two children per node, and has precisely
\(s\) leaves. Averaging gives \(L_0\le O+W\).
When there are \(k\) greedy blocks, subadditivity gives total block
weight at most \(L_0\). The cheapest pair output is no greater than
the sum of the two smallest block weights, at most \(2L_0/k\).
Summing gives \(C_w(G)\le 2(H_n-1)(O+W)\), where
\(H_n=\sum_{k=1}^n 1/k\). This is a restricted-workload translation
of the prior logarithmic bound, not a new constant-factor or
matching lower bound for coverage or uniform single-keyword queries.

The exact ratios above refer only to abstract OR trees with fully known
query distribution and exact minimization in each greedy step. They
concern an efficiency objective, not a cryptographic security property,
implementation, or learned query behavior.
