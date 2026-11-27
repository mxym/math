# Scope and sharp asymptotics of the level-optimal OR-tree heuristic

## 1. Model and results

There are \(n=2^k\) distinguishable leaves, \(k\ge1\), with labels
\(L_i\subseteq[m]\); labels need not be distinct. A tree is full and binary.
The label \(L_u\) of each node is the union of the labels of its descendant
leaves. A monotone Boolean query \(q\) is evaluated on the indicator of
\(L_u\). For a distribution \(\mathcal Q\) on such queries write
\[
 P(S)=\mathbb E_{q\sim\mathcal Q}q(S),\qquad
 \mathrm{SLC}(T)=\sum_{u\text{ internal}}P(L_u),\qquad
 O=\min_T\mathrm{SLC}(T).
\]
The minimum includes unbalanced trees. From the leaves to the root,
Algorithm 2 of [EME] uses a minimum-cost perfect matching at each layer,
where joining nodes with labels \(S,T\) costs \(P(S\cup T)\). Call any
tree so obtained a level-optimal (LO) output, without fixing ties.
Write \(L_*=\bigcup_iL_i\) and \(W=P(L_*)\).
Always \(O\ge W\); \(W=0\) forces all costs to be zero.

**Theorem 1 (a strictly larger logarithmic class).** Fix \(K\ge1\).
Split the workload into ordinary disjunctive queries and exceptional
queries (i.e., partition its probability mass). For some finite
join-semilattice \(J\) with \(|J|\le K\), assume there is a map
\(\pi:2^{[m]}\to J\) with
\(\pi(S\cup T)=\pi(S)\vee\pi(T)\), through which every exceptional
query factors. These data may depend on the workload; \(K\) does not.
Then every LO output satisfies
\[
 \mathrm{SLC}(T_{\rm LO})\le (K+2)\log_2 n\; O . \tag{1}
\]
In particular, take a fixed \(B\ge2\) and any \(B\) common disjunctive
tests \(r_j(S)=\mathbf1\{S\cap U_j\ne\varnothing\}\), \(U_j\subseteq[m]\).
Allow arbitrary mixtures of unrestricted disjunctive queries and
arbitrary monotone Boolean combinations of these same \(B\) tests.
This gives \(K=2^B\) and a class strictly containing the disjunctive
workloads, already with \(B=2\). For example, it allows adding a
conjunction of two fixed, possibly large, keyword disjunctions with
unrestricted probability weight. The usual logarithmic lower order
from [EME, discussion after Theorem B.1] is inherited by containment.

**Theorem 2 (maximal and pair-conjunction asymptotics).** For every
instance and LO output,
\[
 \mathrm{SLC}(T_{\rm LO})\le (n/2)\,O . \tag{2}
\]
Let \(b_n\) be the supremum of \(\mathrm{SLC}(T_{\rm LO})/O\) over all
instances with \(O>0\) and all LO outputs, and \(b_n^{(2)}\) the same
supremum with every query a conjunction of two distinct keywords. Then
\[
 \lim_{k\to\infty}\frac{b_{2^k}}{2^k}=\frac12,\qquad
 \lim_{k\to\infty}\frac{b_{2^k}^{(2)}}{2^k}
   =\gamma:=\sum_{h=1}^{\infty} 2^{-h}
          \bigl(1-2^{\,1-2^{h-1}}\bigr)
   =0.358885765068\ldots . \tag{3}
\]
The lower families work for **every** LO output, with a unique
minimum-cost matching on their first level. In particular unrestricted
two-keyword conjunctive workloads refute a logarithmic bound, even
though the existential larger-class conjecture holds by Theorem 1.

When the root is counted, the expected-visited cost is
\(V(T)=1+2\mathrm{SLC}(T)\). Every result about an optimum below then uses
\(V_{\min}=1+2O\). The logarithmic upper bound persists, and the
respective asymptotic worst-case coefficients in (3) for
\(V(T_{\rm LO})/V_{\min}\) are \(1/3\) and \(2\gamma/3\).
These are performance results for a combinatorial heuristic only.

## 2. The logarithmic guarantee

Let \(D(S)\) and \(X(S)\) be the disjunctive and exceptional
contributions to \(P(S)\), with original probabilities, not
separately normalized. Write \(D_h,X_h,C_h=D_h+X_h\) for their
sums over layer \(h\) of the computed tree; \(h=0\) is the leaves.
For any \(S,T\), \(D(S\cup T)\le D(S)+D(T)\), since this holds
for each disjunctive indicator. Thus \(D_{h+1}\le D_h\) for
every matching. Put \(W_X=X(L_*)\).

At any layer, consider the competing perfect matching which pairs
nodes with equal \(\pi\)-value within each type as far as possible.
There are at most \(K\) unmatched nodes, of even total number, and
one pairs them arbitrarily. A within-type pair has exceptional
parent contribution exactly half the sum of its children's
exceptional contributions, by \(\pi(S\cup T)=\pi(S)\vee\pi(T)\) and
idempotence. An unmatched pair's parent contribution is at most
\(W_X\), by monotonicity. The candidate matching therefore has
exceptional total at most \(X_h/2+(K/2)W_X\) and disjunctive total
at most \(D_h\). The minimum matching used by LO, regardless of
ties, satisfies
\[
 C_{h+1}\le D_h+X_h/2+(K/2)W_X
     \le \tfrac12(C_h+D_0+K W_X). \tag{4}
\]
In any comparison tree, every leaf's cost is at most its parent's
cost and each internal node is charged at most twice this way.
Hence \(D_0\le C_0\le2O\), and \(W_X\le W\le O\).
Inducting in (4) gives \(C_h\le\max(C_0,D_0+K W_X)\le(K+2)O\);
summing \(h=1,\ldots,k\) proves (1).
This argument uses fixed \(K\). It does not apply just because
every query has small arity if the list of shared tests is unbounded.

## 3. A universal first-layer bound

Pair the leaves of an arbitrary comparison tree from bottom to top.
In each subtree pair as many as possible by combining any two
unpaired leaves returned by its children, and pass upward a single
unpaired leaf if its subtree size is odd. At the root \(n\) is even,
so this gives a perfect matching, and at most one pair was joined
at each internal node. The union label of that pair is contained
in the node's label, hence costs at most the node's cost. Applying
this to an optimal tree gives total matching cost at most \(O\).
Thus the first LO layer has cost \(C_1\le O\). There are exactly
\(n/2-1\) remaining internal nodes, each costing at most \(W\le O\).
This proves (2). The same reasoning gives
\[
 \mathrm{SLC}(T_{\rm LO})\le O+(n/2-1)W . \tag{5}
\]

## 4. Upper asymptotic constant for pair-conjunction queries

Here \(W>0\) and let \(R=O/W\ge1\). Let \(g_h=n/2^h\) and
\(x_h=C_h/(g_h W)\) be the normalized cost on layer \(h\).
Root-inactive queries contribute nothing on any node, so this is
the expected fraction of accepting nodes when conditioning on an
active query. In particular \(0\le x_h\le1\), and \(x_1\le2R/n\)
by the first-layer bound.

At any \(h<k\), write \(g=g_h\). For a fixed active two-keyword
query let \(c,a,b\) be the counts of nodes containing both, only
the first, and only the second keyword, respectively. Put \(x=c/g\).
In a uniformly random perfect matching each unordered pair has
probability \(1/(g-1)\) of being matched. The number of candidate
pairs accepting at their union is exactly
\[
 c(g-c)+\binom c2+ab .
\]
Its expectation divided by \(g/2\) is at most
\[
 \frac g{g-1}\left(f(x)-\frac{x}{g}\right)
      \le f(x)+\frac1{g-1},\qquad
 f(x)=1-(1-x)^2/2, \tag{6}
\]
using \(4ab\le(g-c)^2\) and \(f(x)\le1\).
The minimum total matching cost is at most the expectation over
one random matching of the whole layer. Average (6) over the
root-active query distribution and use the concavity of \(f\) to get
\[
 x_{h+1}\le f(x_h)+1/(g_h-1). \tag{7}
\]
This is a bound on the actual objective, not a claim that the
matching independently optimizes each query.

For any sequence along which the normalized SLC ratio is bounded
away from zero, \(R\) is bounded: even the trivial bound
\(\mathrm{SLC}\le(n-1)W\) gives ratio divided by \(n\) at most \(1/R\).
So \(x_1\to0\). For each fixed \(h\), induction through (7), with
\(g_h\to\infty\) and \(f\) continuous nondecreasing on \([0,1]\),
gives \(\limsup x_h\le z_h\), where \(z_1=0\) and \(z_{h+1}=f(z_h)\).
Squaring the complement shows \(z_h=1-2^{1-2^{h-1}}\).
Now
\[
  \frac{\mathrm{SLC}(T_{\rm LO})}{nO}
     =\frac1R\sum_{h=1}^k 2^{-h} x_h
     \le \sum_{h=1}^k 2^{-h}x_h .
\]
Truncating after \(H\) loses at most \(2^{-H}\), independently
of the instance. This proves the upper bound \(\gamma\) for
the limsup. The sequence argument applies to suprema too: choose
arbitrarily near-supremal instances at each \(n\) on the limsup
subsequence. If the limsup is zero the bound is automatic.

## 5. Forced matching and lower families

Let \(n=2m_0\), \(m_0=2^{k-1}\ge2\).
Write the leaves \(A_i,B_i\) for \(i=0,\ldots,m_0-1\).
A column is a bit vector \(v\in\{0,1\}^{m_0}\), with a distinct
pair of main keywords \(a_v,b_v\) for each occurrence in a list
of nonconstant columns. Put \(a_v\) in \(A_i\) when \(v_i=0\),
and otherwise put \(b_v\) in \(B_i\). Neither keyword is placed
on the opposite leaf of that same pair. The main workload samples
a column uniformly and queries \(a_v\wedge b_v\), with its total
mass \(1-\eta\).

For control, each leaf \(U\) has a private additional keyword \(p_U\).
Use total mass \(\eta=n^{-2}\), uniform over queries
\(p_U\wedge p_V\) for unordered pairs \(\{U,V\}\) other than
\(\{A_i,B_i\}\). This list is nonempty for \(n\ge4\). The two
lists together form a probability distribution. Every first-layer
pair \(\{A_i,B_i\}\) has cost zero, and every other pair has
positive cost because its private marker query accepts. Thus the
unique zero-cost and minimum-cost matching is the intended one.
This is not an assumption about later ties.

The main cost is zero below the root of the balanced comparison
tree with all \(A_i\) on one side and all \(B_i\) on the other.
It is \(1-\eta\) at the root, because each column is nonconstant.
Any control query accepts precisely at the ancestors (including
itself) of the LCA of its two marked leaves. There are at most
\(k\) such nodes in the comparison tree. Every query accepts at
the root, hence
\[
 1\le O\le 1-\eta+\eta k . \tag{8}
\]
In any LO output, every layer-\(h\) node for \(h\ge1\) joins
\(\ell=2^{h-1}\) distinct blocks \(\{A_i,B_i\}\).
The main query accepts exactly when the corresponding column is
nonconstant on those \(\ell\) indices. This condition uses just the
indices, independently of the order or shape of previous matchings.

**Exact asymptotic pair-conjunction lower bound.** Take the column
list to be all nonconstant bit vectors. For each group of
\(\ell\ge1\) indices its relative main acceptance is exactly
\[
 a_{\ell,m_0}=\frac{1-2^{1-\ell}}{1-2^{1-m_0}} .
\]
Indeed the fraction having both bits under an unconditioned uniform
column is \(1-2^{1-\ell}\), and that event already excludes constant
columns. Each layer has \(g_h\) nodes, so
\[
 \frac{\mathrm{SLC}(T_{\rm LO})}{n}
 \ge (1-\eta)\sum_{h=1}^{k}2^{-h}a_{2^{h-1},m_0}.
\]
With (8) this proves the matching lower limit \(\gamma\) in (3).
No control cost was needed for this lower estimate.

**Polynomial-size variant.** The exponential column list can be
replaced by a list of at most \(m_0^4\) columns, without changing the
limit. Let \(F\) be the field of order \(q_0=m_0^2\). For
\((u,v)\in F^2\) use the column \((\operatorname{Tr}_{F/\mathbb F_2}
(u v^i))_{i=0}^{m_0-1}\), with \(v^0=1\).
For every nonempty subset \(I\) of indices, its parity bias is
\(\Pr_v[\sum_{i\in I}v^i=0]\le(m_0-1)/q_0<1/m_0\):
the polynomial is nonzero of degree at most \(m_0-1\), and the
uniform \(u\)-trace character averages to zero if its multiplier
is nonzero. This is the standard AGHP powering construction,
using the nondegenerate trace pairing. The trace is nonzero since
its linearized polynomial of degree \(q_0/2\) cannot vanish on
all of \(F\). On any group of \(\ell\) indices the all-equal
indicator has the Fourier expansion
\[
 2^{1-\ell}\sum_{I\subseteq\text{group},\ |I|\text{ even}}
                    (-1)^{\sum_{i\in I}b_i},
\]
where \(b_i\) denotes the column bit. Thus the fraction of
unconditioned columns nonconstant on the group is at least
\(1-2^{1-\ell}-1/m_0\). Delete globally constant columns, which
cannot decrease any group's acceptance fraction. At least one
column remains (a pair's all-equal probability is at most
\(1/2+(m_0-1)/(2q_0)<1\)).
The resulting lower sum differs from the desired one by at most
\(1/m_0\). This also gives a polynomial-size explicit family:
the field can be found, for example, by exhaustive search of
degree \(2\log_2m_0\) binary monic polynomials with irreducibility
testing, which is polynomial in \(m_0\); every column can then be
enumerated. Repeated columns are indexed by their separate seeds
and have separate keyword pairs.

**Maximal monotone lower bound.** Use the same columns and private
markers but replace all main queries with the single monotone
query \(\bigvee_v(a_v\wedge b_v)\) at mass \(1-\eta\).
Every singleton block fails it; every two distinct blocks satisfy
it since some column separates those indices. This separation
holds for either column list. Hence exactly the \(n/2-1\) internal
nodes above the first layer accept the main query in every LO
output. The comparison tree in (8) is unchanged. Together with
(2) this proves the maximal limit \(1/2\). The combined query
is not a two-keyword conjunction, so this is a different class.

## 6. Expected number of visited nodes

For each monotone query, every satisfying internal node is
visited because all of its ancestors also satisfy the query.
Each such node causes visits to both its children, and every
node other than the root is visited this way exactly once.
Taking the expectation gives \(V(T)=1+2\mathrm{SLC}(T)\), as in
[EME, Lemma B.3]. This translates any approximation ratio
upper bound \(\mathrm{SLC}(T)\le A O\) with \(A\ge1\) to the
same ratio bound for \(V\). For the sharp asymptotics, write
\[
 \frac{V(T_{\rm LO})}{n(1+2O)}
    = \frac{1}{n(1+2O)}
     +\frac{2W}{1+2RW}\sum_{h=1}^{k}2^{-h}x_h .
\]
Here \(W\le1\) and \(R\ge1\), hence the second prefactor is at
most \(2/3\). If the normalized visited ratio is bounded away
from zero then \(R\) is bounded as before (the prefactor is
at most \(1/R\)). The pair-conjunction upper bound thus follows
from the same layer induction. For general monotone workloads
use (5) directly: the first layer's term normalized by
\(n(1+2O)\) is at most \(1/n\), and all later nodes cost at
most \(W\). The lower families have \(W=1\) and \(O\to1\)
by (8), giving the two asserted visited-ratio coefficients.
