# Best-first OR-tree approximation

All logarithms in asymptotic formulas below are base two. For n ≥ 2 fixed leaves indexed by [n], let a_i be each leaf's keyword indicator. For a nonempty cluster U⊆[n], its label is the bitwise OR of the a_i it contains. Let Q be any distribution of monotone Boolean formulas in the dictionary keywords, and put w(U) equal to the probability that a draw from Q is true on that label. The inclusion U⊆U' implies w(U)≤w(U'), by monotonicity of each query. Each w is in [0,1]. Denote the common root weight by R=w([n]).

For a full binary tree T, write S(T)=sum of w(U) over all internal clusters, including the root. The best-first rule begins with singleton clusters and repeatedly merges a pair of current clusters for which w(their union) is minimum, allowing arbitrary ties. Write G=S(T_G) for any resulting tree and O=min_T S(T) over all full binary trees, with no height restriction.

The expected number of visited nodes in the root-tested traversal is V(T)=1+2 S(T), as in the source's Lemma B.3. Indeed the root is visited, and each other node is visited just when its parent satisfies the query: if the parent satisfies, every ancestor satisfies by monotonicity, and both its children are visited even if their own tests will fail. Leaves are accounted for by their parents; neither leaf acceptance nor a second root cost is added to S. Minima of V and S select the same tree, but their ratios differ. The paper also mentions skipping a redundant root test when its label and satisfaction are known; in that variant, when the root is always satisfied, visited cost is 2 S and the ratio is the S ratio. A further nonnegative tree-independent cost added to the root-tested visit count can only improve a ratio to the optimum.

## 1. Universal sharp upper bounds

**Theorem 1.** Put k=floor(n/2). For every monotone workload and every tie-breaking,

    G−O ≤ (k−1) R,    G ≤ k O,
    (1+2G)/(1+2O) ≤ (2k+1)/3.                              (1)

All bounds are sharp in the senses specified in §2. The first two bounds apply even to any nonnegative monotone set weight before normalization into probabilities.

First the values of the greedy merges are nondecreasing. If the chosen merge of A,B has weight u, all unions of unchanged clusters had weight at least u; all newly introduced unions with A∪B also have weight at least u by monotonicity. For a threshold τ with 0<τ≤R, stop the greedy rule just before the first merge with weight at least τ, so all merges thus far had weight strictly less than τ. This is exactly the first time all available pair-union weights are at least τ. It exists since the final merge is the root. If k_τ is the number of clusters in this partition, at least 2k_τ−n are singleton clusters, since all other clusters contain at least two leaves. Subsequent merges, precisely k_τ−1, all cost at least τ; write G_τ=k_τ−1.

For an optimum tree, start at its root and stop whenever a singleton leaf or a cluster of weight less than τ is reached. The resulting frontier of ℓ_τ clusters forms the leaf set of a pruned full binary tree whose internal clusters are exactly the optimum tree's clusters of weight at least τ. Indeed any cluster of weight at least τ has only such ancestors, and no cluster of weight less than τ can contain a heavier cluster. Thus O_τ=ℓ_τ−1 counts internal costs at least τ. The root is heavy, so ℓ_τ≥2. No frontier cluster contains two of the greedy singleton blocks: if it contained two, it would be a nonsingleton cluster of weight less than τ, but the two singleton leaves are a candidate greedy pair at the stopping state with union of weight at least τ and their union is contained in the purported cluster. Hence ℓ_τ≥2k_τ−n, as well as ℓ_τ≥2.

Consequently 2(k_τ−ℓ_τ)≤n−ℓ_τ≤n−2, so the integer difference G_τ−O_τ=k_τ−ℓ_τ is at most floor((n−2)/2)=k−1. In particular G_τ≤O_τ+k−1≤k O_τ, since O_τ≥1. This includes n=2,3, where k=1. For τ>R all internal weights are below τ. Integrating the threshold counts on (0,R], each internal node contributes exactly its weight, independent of endpoint conventions. We get G−O≤(k−1)R, and O≥R since the optimum includes the root, giving G≤kO. If R=0 all costs are zero; the inequalities still hold and the visit ratio is one. For general R∈[0,1],

    (1+2G)/(1+2O)
      ≤ 1+2(k−1)R/(1+2O)
      ≤ 1+2(k−1)R/(1+2R)
      ≤ 1+2(k−1)/3 = (2k+1)/3.

The same argument would compare the greedy tree with any fixed comparison tree just by replacing O by its cost.

## 2. A two-DNF family that reaches the bounds

For n≥4, split the leaves into a left and right side of sizes ceil(n/2) and floor(n/2). Give each leaf its own unique keyword, so a cluster contains precisely the keywords of its members. Designate b pairwise disjoint cross-side pairs, with b=k−1 for n=2k and b=k for n=2k+1. This leaves exactly one unmatched leaf on each side in the even case and one unmatched left leaf in the odd case. All cross pairs not designated are called forbidden. This is a complete bipartite graph of forbidden pairs with a disjoint matching removed.

Let Q_main be the OR of the two-keyword conjunctions over all forbidden cross pairs. Let Q_side be the OR of the two-keyword conjunctions over all same-side pairs from either side. These are monotone DNFs allowed by the source's model. They may have no satisfying leaf, which is allowed and does not prevent internal or root tests from succeeding. Both are true at the full root. Consider the workload choosing Q_main with probability 1−λ and Q_side with probability λ, where 0<λ<1/(n−1). Pure nonsingleton clusters cost λ. A designated cross pair costs zero, a forbidden two-leaf cross pair costs 1−λ, and a mixed cluster of three or more leaves costs one (at least two on one side, and some forbidden cross pair since the designated pairs form a matching).

In the initial greedy phase, as long as any designated pair has not been merged, it is a zero-cost pair of singleton clusters. The only available zero-cost merges are these designated pairs: existing mixed designated blocks are already of size two and any merger involving one is mixed of size at least three; unions of pure same-side singletons cost λ and any other cross pair is forbidden. Inductively every tie-breaking first merges exactly the b designated pairs, at zero cost.

In the even case the remaining clusters are k−1 mixed blocks and the two unmatched opposite-side singletons. Their union is the only prospective merge of weight 1−λ, and all others cost one. The rule merges these singletons next; the remaining k mixed blocks then charge one for each of their k−1 merges. Thus G=k−λ. In the odd case there are k mixed blocks and one unmatched left singleton; every prospective merge now costs one, so G=k. These formulas hold for every tie-breaking.

The tree that makes both root children pure side trees costs 1+(n−2)λ, since its only main-query trigger is the root and it has n−2 pure proper internal clusters. This cost is strictly below 2−λ by the bound on λ. In any optimum no proper internal cluster can trigger Q_main, because even one would add at least 1−λ to the root cost one. Every proper mixed cluster that avoids the main query must be exactly a designated cross pair. If such a cluster occurs, it must be an entire root child: the next proper ancestor would have three or more leaves, be mixed and trigger Q_main. The complementary root child then contains both sides since both initial sides have at least two leaves. For n≥5 this complementary child has at least three leaves, contradicting the absence of a proper main trigger. For n=4 it consists of the two unmatched leaves (there is only one designated pair), a forbidden cross pair. Thus no proper mixed cluster exists, and every optimum has two pure root children, with all proper internal clusters costing λ. We obtain exactly

    O=1+(n−2)λ,    G=k−λ (even n) or k (odd n),    R=1.       (2)

Letting λ down to zero along positive rationals proves the lower supremum in (1) for every tie-breaking. At λ=0, a permissible sequence of ties still merges all designated pairs first, and all subsequent merges then trigger the main query. That greedy sequence reaches G=k with O=1, attaining the bounds, though this exact equality need not hold for other ties at λ=0. For n=2,3 the upper bound already states exact optimality and instances with positive root weight give ratio one. Thus the worst-case suprema of expected visits and positive-optimum S ratios are exactly (2floor(n/2)+1)/3 and floor(n/2), respectively.

## 3. Positive bound for disjunctions

**Proposition 2.** If Q is supported on disjunctions of individual keywords (including a single keyword), then every best-first tree satisfies

    G ≤ 4 (H_n−1) O,                                        (3)

where H_n=sum_{r=1}^n 1/r. This extends to all nonnegative monotone subadditive set weights. It also bounds the visit ratio whenever O>0, and the visit ratio is one if O=0. The universal bound (1) may be stronger for small n.

Each disjunctive query succeeds on the union of two labels just when it succeeds on at least one of them. This makes the weight subadditive, and for an arbitrary such weight the sum of the weights of the current clusters is at most W=sum_i w({i}), since they partition the leaves. When r≥2 clusters remain, the sum of the two smallest cluster weights is at most 2W/r (for instance by averaging all unordered pairs). The union of that pair costs at most this sum, and greedily chosen cost cannot exceed it. Sum over r=n,n−1,...,2 to get G≤2W(H_n−1). For any comparison tree, charge each leaf weight to its own parent; monotonicity and at most two leaf children per internal node give W≤2 S(T). In particular W≤2O and (3) follows. Since 4(H_n−1)≥1 when n≥2, adding the same unit root constant to twice S can only decrease the bound on the visit ratio.

## 4. Even uniform single-keyword queries preclude a constant

**Theorem 3.** On an infinite sequence of instances with n files, exactly four keywords per file, and the query uniform over individual dictionary keywords, every best-first tree has S ratio Omega(log n/log log n). The same asymptotic lower bound holds for the root-tested visit ratio. This leaves a loglog gap with (3); neither a logarithmic lower bound nor a sharp single-keyword ratio is claimed.

Let c≥2 be a power of two, put h=c and s=c^h, and use the subfield F_c⊆F_s. Let r=s² and n=cr=c^(2c+1). Index the files by a point p=(x,y)∈F_s² and a direction j∈F_c; each file (p,j) contains four keywords:

1. the point keyword P_p;
2. two different column keywords C_(j,1), C_(j,2), shared by all files of direction j;
3. the line keyword L_(j,y−jx), shared by those in column j at that line.

There are r+2c+cs different keywords and all are present. For uniform single-keyword queries, w is the number of distinct keywords divided by this dictionary size, so construction and ratios concerning S can be computed entirely with unnormalized integer weights. In each column j the files partition into s line groups of size s. Lines of distinct slopes intersect at exactly one point over F_s: solve y−jx=u, y−j'x=u' using j≠j'. Lines of the same slope with different intercepts are disjoint.

### 4.1 Every tie-breaking first finishes all line groups

Before the first inter-group merge, all clusters lie within a single line group. For two such current clusters of sizes a,b, union weights are as follows.

- Same group: row points disjoint because the leaves within one column are distinct, and two column keywords and one common line keyword remain. Weight a+b+3.
- Same column, distinct groups: disjoint point sets, two column keywords, two line keywords. Weight a+b+4.
- Distinct columns: at most one point keyword is shared, four column keywords, two line keywords. Weight at least a+b+5.

Initially all clusters are singletons. For each d=1,2,4,...,s/2, inductively start a phase in which all clusters have size d inside individual groups. Each group starts the phase with s/d clusters, an even integer. During the phase, each merge of two d-clusters in one group removes two from that group's remaining d-count and creates one 2d-cluster; the d-count remains even. While any d-cluster remains, some group still has at least two of them. Thus the global minimum union weight is 2d+3, and by the three comparisons it can be attained only by two d-clusters in the same group. This proves inductively that no greedy tie can leave the line groups or merge unequal sizes before each group has fully coalesced. The argument makes no claim about the later merges.

At each phase the selected union weights charge exactly n for the point keywords: each point label in a cluster is distinct and the merged clusters of size 2d partition all n leaves. There are log s phases, so raw G is at least n log s. In fact the forced phases alone also contribute 3(n−n/s) from column and line keywords.

### 4.2 An inexpensive comparison tree

First build a balanced binary subtree joining the c files of each point. At every one of these log c levels, clusters partition the n original leaves, and each cluster's union weight is at most four times the number of leaves it contains. Their total raw cost is at most 4n log c.

Next treat the r resulting point subtrees as leaves of an outer tree. Choose nested F_c-linear subspaces U_0⊂U_1⊂...⊂U_h=F_s with dim U_i=i; U_0={0}. Use the point blocks (x+U_i)×(y+U_i), which partition F_s² at each i. Each such block has c² child blocks at the preceding i. At each macro stage i join its c² child point-block subtrees by a balanced full binary tree, with 2 log c binary levels. At the end the entire collection is one tree.

Bound outer cost by keyword class. Point keywords contribute exactly r log r, because all point leaves have the same depth 2h log c=log r, and a given point keyword occurs in precisely the ancestors of its point subtree. Every outer cluster contains all c columns, hence column keywords contribute exactly 2c(r−1) over its r−1 internal nodes.

For line keywords consider a fixed direction j and a fixed macro stage i≥1. Put B=c^(i−1). A child point-block is a product of two cosets of U_(i−1), and its intercepts y−jx occupy at most one coset of U_(i−1) since j∈F_c preserves that linear subspace. It has at most B different line keywords of this slope. Each binary level of stage i partitions the child blocks among its nodes. There are r/B² child blocks globally, so using a simple union bound their total contribution at this binary level is at most (r/B²)*B=r/B, for this direction. Therefore over the c directions, 2 log c binary levels per macro stage, and all i, the line contribution is at most

    2 c r log c * sum_{i=1}^h c^(-(i−1)) ≤ 4n log c.

The comparison tree's raw cost is consequently at most

    4n log c + r log r + 2c(r−1) + 4n log c ≤ 12n log c,

because r log r=2rc log c=2n log c and log c≥1. The ratio to the true optimum is at least (n log s)/(12n log c)=c/12. Since log n=(2c+1)log c, one has (log n)/(log log n)≤2c+1≤3c, and so the S ratio has the asserted lower bound on this sequence. The normalized root weight equals one, so O≥1. Accordingly the visit ratio is at least 2G/(3O)≥c/18. This argument is entirely about tree construction and expected node counts; it does not infer anything about ciphertexts, data disclosure or implementation security.
