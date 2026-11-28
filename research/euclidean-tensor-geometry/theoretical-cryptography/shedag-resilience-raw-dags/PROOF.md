# Exact and approximate SHEDAG resilience from raw DAGs

## 1. Definitions and simultaneous threshold formula

Let G=(V,E) be a finite DAG on N≥2 vertices. Arrows point from predecessor to successor. For v∈V write A(v)={v}∪{u: a nonempty directed path leads from u to v}, and c(v)=|A(v)|. The nonempty path predecessors are exactly the strict view of v in Definition 1 of TR26-011 rev2; in particular, v is not in its own view. For nonempty S⊆V set

    d(S) = max_{v∈S} |A(v)∩S|,
    r_a(S) = |S| − max(a,d(S)),   R_a(G) = max_{S nonempty} r_a(S),  a∈{1,2}.

These are Definition 19's uniform and entropic quantities for a=1,2, respectively (also Definitions 23,25 in §§5.4–5.4.1). The graph-size constraints are 0≤R_a(G)≤N−a: a singleton gives zero for a=1; any two-element set gives zero for a=2; the upper bounds hold term by term. For any nonempty S the view uses paths in G, not just those staying in S, as in the view-preserving graph of Definition 17.

Call S an ideal if A(v)⊆S for each v∈S. The closure I=∪_{v∈S} A(v) satisfies r_a(I)≥r_a(S). Indeed, for each x∈I there is y∈S with A(x)⊆A(y). Thus |A(x)∩I|≤d(S)+|I∖S|. Taking the maximum and then applying max(a,·) increases the penalty by at most |I∖S|, while its reward increases by exactly that amount.

For an integer D between 1 and N, put S_D={v:c(v)≤D} and F(D)=|S_D|. This is a nonempty ideal: at least one source has c=1, and strict predecessors have strictly smaller c. Indeed A(u)⊆A(v) and v∉A(u) on any nonempty path u→v. On any ideal I the penalty is max(a,max_{v∈I}c(v)). For D=max_{v∈I}c(v), S_D contains I and has the identical penalty, strictly increasing the score if containment is proper. For arbitrary D, max_{v∈S_D}c(v)≤D, so F(D)−max(a,D)≤r_a(S_D). It follows that

    R_a(G) = max_{1≤D≤N} (F(D)−max(a,D)).                         (1)
    Δ_a(G) := N−R_a(G) = min_{1≤D≤N} (N−F(D)+max(a,D)).

A maximizing threshold produces an optimizing ideal; indeed every maximizing ideal must be a threshold, not every maximizing set. It suffices to scan thresholds attained as c-values, and ties among scores may be broken arbitrarily. Either form can also be evaluated at all integer thresholds with prefix counts.

The uniform closure argument is already present in Lemmas 6–7 of the source; its entropic algorithm already groups by global weight, and (1) is a simultaneous justification. The source's use of the global weights for arbitrary nonempty S, before Lemma 8, is false in general. For the path 1→2→3 take S={1,3}: d(S)=2, r_2(S)=0, yet using global weights gives 2−3=−1. This S is not a threshold and is optimal (every nonempty path-subset has d(S)=|S|). The threshold-output algorithm remains correct with the ideal restriction. Also, the uniform Algorithm 2 line 13 uses s−|view(v)|; with the intended largest-view head removal, the correct score there is s−|view(v)|−1. Already on the edgeless graph the literal line gives N instead of N−1.

## 2. Exact upper bounds and the representation issue

Given exact c-values, bucket them in [1,N] and use (1), obtaining each value and a witness in O(N) time. Given an explicit transitive-closure adjacency list, compute c from the indegrees there in O(N+E_cl) time. The raw input of §§5.4–5.4.1, by contrast, need not have every transitive edge (in Definition 17, H(V)=G). Topological sorting alone does not supply the c-values, and summing parent counts double counts shared predecessors: in the diamond s→u,s→v,u→w,v→w, c(w)=4, not 1+2+2. The source claims a linear raw-graph preprocessing bound in §5.4; this summation example is not itself a lower bound. Section 3 gives a conditional lower bound on the scalar task, even for algorithms that never produce all counts. The source's entropic O(N(N+E)) upper bound is not contradicted.

For comparison, N graph searches take O(N(N+E)) time. On a word RAM supporting w-bit Boolean operations, parent-set union in topological order with bitsets takes O((N+E)ceil(N/w)) time and O(N ceil(N/w)) auxiliary words with unit word popcount. For the standard w=Θ(log N) model without unit popcount, a lookup table for chunks of max(1,floor((log_2 N)/2)) bits is built in O(N) and gives the same order. Under a promise that distinct incoming neighbors of each v have disjoint closed ancestor sets, their counts can instead be summed in O(N+E) time. A DAG with at most one directed path between each ordered pair has this promise: a shared ancestor would give two paths to v.

An output-sensitive exact algorithm does not need large ancestor sets if the deficit is small. For integer K≥1, propagate each truncated set containing the first min(K+1,c(v)) IDs of A(v) in a common total order. The identity

    first_L(U∪W) = first_L(first_L(U)∪first_L(W))                   (2)

holds even for overlapping sets: any item dropped from an input already has at least L smaller distinct items in that input, so cannot be in first_L of the union. In topological order start at {v} and merge with the truncated lists of its immediate predecessors, deduplicating on a common total order. Sorted list merges cost O(K+1) per vertex or edge, so the truncated cardinalities take O((N+E)(K+1)) time and O(N(K+1)) auxiliary words (cap K at N). For D≤K they give F(D) exactly. Every term with D>K in the deficit form of (1) is bigger than K. Hence scanning D≤K decides Δ_a≤K and gives the exact value and witness whenever the answer is yes. Double K starting at 1 until this occurs, capping at N. Since a≤Δ_a≤N, the total time for either requested score R is O((N+E)(N−R)), with the same O(N(N−R)) auxiliary space. The extremes Δ_a=a and Δ_a=N require no separate assumptions. Both scores can be computed by the same pass sequence, stopping when both are determined.

## 3. Conditional lower bound on either one exact scalar

**One-query padding.** Given an arbitrary M-vertex DAG G₀ and an integer 2≤q≤M, take a disjoint component consisting of q−2 new sources, one vertex p with incoming edges from those sources, and q distinct leaves with sole incoming edge from p. Their closed view sizes are 1 at the sources, q−1 at p, and q at each leaf. The new N=M+2q−1 and the increase in edge count is 2q−2. The component has no path of length >2 (for q=2, p is a source with two leaves). For either a, the surrogate in (1) is at most N−q−1 at every D<q, since all q leaves are missing and the penalty is at least 1. At every D>q it is at most N−q−1 because the penalty is at least q+1. At D=q it is exactly

    N−q − |{v∈V(G₀):c(v)>q}|.                                      (3)

Consequently R_a=N−q iff max_v c_{G₀}(v)≤q; in this case no other threshold ties D=q. Otherwise R_a≤N−q−1. If the base maximum is precisely q+1, D=q+1 includes all vertices and R_a=N−q−1. This reduction takes O(M+E₀) time and one exact call. Its use of a single scalar is important: a hardness result for all individual counts alone would not prove this. The maximum can also be recovered by binary search with O(log M) such queries; q=1 is handled by checking whether there is an edge.

**Hitting Set Existence.** Let the inputs be two lists of m binary d-vectors, a₁,…,a_m and b₁,…,b_m, with m,d≥1, and ask whether at least one a_i intersects every b_j (the witnessing 1-coordinate may depend on j). This is the quantifier in the Hitting Set Conjecture, not the Orthogonal Vectors quantifier. Begin from the tripartite incidence pattern of Abboud–Vassilevska Williams–Wang §4, orienting it toward the a-vertices and balancing the number of coordinate predecessors as follows:

- Layer 1 has m vertices labelled b_j. Layer 2 has d real and d dummy coordinate vertices u_k,u'_k. Include b_j→u_k exactly for b_{jk}=1; no b_j has an edge to u'_k.
- Layer 3 has m vertices labelled a_i. Each coordinate contributes precisely one edge into a_i: u_k→a_i when a_{ik}=1, and u'_k→a_i otherwise.

The base has M=2m+2d vertices and exactly m d+∑_j |b_j|_1 edges. A b_j is a strict ancestor of a_i iff they intersect, even when an intersection has more than one witnessing coordinate. Thus c(a_i)=1+d+#{j:a_i and b_j intersect}. Other vertices have closed count at most m+1. Take q=m+d, for which m+1≤q≤M and q≥2. In a NO instance, max c≤q. In a YES instance, max c=q+1. Apply the padding above. Both scores are exactly

    NO  : N−q,
    YES : N−q−1,

with N=4m+4d−1 and edge count E=m d+∑_j |b_j|_1+2q−2≤2m d+2q−2. The resulting graph is still three-layered with edges between consecutive layers only, by putting p in layer 2 and its leaves in layer 3. The construction takes O(m d+m+d) time from explicit input vectors. The two cases are distinguishable without any tie-breaking assumption (thresholds may tie below the NO target). If literal E≤N is required, add z=max(0,E−N) isolated vertices. Each old threshold includes every added vertex and all previous c-values are unchanged, so each old surrogate increases by z. Any newly allowed D>N includes all vertices and has a larger penalty than D=N. Thus both score values increase by z exactly, the distinguishing gap is unchanged, and the new N is max(N,E)=O(m d+m+d). The order by layers, with isolated vertices anywhere, may be given to the algorithm.

The Hitting Set Conjecture asserts that there is no fixed ε>0 for which every fixed c≥1 admits an O(m^(2−ε)) algorithm on d=c log m (with integer rounding), for the model in which the conjecture is made. On these inputs the reduction gives explicit raw adjacency lists with O(m log m) vertices and E≤N. A hypothetical O(N^(2−ε)) algorithm for either exact scalar, even on this restricted class, would give a truly subquadratic Hitting Set Existence algorithm; the polylogarithmic overhead can be absorbed into a smaller positive exponent. The same argument covers O((N+E)^(2−ε)) and any overhead of polylogarithmic order. No assertion is made for randomized error models not included in the conjecture used. In particular, this is not a SETH-only lower bound or an unconditional refutation of a linear-time bound. A transitive-closure representation, which could already have quadratic size on these instances, is a different input model.

## 4. Relative approximation to the deficit, with a near-optimal ideal

Fix a given DAG, 0<ε≤1, and 0<δ<1, let η=ε/3, let J=ceil(log_2 N), and choose the following integer sketch budget (or pass N as the cap if this budget exceeds N):

    L = ceil(12 η^(−2) ln(3N(J+1)/δ)).

We use a word RAM with O(log N)-bit words (a constant number per intermediate integer); take the cap K=min(L,N). If N≤L compute exact counts via (2) with cap N and skip sampling. Otherwise sample independent uniform integer ranks h(u) from {0,…,2^J−1}, one J-bit word per vertex. Order items by (h(u),vertex ID) to break collisions. In one topological pass, initialize every vertex with its own item and merge its lists once per incoming edge. The actual work is O(L) per vertex or raw edge, with sorted, deduplicating truncation from (2). Thus all lists together take O((N+E)L) time and O(NL) auxiliary space; there is not a graph traversal per dyadic scale. This is the standard coordinated bottom-k union, applied here to closed ancestor sets.

For 0≤j≤J define X_{vj}=|{u∈A(v):h(u)<2^(J−j)}|. At each *fixed* v,j it is a binomial random variable with mean μ_{vj}=2^(−j)c(v), so 2^j X_{vj} is unbiased at a fixed scale. Counts across v or j need not be independent. From the stored list we can tell whether X_{vj}≥L, and recover the count exactly if less than L; truncation uses the order by rank first. When c(v)<L its exact count is already known. Otherwise use the smallest j with X_{vj}<L and take preliminary estimate 2^j X_{vj}, using any estimate in [1,N] if no such j exists. The chosen-scale estimator is not assumed unbiased. This test can be found in O(J+L) time per vertex by comparing the Lth rank to the J+1 thresholds and scanning the stored list once. Clamp every preliminary estimate to [1,N].

For μ≥L/4 the multiplicative Chernoff bound gives

    Pr(|X−μ|>ημ) ≤ 2 exp(−η² μ/3) ≤ 2 exp(−η² L/12).

For μ<L/2, Markov applied to 2^X and (1+p)^c≤exp(μ) gives

    Pr(X≥L) ≤ exp(μ−L ln 2) ≤ exp(−L/6).

The displayed inequalities also hold for deterministic j=0; at μ=L/2 the latter bound may be used or not. By a union bound, simultaneously for all N(J+1) pairs, both indicated properties hold with probability ≥1−δ. When c(v)≥L, j=0 is saturated; j=J has μ≤1<L/2, so on the good event an unsaturated j≥1 exists. Its preceding scale j−1 was saturated; the second property implies μ_{v,j−1}≥L/2 and hence μ_{vj}≥L/4. The first property now gives a (1±η) relative estimate of c(v). Clamping does not worsen this bound since c(v)∈[1,N].

Estimates from different chosen scales need not respect the DAG. In a topological pass replace each clamped estimate by the maximum of itself and the already revised values at its immediate predecessors. Write the resulting values as b(v). This computes maxima of clamped estimates over A(v), so b is isotone along directed edges. On the same good event, (1−η)c(v)≤b(v)≤(1+η)c(v), using c(u)≤c(v) for u∈A(v) and using v itself for the lower bound. All b-values are integers in [1,N]. Scan their histogram just as in (1): the set of all vertices with b≤D is an ideal, and the same enlargement argument for ideals holds even when b ties along an edge. Thus the histogram minimizes

    hatΔ_a(S) = N−|S| + max(a,max_{v∈S} b(v))

over nonempty ideals. For any such ideal S, its true deficit Δ_a(S):=N−r_a(S) satisfies

    (1−η) Δ_a(S) ≤ hatΔ_a(S) ≤ (1+η) Δ_a(S).

Indeed the maxima, including the unchanged a, obey these inequalities, and the uncovered count N−|S| is nonnegative. Let S* be a minimizing threshold and hatΔ_a=hatΔ_a(S*). Then

    (1−η) Δ_a(G) ≤ hatΔ_a ≤ (1+η) Δ_a(G),
    Δ_a(S*) ≤ (1+η)/(1−η) · Δ_a(G) ≤ (1+ε) Δ_a(G).

The lower-value inequality uses the fact that the true minimum over ideals equals the unrestricted one. The upper-value inequality uses a true optimum ideal. These statements hold simultaneously for both a on the same event. In particular S* attains at least R_a−εΔ_a≥R_a−εN; subtracting the estimated deficit from N also estimates R_a to that scale. The set S* can be returned explicitly, and checking that it is an ideal requires only O(N+E) edge scans; the numerical approximation guarantee is probabilistic, not a deterministic certificate of the score of that set. An exact score can be separately verified from exact counts in its induced ideal if required.

With either branch the time is O((N+E) min(N,L)) and auxiliary space O(N min(N,L)). The topological merge, scan of dyadic scales and threshold histogram all fit in the bound since J=O(L); in the exact branch dyadic scans are not used. The rank order, binomial trials and threshold comparisons require only finite random bits and integer operations. As L=O(ε^(−2) log(N/δ)), the estimator is near linear for fixed ε and inverse-polynomial δ. This is a statement about estimating graph parameters and selecting an ideal, not about the error or complexity of any extractor on a source.
