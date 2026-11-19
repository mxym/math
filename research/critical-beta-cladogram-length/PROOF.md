# The drawn length and width of a critical beta-splitting cladogram

Let T_n be the n-leaf ordered critical beta-splitting tree, with ordered root split of sizes (i,n−i) having probability n/[2 H_{n−1} i(n−i)], where H_j=Σ_{r=1}^j 1/r. Given the split, the two subtrees are independent copies at their respective sizes. The order can be forgotten throughout. Draw every leaf at height 0 and place each internal vertex one unit higher than the higher of its two children. Write h(t) for the draw-height of the root of any tree t (its maximum edge-depth), D(t) for the sum of vertical edge lengths and W_t(j) for the number of vertical edges spanning (j,j+1), j=0,1,… . Length counts edges with multiplicity, exactly as in Aldous–Janson's recursion (73), not the horizontal segments or the branch lengths of their continuous-time tree.

**Theorem.** Define, for m≥2,
```
b_m = H_{m−1}/[ζ(2)m(m−1)],   w_j = Σ_{m≥2} b_m P(h(T_m)>j),
c = Σ_{m≥2} b_m E h(T_m).
```
Then w is summable, c=Σ_j w_j≥2, and, for every fixed real 1≤p<∞,
```
E ||W_{T_n}/n − w||_1^p → 0,       E |D(T_n)/n − c|^p → 0.
```
In particular E D(T_n)∼cn. This is linear, rather than the proposed n(log n)^4 in [Aldous–Janson II, v3, §6.1.1, Open Problem 14](https://arxiv.org/html/2303.02529v3#S6.SS1.SSS1). The normalized, deterministic whole-profile limit is an answer to their Open Problem 15 on one scale. No fluctuation limit or least-error estimates for W are claimed.

### 1. Two deterministic identities

For an internal vertex v let t_v be its descendant tree. Let u_j(t)=(1{h(t)>j}) and u(t)=(u_j(t))_{j≥0}. On any edge parent→child, the crossing indicator is u_j(t_parent)−u_j(t_child). Summing, every internal parent occurs twice, every nonroot child once, and leaf indicators vanish. Therefore, including the one-leaf tree,
```
W_t = u(t)+Σ_{v internal}u(t_v),
D(t) = h(t)+Σ_{v internal}h(t_v).
```
The second identity follows by summing in j. In particular D(t)≤(2n−2)h(t) for n≥2 also follows by bounding each of the 2n−2 edges by h(t). Every edge has length at least one, so D(t)≥2n−2. Already the former inequality and the known mean height bound O(log² n) rule out the proposed order; the remainder identifies the correct first-order limit. Define the support-weighted vector u(t) only on the nonnegative integer levels as above, so that ||u(t)||_1=h(t).

### 2. Counting fringe clades and controlling large clades

Write N_n(m) for the number of m-leaf fringe clades in T_n. A uniform tagged leaf passes through any fixed m-leaf clade with conditional probability m/n. Two different clades of the same size cannot be nested. The decreasing tagged-size chain has transition from s to t<s with probability 1/[(s−t)H_{s−1}], by size-biasing the split. If a(n,m) is its probability of visiting m (including the starting state), then
```
E N_n(m)/n = a(n,m)/m,       a(n,m)→a(m)=H_{m−1}/[ζ(2)(m−1)]   (m≥2 fixed).
```
Both facts are prior: see [Aldous–Janson II, (51), Theorem 18](https://arxiv.org/html/2303.02529v3#S4.SS1), and [Aldous–Janson–Li, The Harmonic Descent Chain](https://doi.org/10.1214/24-ECP645). Also, for any nonnegative function f on finite trees,
```
(1/n)E Σ_{v: |t_v|=m} f(t_v) = a(n,m) E f(T_m)/m.       (1)
```
For example, label candidate nodes by finite binary addresses. Conditional on existence and size m at an address, its subtree has law T_m, since the splits down to but not including that address are already determined. Summing proves (1). Thus the visit probability and the count per leaf differ by a factor m; in (75) of the heuristic these must not be interchanged.

For any integer M≥2, from any state s∈[M,2M) the chance the next state is strictly below M is at least (M−1)/(2M H_{2M})≥1/(4H_{2M}), by summing the M−1 corresponding transition probabilities. After exit below M the decreasing chain never returns. Hence its total expected visits to this interval, from any start, satisfy
```
Σ_{M≤m<2M} a(n,m) ≤ 4H_{2M}.                              (2)
```
No independence of exit events is required: the conditional probability of one further visit is at most 1−1/(4H_{2M}).

We need only the prior height-moment bound ||h(T_m)||_p≤C_p(1+log m)^2 for each fixed finite p≥1. This follows, for example, from [Ma, The height of discrete-time critical beta-splitting trees, Theorem 1.1](https://arxiv.org/abs/2609.14329v2), whose Theorem 1.1 proves the stronger L^p asymptotic for all 1≤p<∞. By (1) and (2), summing over [M,2M),[2M,4M),… gives
```
sup_n (1/n) E Σ_{v: |t_v|≥M} h(t_v)^p ≤ C'_p (1+log M)^{2p+1}/M.  (3)
```
In each dyadic bin starting at x, use 1/m≤1/x, bound its moment by C_p^p(1+log(2x))^{2p}, and use (2). Summability of the geometric sequence times a fixed power gives (3). In particular there is no false pointwise assertion a(n,m)≤C log(m)/m all the way to m=n.

### 3. The finite truncations and the limits

For a fixed shape τ on m leaves let N_n(τ) count its fringe occurrences. Then E N_n(τ)/n→b_m P(T_m=τ) by (1). Its variance is O_τ(n) by [Brandenberger–Chin–Mossel, Asymptotics for the harmonic descent chain and applications to critical beta-splitting trees, Corollary 1.4 and Section 4](https://arxiv.org/html/2505.24821v3#S4). Indeed just their size-count assertion Var N_n(m)=O_m(n) suffices for either shape convention: reveal all splits at sizes greater than m, but none at smaller sizes. The size-m boundary trees are independent copies of T_m conditional on this stopped skeleton, which determines their count; thus N_n(τ) conditional on it is binomial with parameters N_n(m) and P(T_m=τ). The law of total variance gives the bound. Thus N_n(τ)/n converges in L² to its mean limit. Since the normalized counts are bounded by 1, convergence holds for every fixed finite L^p. For each fixed cutoff M, the contribution from all sizes 2≤m<M to the internal-vertex sum W/n in §1 is a finite sum of these normalized counts times fixed vectors u(τ). It converges in L^p(ℓ¹) to Σ_{2≤m<M} b_m E u(T_m).

For the omitted large-clade vector, its ℓ¹ norm is n⁻¹Σ_{v:|t_v|≥M} h(t_v). Padding the list of at most n−1 internal vertices with zeros to length n and using convexity, the p-th power of this norm is bounded by n⁻¹Σ_{v:|t_v|≥M} h(t_v)^p. Bound this uniformly by (3) after expectation. The separate root vector has L^p(ℓ¹) norm ||h(T_n)||_p/n→0. Finally, the proposed infinite sum defining w converges absolutely in ℓ¹: b_m=O((1+log m)/m²), while E||u(T_m)||_1=O((1+log m)^2). Taking first n→∞ and then M→∞ now gives the claimed profile limit by the triangle inequality. Summing all coordinates (a bounded linear functional on ℓ¹) gives the claimed length limit. The deterministic lower bound in §1 yields c≥2. This proves the theorem.

The constant and profile use only the finite tree laws. For instance the laws of h(T_m) may be calculated exactly from P(h(T_1)≤j)=1 for j≥0 and, for m≥2, P(h(T_m)≤j)=Σ_i q(m,i)P(h(T_i)≤j−1)P(h(T_{m−i})≤j−1), with negative thresholds assigned probability zero. No numerical experiment is used in the proof.
