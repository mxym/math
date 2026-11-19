# A sharp 4/3 correlation gap for nonnegative pairwise covariance

Let X be a random subset of a finite set [n] with specified membership probabilities p_i. Write F(p) for the maximum of E f(X) over all laws with those marginals, for a nonnegative nondecreasing set function f. Write F_pos(p) for the maximum over laws also satisfying
```
 P(i,j∈X) ≥ p_i p_j       for all distinct i,j.
```
In particular zero covariance is allowed. Both classes are nonempty compact polytopes (the product measure is feasible). The standard submodular case is included, but submodularity will not be needed.

**Theorem.** F_pos(p) ≥ (3/4) F(p), and the factor 3/4 is best possible even for a union indicator and two elements. In fact a single, f-independent transformation of any input law into a new law Y with the same marginals has the stronger simultaneous properties
```
 P(J⊆Y) ≥ ∏_{i∈J} p_i       for every J⊆[n],
 E f(Y) ≥ (3/4) E f(X)       for every nonnegative nondecreasing f.
```

**Proof.** Put a=3/4. For each i set
```
 if p_i<a:     h_i=a,     l_i=(1−a)p_i/(1−p_i);
 if p_i≥a:     h_i=l_i=p_i.
```
Each endpoint at p_i=0 or 1 is covered, with no division by zero. Both l_i and h_i are nondecreasing in p_i, 0≤l_i≤p_i≤h_i, and h_i≥a. Let U be uniform on [0,1] independent of X. The threshold T_i is h_i if i∈X and l_i otherwise. Include i in Y precisely if U≤T_i. The marginal identity E T_i=p_i is immediate. On U≤a, every i in X belongs to Y simultaneously, so E f(Y)≥E[f(X)1{U≤a}]=a E f(X), by monotonicity and nonnegativity.

For any J of size at least two, order its members so the two smallest marginals are p≤q. If q≥a, every coordinate of J other than the first has a constant threshold equal to its marginal (and at least q), whereas the threshold of the first is at most q. The probability of the intersection is p, which is at least the product. If q<a, write l(t)=(1−a)t/(1−t). Conditional on the entire X, the intersection probability is min_{i∈J}T_i. When the first member is absent from X that minimum is l(p); when present it is at least l(q), since all other thresholds are at least l(q) and h(p)=a≥l(q). Therefore
```
 P(J⊆Y) ≥ (1−p)l(p)+p l(q) = p/[4(1−q)] ≥ pq ≥ ∏_{i∈J}p_i.
```
The middle inequality is q(1−q)≤1/4. Empty and singleton intersections are automatic. Apply the construction to an optimizing X.

For sharpness, let p₁=p₂=1/2 and f(S)=1{S nonempty}. Uniform mass on the two singleton sets gives F=1. With the pair lower bound, the probability of a nonempty set equals 1−P(1,2∈Y)≤3/4, attained by the independent law. Thus the sharp ratio F/F_pos is 4/3 where F>0, even if all upper intersection constraints are imposed. ∎

**Interpretation.** In the final paragraph of [Ramachandra, arXiv:2609.02659v1, §5](https://arxiv.org/html/2609.02659v1#S5), after settling the sharp *pairwise independent* gap asymptotically, the author suggests investigating the larger feasible set that admits positive correlations. The paragraph does not define an additional higher-order condition. The theorem answers that suggestion when pairwise joint probabilities may exceed their independent values; it does not concern pairwise independence (a different feasible set). The upper intersection bound is an additional property of the constructed law, not an assumption attributed to the original source.

In particular this is not positivity of covariance for all increasing functions (positive association). To see why that distinction is substantive, take n equally likely singleton inputs with p_i=1/n and consider the union indicator. Association makes indicators of simultaneous absence and of individual absence nonnegatively correlated, since both are decreasing. Inductively P(Y empty)≥(1−1/n)^n. Thus even the *best* associated law has union probability at most 1−(1−1/n)^n, attained by independence. Already for n=3 this is less than 3/4. The established independent correlation-gap theorem for monotone submodular functions together with this example also gives the asymptotic 1−1/e factor if full association is required. The present theorem asserts neither positive association nor the FKG lattice condition.
