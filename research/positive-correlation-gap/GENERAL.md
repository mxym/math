# A sharp bound for general pairwise lower constraints

Let g:(0,1)→[0,1] be arbitrary; give it any values in [0,1] at 0,1. For a law on subsets with membership probabilities p_i, impose the lower bound
```
 P(i,j∈Y) ≥ p_i g(p_j)   whenever i≠j and p_i≤p_j .
```
This class is always nonempty: taking Y_i=1{U≤p_i} gives the upper Fréchet value min(p_i,p_j). Let F_g(p) denote its maximum expectation of f, with F(p) unrestricted. For any n and any nonnegative nondecreasing f,
```
 F_g(p) ≥ a_g F(p),    a_g=1−sup_{0<q<1}(1−q)g(q).
```
The constant is optimal uniformly in the dimension, marginals, and objectives. The union indicator already witnesses optimality, so restricting f to monotone submodular functions does not improve it. No continuity or monotonicity of g is required; only its values at finitely many input marginals enter any particular model.

**Lower bound.** Put a=a_g∈[0,1]. Use the common U and the high/low thresholds of the main theorem, now with a in place of 3/4, again taking both thresholds to equal p whenever p≥a. This handles a=0, a=1 and marginal endpoints: at a=1 and p=1 use the constant threshold. As before Y has the prescribed marginals and captures all of X on a common event independent of X of probability a, so it retains at least a of the expectation simultaneously for every nonnegative monotone f. For p=p_i≤q=p_j and q≥a, the j threshold is constant q and the i threshold is ≤q, giving intersection p≥p g(q). For 0<q<a the pair calculation of the main proof gives intersection at least p(1−a)/(1−q)≥p g(q). For q=0 or p=0 the required lower bound is zero. Endpoints do not constrain a.

**Sharpness.** For any 0<q<1, take one distinguished element of marginal q and split 1−q into finitely many other marginals p_i≤q (e.g., equal shares with count ceil((1−q)/q)). All marginals sum to one. A law supported on singletons achieves F=1 for the union indicator. For any admissible Y, splitting off the distinguished element and using the union bound on its complement gives
```
 P(Y nonempty) ≤ q + Σ_i [p_i−P(i and distinguished in Y)]
                ≤ q + (1−q)[1−g(q)] = 1−(1−q)g(q).
```
The first inequality is the classical star union bound. Take the infimum over q; no maximizing q or finite optimizing dimension need exist. This proves exactness.

**Examples.** For g(q)=r q, 0≤r≤1, the factor is 1−r/4. On the other side, a lower bound interpolating from the independent joint to its maximal possible value is P(i,j∈Y)≥(1−t)p_i p_j+t min(p_i,p_j), 0≤t≤1. Its function is g(q)=(1−t)q+t. Maximizing (1−q)g(q) gives a=1−1/[4(1−t)] for t≤1/2 and a=1−t for t≥1/2. For t<1/2 the maximizer is q=(1−2t)/(2(1−t)), while t≥1/2 uses q↓0. Thus full comonotonicity has no dimension-independent positive guarantee even for union indicators.
