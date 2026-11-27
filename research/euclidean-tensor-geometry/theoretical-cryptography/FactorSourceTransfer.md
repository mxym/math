# Which source-distribution bounds transfer average-case factoring assumptions?

An average-case assumption about factoring uniform balanced semiprimes concerns one source distribution. To reuse it for a different source, it is not enough to compare its Shannon entropy, the marginal laws of its two factors, or even a predetermined collection of coarse joint classes. This note makes the exact statistical transfer condition explicit and gives balanced-semiprime examples showing the gap. It does **not** assert that any rare class exhibited here can be factored by an efficient algorithm.

## Domain and exact transfer criterion

Let S_n be the n-bit primes and M_n=|S_n|. The label space Ω_n consists of unordered pairs of distinct elements of S_n, identified with their products by unique factorization. Write U_n for its uniform law and D_n for any alternative law on that same space. When describing two factor marginals, order the factors by an independent fair orientation rather than by size. The corresponding symmetric ordered distributions have the same likelihood ratio and divergences as the laws on products.

A sequence is negligible if it is eventually at most n^(−s) for every fixed s>0. Set L_n(x)=D_n(x)/U_n(x). The following conditions are equivalent:

1. For every sequence of functions 0≤f_n≤1 on Ω_n, negligible E_(U_n) f_n implies negligible E_(D_n) f_n.
2. For every s>0 there is a constant c>0 such that D_n{L_n>n^c}≤n^(−s) for all sufficiently large n.

For sufficiency, split according to the likelihood threshold and use
```
E_D f ≤ n^c E_U f + D{L>n^c}.
```
For necessity suppose condition 2 fails at s. For each integer j≥1 choose a larger n_j with D_{n_j}{L_{n_j}>n_j^j}>n_j^(−s). Take A_{n_j} to be that tail event and all other A_n empty. Then U_{n_j}(A_{n_j})≤n_j^(−j), so f_n=1_(A_n) is a counterexample. Thus the criterion is exact for all statistical tests, not only indicators.

For an arbitrary randomized algorithm on input N, its success probability on each fixed N is one such f_n. Hence condition 2 is sufficient to transfer any negligible uniform-source success bound, including an assumed one for efficient factoring. Necessity is asserted for *all* tests, not for the subclass of efficient factoring algorithms; a violating event need not be efficiently recognizable. This is a one-way transfer, and side information not already represented in Ω_n would need its own joint likelihood comparison.

A single fixed polynomial likelihood cap plus a negligible exceptional probability is a useful stronger condition, not necessary. For example, in a cyclic labeling of S_n, for each j=1,…,floor(sqrt n) choose a disjoint regular undirected edge layer E_j of degree 2 floor((M_n−1)/(2n^(2j))) using distinct cyclic distances, ignoring the antipodal distance if M_n is even. For all sufficiently large n these degrees are positive: the prime number theorem gives ln M_n∼n ln 2. The total used degree is less than M_n−2 for large n. Let e_j=U_n(E_j)∼n^(−2j), uniformly in j. Mix the uniform law with mass w_j=n^(−j)/2 on U_n conditioned on each E_j (the weights sum to less than one). On E_j the likelihood is of order n^j; the probability of levels j≥k is O(n^(−k)) for each fixed k. Hence condition 2 holds, and yet any fixed polynomial threshold misses inversely polynomial mass on some fixed higher level. All factor marginals in this example remain exactly uniform because the layers are regular.

## What entropy can and cannot give

For any event A with u=U(A) between zero and one and p=D(A), write d(p||u) for binary relative entropy in natural logarithms. Applying the log-sum inequality to A and its complement gives
```
KL(D||U) ≥ d(p||u)
         = p ln(p/u) + (1−p) ln((1−p)/(1−u)).
```
Thus when only a Shannon-entropy deficit budget B=ln|Ω|−H(D) is known, the exact unrestricted upper limit on p is the largest p with d(p||u)≤B. It is attained by keeping uniform conditional distributions on A and its complement. This extremizer also has uniform factor marginals when A comes from a regular graph on the prime labels: conditional on either edge layer each endpoint is uniform.

For example, take A to be a perfect matching when M_n is even, and a cycle when it is odd. Then u=1/(M_n−1) or 2/(M_n−1), respectively, both exponentially small in n. If B=n^(−a) for any fixed a≥0 (or any fixed positive absolute budget), the largest p is asymptotic to B/ln(1/u), hence inversely polynomial, even with exact uniform factor marginals. For a proof of this asymptotic, set `T=ln(1/u)` and compare p=(1±η)B/T for fixed 0<η<1. With binary entropy h, d(p||u)=pT−h(p)−(1−p)ln(1−u), and h(p)=O(p ln(1/p)+p)=o(B), while u=o(B). Thus the two test values lie on either side of B for large n, and d(p||u) increases for p≥u. In this regular construction the conditional Shannon deficit of the second factor given any fixed first factor equals the same B, not just its average.

A fixed-order Rényi upper bound is different: if α>1 is fixed and D_α(D_n||U_n)=O(ln n), Hölder gives
```
D_n(A) ≤ exp((α−1)D_α/α) U_n(A)^((α−1)/α),
```
and the same bound holds with expectations of 0≤f≤1. This transfers negligible probabilities. Losing a logarithmic number of bits of min-entropy does as well, since U_n is uniform and the likelihood itself is then polynomially bounded.

In fact one must be careful if the Rényi order approaches one. For any positive δ_n tending to zero, pick an integer τ_n tending to infinity with τ_n≤min(n^(1/4),1/(8δ_n)). Use a regular circulant event E with U(E) asymptotic to n^(−τ_n), feasible since M_n grows exponentially. Mix weight w=1/n of U restricted to E into U. The event receives probability p∼1/n, despite negligible U(E); nevertheless D_(1+δ_n)(D||U)=o(1). Indeed outside E the likelihood is ≤1, and on E it has a constant value R≤3n^τ_n for large n. Hence
```
D_(1+δ)(D||U) ≤ ln(1+p(R^δ−1))/δ
              ≤ p (ln R) R^δ,
```
by the mean-value inequality for the exponential. Here R^δ=O(n^(1/4)), ln R=O(n^(1/4)ln n), and p=O(1/n). For this example the factor marginals are still exact. This does not contradict the preceding fixed-order bound.

## Exact coarse diagnostics still do not suffice

Fix any partition C_1,…,C_k of the prime pool into nonempty classes, for example a collection of coarse factor categories fixed in advance. Write a_i=|C_i|. There is a symmetric reference-perturbation law Q on distinct ordered pairs satisfying all of the following:

* Both marginals are exactly uniform on S_n.
* The joint law of the two class labels is exactly the same as for uniformly sampled distinct factors. More strongly, given either exact factor, the conditional law of the *other* factor's class is also unchanged.
* Q is supported on at most 2kM_n ordered pairs.

To construct this purely statistical example, first give each ordered class pair the same mass as under U: a_i a_j/[M_n(M_n−1)] for i≠j and a_i(a_i−1)/[M_n(M_n−1)] for i=j. For different classes, jointly assign their uniform labels by two equal-length quantile partitions of a common unit interval with a_i and a_j cells. There are at most a_i+a_j−1 nonempty intersections, and both conditional marginals are uniform. Use transposed couplings for reversed class pairs. In a class of size at least two, pair along a cyclic order and reverse with independent probability one half, which uses at most 2a_i ordered pairs and again has uniform marginals. A singleton diagonal has zero weight. This proves symmetry and the asserted support count. The conditional class assertion follows because each fixed pair of classes leaves each individual label uniformly distributed within its own class.

Let A be this support, viewed as a product event. Its probability under U is at most 2k/(M_n−1), negligible for polynomial k. Yet the mixture D=(1−w)U+wQ assigns it probability at least w, preserves all the stated diagnostics, and satisfies
```
KL(D||U) ≤ w KL(Q||U) ≤ w ln(M_n(M_n−1)).
```
In fact for *every* fixed first factor, the conditional law of the second factor has Shannon entropy within w ln(M_n−1) of its uniform conditional maximum, using convexity in that row; similarly for the reverse. For any fixed desired polynomial accuracy n^(−a), taking w=n^(−a−2) gives pointwise conditional entropy deficits of order at most n^(−a−1) but nonnegligible amplification. These distributions establish the limits of these statistical diagnostics. They are not proposed procedures for deploying or attacking a cryptosystem, nor do they assert that knowing coarse features enables factoring.

## Relation to earlier work

[Loebenberger–Nüsken, Notions for RSA integers](https://arxiv.org/abs/1104.4356) distinguish entropy estimates from a hardness transfer for sufficiently large generation regions. Their transfer uses cardinality/density comparisons, not Shannon entropy alone. The criterion here is the elementary likelihood-tail version of this distinction at the negligible-probability scale. The exact graph examples isolate what Shannon and coarse marginals cannot determine. Ordinary statistical contiguity concerns probabilities tending to zero rather than detailed polynomial-scale control; see [Pollard's discussion of Le Cam's lemma](https://www.stat.yale.edu/~pollard/Books/LeCamFest/Pollard.pdf). For the classical entropy and divergences see [Kullback–Leibler](https://doi.org/10.1214/aoms/1177729694) and [van Erven–Harremoës](https://arxiv.org/abs/1206.2459). The exponential number of n-bit primes uses only the prime number theorem; see [Rosser–Schoenfeld](https://projecteuclid.org/download/pdf_1/euclid.ijm/1255631807).

There is no unconditional hardness claim even for the uniform source, no implication about a concrete key generator, and no factoring algorithm. The result concerns the logic of transferring an existing average-case success bound on the full product. It is different from [a bound on intentionally restricted input leakage](FactorBoundedInputShadow.md).

[The toy checker](verify-factor-source-transfer.js) checks symmetric regular mixtures, exact two-level likelihood masses, and the class-coupling laws using integer weights over generated tiny label pools. The replay covers 38 exact regular mixtures, 180 partition couplings, 15,492 conditional class checks, and 60 likelihood-tail layer checks. The asymptotic conclusions are proved above, not inferred from experiments.
