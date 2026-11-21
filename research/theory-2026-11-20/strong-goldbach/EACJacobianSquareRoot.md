# Square-root sparsity for invertible exponent matrices, including all four-label components

Let K(X)=o(√(log X/loglog X)). The number of even centers N≤X possessing a [Bożek exceptional autonomous component](https://arxiv.org/abs/1909.09900) with k≤K(X) labels and **invertible A** is at most X^{1/2+o(1)}. Here A_{ij}=v_{p_j}(N−p_i), without a bound on multiplicities, and the condition is det A≠0, *not* det(I−A)≠0. There is no lower bound on the smallest prime label. In particular the estimate includes the case of singular I−A and very small labels.

Combining this result with [the independent order-divisor estimate for invertible I−A](EACNonsingularSquareRoot.md), outside at most X^{1/2+o(1)} centers every EAC of size k≤o(logloglog X) must possess **both** eigenvalues 0 and 1 for A. No four-label EAC can possess both. Indeed A has zero diagonal and nonnegative entries, and the row sums are at least two, so its Perron eigenvalue ρ is at least two and is its spectral radius. Four eigenvalues counting multiplicities would be 0,1,ρ,−(1+ρ), impossible by the trace-zero identity and the spectral radius bound. Therefore the number of centers ≤X with an EAC of four labels is at most X^{1/2+o(1)}, allowing every possible exponent/signature. This is a count of centers supporting components, not of the exceptional set for Goldbach. The conjectured nonexistence of *all* four-label EACs does not follow.

### Quantities fixed before counting

Only √X<N≤X matters, since there are at most √X smaller centers. Label the k vertices in any order. Let D=max_i ∑_j A_{ij}≤log X/log 3, S₀=kD^{k−1}, B=4+4S₀. Cofactor expansion with Hadamard's inequality and |det A|≥1 give ||A^{-1}||∞≤S₀ (maximum absolute row sum). Uniformly in the indicated k range, B^k=X^{o(1)}, so B<√N for large X.

In the actual tuple **fix all labels p_i≤B to their actual integer values**, not just one smallest label. The counting step will pay for these few-bit parameters. The next two claims use the linearized complex equations at the physical tuple, with those parameters fixed. Write n=δN/N and h_i=δp_i/p_i, so the ordinary polynomial equations p_i+∏p_j^{A_{ij}}=N give
     
    (Ah)_i=(1+C_i)n−C_i h_i,          C_i=p_i/(N−p_i)≤1/2.             (1)

The last inequality holds since each label divides an odd composite row and is ≤(N−3)/3.

### 1. There is no nonzero tangent with n=0

Call a label high in this paragraph if q>N/B. For each high q choose one incoming row with q as a factor; such a row exists by strong connectivity. Exactly N−p_j=u q where u<B, so u's prime factors are fixed labels. In particular the multiplicity of q in that row is one (q>√N>B). Differentiating this one equation at n=0 gives h_q=−C_j h_j.

If j is nonhigh, C_j≤1/(B−1). If j is high, follow high parents backwards. Each further step contributes a factor of modulus ≤1/2. A repeated high vertex forces its h to vanish since the product of the contraction factors has modulus <1; otherwise the finite chain ends at a nonhigh parent. In every case |h_q|≤||h||∞/(B−1). Thus in (1) with n=0 one has ||diag(C)h||∞≤||h||∞/(B−1): this uses the bound on h at high coordinates and the bound on C at nonhigh ones. Inversion of A now gives ||h||∞≤S₀||h||∞/(B−1), forcing h=0. Consequently the tangent space after fixing all the tiny labels has complex dimension at most one.

### 2. If one mode remains, it moves some label at most √N

Suppose that a nonzero tangent fixes every p≤√N to first order. Then n≠0 by the first claim. A row either has all factors ≤√N or has exactly one factor q>√N. In the latter case put N−p=u q. All factors of u are fixed to first order under this supposition, and u≥3. Set z_p=δp−pn. Direct differentiation gives z_q=−z_p/u.

Start at any p≤√N, which exists by taking a least prime factor of a composite row. Here z_p=−pn≠0 and |z_p|≤√N |n|. Follow the unique >√N factor when present. If a row has no such factor, its entire complementary product is fixed to first order, giving δp=δN and |z_p|=(N−p)|n|≥(2N/3)|n|, inconsistent with the nonincreasing absolute values from the start (N>4 suffices). A repeat instead forces z_p=0 on the cycle since every u≥3, also impossible. These exhaust the finite path. Hence if the tangent dimension is one, there is an index j with p_j≤√N for which h_j≠0. Fixing p_j kills that tangent. If the tangent was already zero, choose any such j. This proof does not infer any strict positivity of A^{-1}1 or assume the tuple lies on a predetermined algebraic curve.

### 3. Count isolated solutions, not entire fibers

Enumerate k and all integral matrices A with entries ≤log X/log 3, all index subsets for the tiny labels and their values ≤B, and one extra index j and value p_j≤√X. Redundancy when j was already fixed is harmless (choose consistent value). The number of choices aside from p_j is
     
    ≤ X^{o(1)},

because (D_max+1)^{k²}, 2^k B^k, and k² each have logarithm O(k² loglog X+k log k)=o(log X). The maximum over k and its sum obey the same bound. This enumeration need not decide in advance which tuples satisfy the defining inequalities: only covering actual tuples is required.

For each such choice substitute the fixed values into the k polynomial equations, leaving n_v≤k free complex variables, including N. At each physical point with the choices from §§1–2 the common tangent is zero: its Jacobian has rank n_v. Select n_v independent equation gradients at that point (at most 2^k choices of row subset overall). Each resulting square polynomial system of degrees ≤D has at most D^{n_v} such nonsingular isolated zeros by ordinary affine Bézout. One can see this even if other components are positive-dimensional by keeping any finite list of nonsingular zeros in disjoint neighborhoods: a sufficiently small generic coefficient perturbation retains a zero in each by the complex implicit function theorem, while the perturbed system has at most D^{n_v} affine zeros by projective Bézout. Thus the bound is on the intended finite isolated points and makes **no purity-of-dimension hypothesis**. Since 2^k D^k=X^{o(1)}, the extra parameter p_j contributes the sole √X factor. This proves the theorem.

## Related 2026 claims

The [Kelanemer SSRN record, dated August 12](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) treats terminal factorization components using exponent matrices and announces low-dimensional exclusions under its proposed counterexample argument. Its full text could not be retrieved for verification. The statement here is specifically an unconditional count of actual component-bearing centers using the Jacobian and the bounded-degree count, including centers that are already represented; it is not a claim of complete four-label exclusion or priority over the SSRN work.
