# Nullity forces more macroscopic prime labels than its dimension

For an even N, let C be k distinct odd primes <N−1, coprime to N. Suppose that each N−x for x∈C is composite with all its prime factors in C. No assumption of strong connectivity or Goldbach failure is needed. Put A_{xy}=v_y(N−x), B=I−A, ν=nullity_ℚ B. The following apply to the *actual* primes, not abstract graphs.

1. **Exact cutoff.** For U≥3 with N−U>U^{2k−3}, the rows of B indexed by x≤U are independent, so at least ν labels are >U. In the exponent 2k−3 one may instead use 2d−1 if at most d distinct factors occur in each row indexed by x≤U.
2. **One more macroscopic label.** For each fixed k there are constants η_k>0 and N_k such that for N>N_k, whenever ν≥1, at least ν+1 distinct labels exceed N^{η_k}. No numerical value for η_k is asserted.
3. **Product inequality.** In every dependent subset of rows I, the product of the input labels in I other than its least one is ≥N/(log N)^{O_k(1)} for all sufficiently large N. In particular, if x₁<⋯<x_k and ν≥1, then x₂⋯x_{k−ν+1}≥N/(log N)^{O_k(1)}.

By [the single fixed-seed and moving generator theorem](PrimeOrbitMovingSeed.md), any hypothetical Goldbach failure at a sufficiently large even N with S-part N_S≥N^{1/2+ε} has the following property: for any prescribed odd seed p coprime to N, its all-composite forward orbit either exceeds a given size cap K, or contains **at least three distinct primes >N^{η}**, with η>0 depending only on K. Make the thresholds uniform over k≤K by taking a finite minimum/maximum. This does not assert every orbit is bounded, that all three labels lie in a terminal component, or that any Goldbach failure exists.

## Private prime powers: exact small-row independence

Write n_i=N−x_i. For distinct inputs i,h, gcd(n_i,n_h) divides x_i−x_h. For each row i with x_i≤U mark J_i={j:x_j^{A_ij}>U}. Such a set is nonempty: there are at most k−1 outgoing factors without multiplicity, by (x_i,N)=1, and n_i≥N−U>U^{k−1} for k≥2. For the degree-d version use 2d−1≥d. The J_i are pairwise disjoint, by the gcd bound. Form disjoint test columns v_i=Σ_{j∈J_i}(log x_j)e_j. The square matrix of B_h v_i on these small row indices is strictly row-diagonally dominant. Indeed its diagonal magnitude is H_i=log n_i−R_i, with R_i=Σ_{j∉J_i}A_ij log x_j≤(d−1)log U. The sum of the absolute off-diagonal entries is at most R_i+log x_i (own diagonal of B may occur in another test column). The cutoff hypothesis gives H_i>R_i+log x_i. This proves (1). No nontrivial one-label configuration is possible.

## A first-order congruence detects short left dependencies

For any dependent subset I, choose a circuit inside it, an inclusion-minimal linearly dependent subset J of rows over ℚ. Signed maximal minors after choosing |J|−1 independent columns give c∈ℤ^k, cᵀB=0, supported exactly on J, with all |c_j|≤D_k=(k!)(1+log N)^k. This follows since the entries of B have magnitude ≤1+log N. If all x_j in J were at most D_k, (1) with U=D_k would make J independent for sufficiently large N (k fixed). Thus some x_i>D_k≥|c_i| in J.

For completeness, the prime rows themselves give ∏_j x_j^{B_ij}=x_i/(N−x_i). As a rational identity cᵀB=0 hence gives ∏_j ((N−x_j)/x_j)^{c_j}=1. On reduction modulo N, (−1)^{Σc_j}=1 since all labels are units and N>2. Cancel that sign, expand ∏_j(1−N/x_j)^{c_j}=1 modulo N², and divide by N; negative exponents are valid via unit inversion. It follows that
     
    N divides D(c)=Σ_{j∈J} c_j ∏_{h∈J, h≠j} x_h.

The numerator is nonzero, since modulo x_i it is c_i times a unit. Each product in D(c) is at most the one omitting the smallest input, and |D(c)|≥N. Enlarging J to I cannot decrease the product with the least input omitted, proving (3); for its last implication take the first k−ν+1 rows.

## The equality case in logarithmic scaling

It suffices to show that along any sequence N→∞ with k,ν fixed, every convergent subsequence of the vectors of logarithmic weights has at least ν+1 positive limits. Indeed a failure of (2) gives a sequence with the (ν+1)-st largest logarithmic weight tending to zero; only finitely many ν need be considered. Order the labels increasingly. Pass to limits of the bounded entries
     
    w_i=lim log x_i/log N,     P_ij=lim A_ij log x_j/log N,
    W=diag(w_i).

Every input either is at most N/2 or is above N/2. In the second case it need not have an incoming edge, so we must explicitly ensure that n_i does not become small. We first prove the equality-case argument under the assumption n_i=N^{1+o(1)} for all i; the final paragraph removes that assumption. Under it, P is nonnegative with all row sums one. Rank(P−W)≤k−ν because it is a limit of (A−I)diag(log x_j/log N). Split into small inputs L={i:w_i=0} and big inputs H={i:w_i>0}, writing t=|H|. For distinct i,h∈L, log gcd(n_i,n_h)=o(log N), so the supports of P_i,P_h are disjoint. Since their row sums are one and W vanishes on those rows, their independence gives t≥ν.

Suppose t=ν. Then the small rows form a basis of the row space of P−W (and the corresponding rows of B are independent for all sufficiently large terms). Every i∈H belongs to the support of some small row P_r: the i-th coordinate of P_i−w_i e_i equals −w_i≠0, since A_ii=0. The small rows together with row i are dependent in the physical rational B, whose rank is k−ν. For a circuit among them the coefficient c_i must be nonzero. All other labels in the circuit are N^{o(1)}. The just-proved inequality (3), or its numerator proof, forces w_i=1 because the product of its non-least labels is at most x_i N^{o(1)}. This holds for every i∈H.

Fix now such an i and its small parent r. Since P_ri>0, for all sufficiently large terms the actual prime x_i divides n_r; write n_r=a_i x_i. As w_i=1, a_i=N^{o(1)}. For **every** small h,
     
    a_i n_i−(a_i−1)n_h = x_r+(a_i−1)x_h >0.

The right-hand side is N^{o(1)}, hence so is gcd(n_i,n_h). Thus the support of P_i is disjoint from every small row's support. It is nonempty, whereas the coordinate i does belong to the union of small supports. Consequently P_i−w_i e_i has a nonzero entry outside that union and cannot lie in their span, a contradiction.

**Rows with no incoming factor.** To remove the auxiliary assumption, iteratively delete all source labels (no incoming arc in the current factor graph). Every deletion preserves closure, since no retained row uses the deleted label. It preserves ν since the source's column in B is its unit coordinate vector. The nonempty residual core when ν>0 has every label occurring in some odd composite row, hence bounded by (N−3)/3. All its complements are between 2N/3 and N, so the preceding proof applies to this core, which has at most k vertices and the original ν. Its ν+1 macroscopic labels occur in the original C. Take the finite minimum of η over possible core sizes. In particular this also proves that ν+1 such primes survive pruning of all sources; that core need not be a single terminal strongly connected component. The removal argument is not needed for (1) or (3), which used only the sizes of their small inputs.

The complementary-factor setup is from [Bożek](https://arxiv.org/abs/1909.09900). [Kelanemer's August 2026 record](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) treats related exponent matrices and spectral restrictions, but its full paper was not available for audit. The statements here apply to all bounded actual composite closures, including reducible ones; they do not assume or prove an upper bound for prime-factor orbits.
