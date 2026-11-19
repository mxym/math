# Strict log-concavity of the first row of fixed-size Jack–Plancherel diagrams, and two matching conjectures

**Private candidate; 2026-11-19.** Let `cr` be the maximum number of mutually crossing arcs in a perfect matching of [2n], and let LIS be the ordinary one-line longest increasing subsequence of the associated fixed-point-free involution. These are *different statistics with different distributions*. For each statistic its counts, in order of its values 1 through n, are strictly log-concave at every interior index. This gives Chen's 2008 Conjecture 1.4 for crossings and the fixed-point-free involution statement of Bóna–Lackner–Sagan (BLS) Conjecture 4.2 for LIS. The statement for n=1,2 has no interior test. Extending by zeros through 2n gives ordinary log-concavity, not strictness in the zero tail.

In fact the first-row marginal of the fixed-size Jack–Plancherel measure is strictly log-concave for *each positive Jack parameter*. Our convention is θ=1/α for Matsumoto's Jack parameter α. The ordered down–up coupling and the stationary slice argument are an adaptation of **Yupeng Li, arXiv:2610.36483, §§4–5**, not a new proof strategy. The growth process, hook formulas, and matching/tableau interpretations are classical. The extension below verifies the parameter-dependent transition formulas, order comparisons and strictness rather than assuming Li's ordinary Plancherel theorem applies to a different measure.

## 1. Explicit probabilities and level weights

Fix the target n and pad all partitions involved with zeros to L≥n+1 rows. At level m≤n write x_i=λ_i+θ(L−i) for i=1,…,L. These are strictly decreasing, pair gaps having absolute value ≥θ, and x_L=0 on levels ≤n. Write

    D_i(λ) = (x_i/m) ∏_{j≠i} (1−θ/(x_i−x_j)),    m>0,
    U_i(λ) = θ/(x_i+θ) ∏_{j≠i} (1+θ/(x_i−x_j)).

They are nonnegative, and strictly positive precisely on removable and addable rows respectively (for the up step we use m<n). A repeated equal part immediately below or above creates a zero in the corresponding product. The last zero row has removal factor x_L=0. For all other terms, strict positivity follows from the row order and the fact that equality of the shifted gap to ±θ requires adjacent equal parts.

For completeness, set P_±(z)=∏(1±θ/(z−x_j)). The residue at x_i equals ±θ v_i^±, where v_i^± is the corresponding product over j≠i. These rational functions tend to 1 at infinity, so their partial fractions are 1±θ∑v_i^±/(z−x_i). Evaluating P_+ at −θ, which is a zero since x_L=0, yields ∑U_i=1. Equating the coefficients of z^−2 at infinity for P_− gives ∑x_i v_i^−=∑x_i−θ L(L−1)/2=m, so ∑D_i=1.

Here is a convenient full formula demonstrating detailed balance. Set H(z)=z Γ(z+θ)/Γ(z+1−θ) for z≥θ, and

    G(λ) = ∏_{i<j} H(x_i−x_j) / ∏_i [Γ(x_i+1)Γ(x_i+θ)] ,
    π_m(λ) = m! θ^m G(λ)/G(∅).

These are the usual Jack–Plancherel probabilities with α=1/θ, by the gamma-product hook formulas in Matsumoto, Lemma 4.1; the level scale is also checked here. For a legal addition in row i, gamma recurrence gives

    π_{m+1}(λ+e_i)/π_m(λ) =
      (m+1)θ/[(x_i+1)(x_i+θ)] · ∏_{j≠i}
      (x_i−x_j+θ)(x_i−x_j+1) / [(x_i−x_j)(x_i−x_j+1−θ)] .     (1)

For j>i this uses H(z+1)/H(z); for j<i use H(z−1)/H(z) with z=x_j−x_i; the inverse shifted factors simplify to the same displayed expression. Legal addition implies all these denominators are nonzero (if j<i and the row is addable then x_j−x_i≥θ+1; if j>i then x_i−x_j≥θ). The right side of (1) is exactly U_i(λ)/D_i(λ+e_i). Thus π_m U and π_{m+1} D give the same mass to each bond. Starting with π_0=1, summing over bonds and using the probability sums proves normalization. The down–up chain K=DU on size n is reversible for π_n since each common predecessor contributes symmetrically by the bond identity. No irreducibility assumption is used for this identity.

## 2. Coupling and censoring

For diagrams of the same size put λ R ν when ν_j≤λ_j+1 for every j, and call row i tight if ν_i=λ_i+1. At a tight row i let y_j=ν_j+θ(L−j). Then y_i=x_i+1 and y_i−y_j≥x_i−x_j for all j. The old and new differences have the same sign for each j, so no pole is crossed. The function 1−θ/z is increasing on each sign interval, the function 1+θ/z is decreasing there, and all factors in use are nonnegative. Consequently

    D_i(λ)≤D_i(ν),       U_i(λ)≥U_i(ν)   (at tight rows).

For a tight **first** row the second comparison is strict: all its factors are positive, and θ/(x_1+θ)>θ/(y_1+θ). This covers blocked moves without dividing by zero.

For a down-step couple the row numbers by pairing all probability D_i(λ) on each tight i with the same amount of D_i(ν) on that row. Couple the remaining marginals arbitrarily, for instance by their normalized product when their common remaining mass is nonzero. If a removal on the left is in a tight row, it is thus also the row removed on the right. All other distinct-row removals satisfy the relation since the left removal is at a slack integer coordinate. For up-steps instead match all U_i(ν) on each tight row, and couple the remainder arbitrarily. This also preserves R. Apply the down coupling first, then the appropriate up coupling conditionally. This gives coupled K-moves whose terminal diagrams satisfy R whenever the starting diagrams do.

For 1≤k≤n let π_{n,k} be π_n conditioned on first row k. Rejecting a full K-proposal whenever its first row is not k preserves detailed balance on this slice. The censored kernel is irreducible: whenever the lower rows contain some part ≥2, remove a box from the last lower row of length ≥2, then add it as a new bottom row of length 1. This is legal and preserves the first row; repeating reaches (k,1^{n−k}). The inverse moves are positive by detailed balance. If no such part exists, one is already at this hook. Thus π_{n,k} is the unique stationary law there.

For consecutive slices start with a pair in R, e.g. the two hooks. Couple the full K-proposals as above and reject separately for the two slices. Joint rejection or joint acceptance preserves R. If the left first row alone leaves k, the right proposal has first row k+1 and R forces the proposed left first row to be k+1 (its change has magnitude at most 1). All other left coordinates can have only decreased, so restoring the original left diagram preserves R. If the right first row alone leaves k+1, the proposed left first row is k and the right one must have decreased to k. All other right coordinates have only increased, so restoring the original right diagram also preserves R. Therefore the paired restricted chain stays in the finite nonempty related set. It has a stationary law there; each marginal is stationary for its own censored kernel, hence equals its indicated conditional π-law. This provides a coupling of π_{n,k},π_{n,k+1} supported on R.

## 3. Strictness and flux

Let b(λ),d(λ) be probabilities that a full K-step increases, decreases the first row respectively. For a related pair with first rows k,k+1, the ordered result of §2 ensures that right growth implies left growth, and left shrinkage implies right shrinkage. Thus b(λ)≥b(ν), d(λ)≤d(ν).

We need strictness. In the removal coupling first-row removal on the left is matched to first-row removal on the right. If ν has a lower row, its last positive lower row is removable with positive probability. Consequently both removals are below the first row with positive probability. For every such paired pair of predecessors the first row is still tight; the first-row up probability on the left is strictly higher, and right first-row additions are all paired with left first-row additions. Thus with positive probability the left first row grows but the right one does not. If ν has no lower row, then b(ν)=0; λ has first row n−1 and a removable lower box, so b(λ)>0. In either case b(λ)>b(ν).

Averaging in the preceding stationary coupling gives b_k>b_{k+1}, d_k≤d_{k+1}, where the subscript means expectation under π_{n,k}. All fluxes between neighboring slices are positive: the k-hook can move its bottom box to the first row for k<n, and the reverse has positive probability. Put A_k=π_n{λ_1=k}. Detailed balance on the cut between consecutive slices yields A_k b_k=A_{k+1}d_{k+1}. For 1<k<n,

    A_k/A_{k−1} = b_{k−1}/d_k > b_k/d_k ≥ b_k/d_{k+1}=A_{k+1}/A_k.

This proves the Jack first-row theorem.

## 4. Two different matching specializations

Write f^ρ for the number of standard tableaux of shape ρ. For a partition λ of n define λ∪λ=(λ_1,λ_1,λ_2,λ_2,...) and 2λ=(2λ_1,2λ_2,...). By RSK and Schützenberger's characterization of the fixed points via odd columns, fixed-point-free involutions of 2n are counted once per standard tableau of every even-column shape. Such shapes are exactly λ∪λ. Their first row (ordinary LIS) is λ_1 and their number of rows (ordinary LDS) is 2ℓ(λ).

The following measure identifications are classical (Matsumoto 2008, Lemmas 3.1–3.2); they can also be read directly from Vandermonde hook dimensions, f^ρ=|ρ|!∏_{i<j}(b_i−b_j)/∏_i b_i! for padded b_i=ρ_i+length−i.

* At θ=2, b for λ∪λ consists of the pairs x_i+1,x_i. Each pair of blocks contributes (x_i−x_j)^2((x_i−x_j)^2−1) and each block has factorials (x_i+1)! x_i!. This is precisely G(λ) up to constants at fixed n, since H(z)=z²(z²−1). Thus the first-row distribution of a uniform fixed-point-free involution (and BLS 4.2) is the Jack marginal at θ=2.
* Equidistribution of the maximum sizes of crossings and nestings is the crossing–nesting theorem of Chen, Deng, Du, Stanley and Yan. For each matching its maximum nesting equals half of the LDS of its involution. In fact a decreasing subsequence visits upper-triangle points (a,b), a<b, before lower-triangle points: after i>σ(i) a subsequent j<σ(j) cannot occur in a decreasing subsequence. The upper-triangle part is a nested family (openers increase while closers decrease); the lower-triangle part likewise is a nested family by reflection about the diagonal and reversing order. Each part thus has length ≤ maximum nesting, and a nested family of size r gives a decreasing subsequence of length 2r by appending its reflected endpoints. Hence the crossing distribution equals that of ℓ(λ). Transpose λ to μ: as f^ρ=f^{ρ′} and (λ∪λ)′=2μ, this is the first-row distribution under weights f^{2μ}. At θ=1/2 the hook coordinates for 2μ are 2x_i and H(z)=z. Using Γ(x+1)Γ(x+1/2)=√π·2^{−2x}Γ(2x+1), the G-weight is proportional to ∏_{i<j}(2x_i−2x_j)/∏_i(2x_i)!, since ∑ x_i is constant at fixed n. This proves Chen's literal 1.4.

Both distributions have support all integers 1,…,n because each of the requisite diagram slices contains a hook, with strictly positive weight. For n=2 their respective lists are (1,2) for LIS and (2,1) for crossings. There is no inference here about unrestricted involutions (BLS 1.2), squared weights on even-column shapes (BLS 4.3), infinite log-concavity, or q-log-convexity across different n. The fixed-size ordinary permutation case θ=1 is already Li's theorem.
