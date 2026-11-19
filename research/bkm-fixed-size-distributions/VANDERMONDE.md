# A tight-row bound for fixed-trace squared Vandermonde weights

**Private candidate.** For integers m>n≥1 let π_n(λ) be proportional to Δ(x)^2 on the partitions λ of n, where x_i=λ_i+m−i (1≤i≤m), Δ(x)=∏_{i<j}(x_i−x_j). Equivalently the x_i are strictly decreasing nonnegative integers with sum n+m(m−1)/2. Their largest entry (indeed each ordered entry) has a log-concave distribution. This addresses the squared-Vandermonde fixed-trace question (31) of Baslingker–Krishnapur–Madiman, arXiv:2412.15116v2, §7(i), with their particle-count and size parameters renamed m and n. No statement for arbitrary Vandermonde powers or for m≤n is needed.

We use the coordinate censoring lemma of the accompanying row/word proof, whose hypotheses are a positive reversible down–up chain with all legal moves and an order-preserving coupling for the relation ν_j≤λ_j+1. For t=|λ|≤n the down formula is D_i=(x_i/t)∏_{j≠i}(1−1/(x_i−x_j)) at t>0, as in that lemma. Use the different up formula

    U_i=(x_i+1)/(t+m²) · ∏_{j≠i}(1+1/(x_i−x_j)).

The factors give exactly the legal bounded-row moves; they are nonnegative. Put v_i=∏_{j≠i}(1+1/(x_i−x_j)). The terms of order z^−1 and z^−2 of ∏_j(1+1/(z−x_j)) give ∑v_i=m and ∑x_i v_i=∑x_i+m(m−1)/2=t+m(m−1). Hence ∑U_i=1. The D_i normalization is unchanged. On each legal bond U_i(λ)/D_i(λ+e_i) is (t+1)/(t+m²) times ∏_{j≠i}(1+1/(x_i−x_j))². This equals the ratio of squared Vandermonde weights times a size-only constant. Consequently the level measures proportional to Δ² give detailed balance for the down–up chain (the bond ratio fixes the level normalization, or cancel that constant in the two directions of a two-step move). All weights and legal bonds are positive.

The D tight-row inequalities are unchanged. Unlike the word case the up prefactor x_i+1 itself **increases** on moving to a tight row of ν. Here is the comparison that makes the argument work.

Let λ,ν be related partitions of the same size t<m and let i be tight: a=λ_i, ν_i=a+1. Write c=a+1−i, H=max(ℓ(λ),ℓ(ν)), B=m+c, X=H+c. Thus H≥i and X≥1. Also X≤m: if H=ℓ(λ), use c≤λ_1 and λ_1+H≤t+1≤m; if H=ℓ(ν), use c≤ν_1−1 instead. If ν is not addable at i the desired U_i(λ)≥U_i(ν) is automatic. Otherwise λ too is addable, since for i>1 the inequalities ν_{i−1}≥a+2 and λ_{i−1}≥ν_{i−1}−1 apply.

For j≠i abbreviate

    h_j=1+λ_j−ν_j≥0,     d_j=a−λ_j+j−i,    e_j=ν_i−ν_j+j−i=d_j+h_j.

Put h_i=0; ∑_{j≤H} h_j=H. The factors for i are positive for both diagrams. Write Q=v_i(λ)/v_i(ν). Each row j contributes

    (1+1/d_j)/(1+1/e_j) = 1+h_j/[d_j(e_j+1)],

where the denominator is positive: below i both differences are positive, and above i they are at most −2 because both additions at i are legal. For j>H, d_j=c+j−1, e_j=c+j. Their product telescopes to B(X+1)/[(B+1)X], also valid for H=m. The desired comparison is Q≥(B+1)/B, since x_i+1=B for λ. If M² bounds every positive d_j(e_j+1) for j≤H, j≠i, it is enough that

    (1+H/M²)(1+1/X) ≥ (1+1/B)².                       (A)

Indeed the product of the interior factors is at least one plus the sum of their nonnegative increments, which is at least 1+H/M².

For i<j≤H we have d_j≤X−1 and e_j+1≤X+1, so d_j(e_j+1)≤X²−1. For j<i the following stronger bound is useful:

    d_j(e_j+1) ≤ m(m−H).                                (B)

To check it, write W_λ=λ_1, W_ν=ν_1, H_λ=ℓ(λ), H_ν=ℓ(ν). The two factors in absolute value are at most W_λ−c and W_ν−c−2, respectively. Since λ_{i−1}≥a+1 and ν_{i−1}≥a+2, lower bounds for the boxes outside the first row give

    W_λ−c ≤ m−ia−max(H_λ−i,0),      W_ν−c−2 ≤ m−1−ia−H_ν.

For the first, count at least (i−2)(a+1)+a+max(H_λ−i,0) boxes outside row one; for the second count (i−2)(a+2)+(a+1)+(H_ν−i) and use t≤m−1. Both factors are at most m. If H=H_ν the second is at most m−H. If H=H_λ>H_ν, then H_λ≥i, a≥1, so ia≥i and the first is at most m−H. This proves (B).

**Case c≥0.** Use M=m because X≤m and (B) holds. Here 0≤c≤m−1. For integer 1≤X≤m define F(X)=(1+(X−c)/m²)(1+1/X). Its forward difference is

    F(X+1)−F(X)=1/m²−(1−c/m²)/[X(X+1)] ≤0     (1≤X<m),

because X(X+1)≤(m−1)m≤m²−c. Thus F(X)≥F(m). Subtracting (1+1/(m+c))² from F(m) gives

    c[(m+1)(m²−c²)−cm]/[m³(m+c)²] ≥ 0:

m−c≥1 implies the bracket is at least (m+1)(m+c)−cm>0. This proves (A).

**Case c<0.** Write h=−c=i−1−a. Then H≤m−i≤m−h−1. Indeed the first i−1 rows of ν have length at least a+2≥2, so H_ν≤t−(i−1)≤m−i. If a≥1 the first i−1 rows of λ also have length at least 2, giving the same bound; if a=0, H_λ<i≤H_ν instead.

If H≤2h, then B=m−h≥H+1≥2(H−h)+1=2X+1. This implies 1+1/X≥(1+1/B)², so the tail alone suffices. If H>2h, (B) gives m(m−H)≤m(m−2h)≤(m−h)²=B², and X≤B. Take M=B; since H≥X, (A) follows from

    H/B²+1/X ≥ X/B²+1/X ≥ 2/B,       H/(B² X) ≥ 1/B².

All comparisons are now proved, including ties and inadmissible moves.

At each tight row match the left down mass inside the right down mass, and in an up step match the right up mass inside the left up mass. The remaining marginals can be coupled arbitrarily; the integer slack protects every unmatched row. This proves the required order-preserving proposal property. The coordinate lemma yields log-concavity of all row marginals and therefore of x_1=λ_1+m−1, as asserted.
