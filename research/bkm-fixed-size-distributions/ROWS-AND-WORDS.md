# Fixed-size lower row marginals and weak LIS of random words

**Private mathematical candidate, 2026-11-19.** In §7, open problems (ii) and (iii), Baslingker, Krishnapur and Madiman (arXiv:2412.15116v2, pp. 20–21) ask about lower rows at fixed Plancherel size and the weakly increasing subsequence problem for a fixed-length uniform word (their equation (32)). Here we prove the following.

1. At fixed size n≥1 and every positive Jack parameter, the marginal of each ordered row λ_r is log-concave. This includes ordinary Plancherel, hence the *individual-row* part of (ii), not its question about sums of rows.
2. For each m,n≥1, the length of the longest **weakly** increasing subsequence of a uniform word in [m]^n has a log-concave distribution, answering (iii). In fact every individual row of the fixed-size Schur–Weyl shape has a log-concave distribution. These conclusions are weak inequalities, including any zeros outside the support.

This adapts the ordered down–up coupling of Yupeng Li (arXiv:2610.36483, §§4–5) and the Jack first-row note at [repository commit af1b5757](https://github.com/mxym/math/blob/af1b5757288006b7228f3040073b40230855e8fe/research/jack-matching-logconcavity/PROOF.md). We give the slice and finite-row details needed here rather than assuming that first-row log-concavity implies a lower-row or random-word result.

## 1. A coordinate version of the slice argument

Fix m rows and level n. In the unrestricted Young graph we may take m=n+1 (pad with zeros); in a genuinely bounded graph m can be less than n. Suppose a positive law π_n on these diagrams is reversible for a down–up kernel K, in which every legal removal followed by every legal bounded-row addition has positive transition probability. Assume that whenever λ,ν have equal size and ν_i≤λ_i+1 for all i, their full K proposals admit a coupling preserving that same relation, denoted R. The coupling assumption concerns size n, not equivalence of a projected process with a Markov chain.

Fix row r≤m, put S_k={λ:λ_r=k}. Its support is contiguous: for r=1 it is ceil(n/m),…,n, by filling up to m rows with capacity k, first row equal to k. For r≥2 it is 0,…,floor(n/r); a diagram for each such k is C_k=(n−(r−1)k,k repeated r−1 times), omitting zero parts.

The kernel obtained on S_k by rejecting moves out of S_k is reversible for the conditional law and irreducible:
* For r=1, fill earlier rows first. If the diagram is not already (k,…,k,s), 0≤s<k, take the first row u≥2 that is shorter than k and remove from the last positive row j>u; add to row u (the preceding row has length k). Such a j exists unless the diagram is already the displayed terminal diagram. All moves preserve the row cap, increase the diagram lexicographically, and terminate. Reverse transitions are positive.
* For r≥2, transfer to row 1 any available surplus. If there is any positive part below r, take the bottommost one as donor. Otherwise, if some row in 2,…,r−1 exceeds k, take the *last* such row; the next row has length k, making removal legal. Row 1 is always addable. These moves reach C_k and are reversible, also when k=0 or r=m.

For consecutive nonempty slices there is a related cross-slice edge. When r=1 take any λ∈S_k and move a box from its bottommost positive lower row to row 1 (there is one for k<n). When r≥2, from C_{k+1} move one box out of row r into row 1. Row r has size k+1 and no positive part below. The resulting λ in S_k and ν=C_{k+1} are related. In particular the aggregate stationary flux across each adjacent cut is positive. If there is only a single slice there is nothing to show.

On related pairs in S_k×S_{k+1} draw coupled K proposals, then restore each diagram individually if it leaves its own slice. For joint acceptance or rejection R persists. If only the left diagram leaves, the right final coordinate is k+1 and R forces the left coordinate to have grown to k+1, so every other left coordinate can have only decreased. Restoring the left original is safe. If only the right diagram leaves, it must have shrunk in row r, so all its other coordinates can have only increased. Restoring the right original is safe. Thus the coupled restricted finite chain has a stationary measure supported on R. Its marginals are stationary for their individually censored, irreducible kernels, so they equal exactly π_n conditioned on the corresponding slices.

Write b_k,d_k for the conditional expectations of the probabilities of increasing, respectively decreasing, row r under full K. A related proposal starting with r-th coordinates k,k+1 cannot exhibit right growth without left growth, nor left shrinkage without right shrinkage. Therefore b_k≥b_{k+1} and d_k≤d_{k+1}. For A_k=π_n(S_k) detailed balance gives A_k b_k=A_{k+1}d_{k+1}, and both sides are positive on adjacent nonempty slices. Then at every interior supported k,

    A_k/A_{k−1}=b_{k−1}/d_k ≥ b_k/d_{k+1}=A_{k+1}/A_k.

For r>m with implicit zero padding the law is a point mass at zero.

## 2. The measures

**Jack.** Take m=n+1. The complete transition formulas in §§1–2 of the cited first-row note give all hypotheses, including the ordered full K coupling before censorship. Nothing in that full-proposal coupling selects a distinguished row: match the left down mass on every tight row to the right down mass on the same row, then match the right up mass on every tight row to left up mass on the same row. Thus §1 proves the claim for each r, including r=1 already proved with strict interior inequalities in the earlier note. This does not rely on depoissonization.

**Finite-alphabet words.** Fix m and set x_i=λ_i+m−i, i=1,…,m, at level t=|λ|. Define

    D_i(λ)=(x_i/t) ∏_{j≠i} (1−1/(x_i−x_j)),   t>0,
    U_i(λ)=(1/m)   ∏_{j≠i} (1+1/(x_i−x_j)).

The last coordinate x_m=λ_m is not assumed to vanish. Products are nonnegative, and zeros are precisely the blocked moves within the m-row graph: for a repeated neighboring part the corresponding product vanishes, and if the bottom part is zero the removal prefactor x_m vanishes. The residues of ∏(1±1/(z−x_j)), matched to its first two coefficients at infinity, give ∑_i∏_{j≠i}(1+1/(x_i−x_j))=m and ∑_i x_i∏_{j≠i}(1−1/(x_i−x_j))=∑x_i−m(m−1)/2=t. Both laws are therefore normalized without using a padded zero row.

Under ordinary word RSK, π_t(λ)=f^λ s_λ(1^m)/m^t: there are f^λ choices of standard recording tableau and s_λ(1^m) semistandard insertion tableaux. The first row equals the longest weakly increasing subsequence. By the Vandermonde hook and Weyl dimension formulas, with Δ(x)=∏_{i<j}(x_i−x_j), δ=(m−1,…,0),

    π_t(λ)= (t!/m^t) · Δ(x)²/[Δ(δ)∏_i x_i!].

For a legal addition at i, the ratio π_{t+1}(λ+e_i)/π_t(λ) equals (t+1)/(m(x_i+1)) times ∏_{j≠i}(1+1/(x_i−x_j))². Direct cancellation gives exactly U_i(λ)/D_i(λ+e_i), hence the down–up kernel is reversible for π_t, with positive mass on every legal two-step move. At a tight row i, the right shifted coordinate equals x_i+1 and each signed difference x_i−x_j increases weakly without changing sign. The down product factors and its prefactor are nondecreasing, while the up factors are nonincreasing and its prefactor is constant. The resulting tight-row inequalities D_i(left)≤D_i(right), U_i(left)≥U_i(right) enable exactly the legal matched-row coupling above. Applying §1 proves all finite-alphabet row claims. At m=1 the single possible shape is (n).

These results address neither sums of rows, the fixed-trace Vandermonde-square question (31), nor longest common subsequences of random words. No assertion of strictness beyond previous first-row results is necessary.
