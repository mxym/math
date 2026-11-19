# A 144-vertex one-family example

Here is a smaller consequence of the same eleven-feature obstruction and [Forster's lower bound](https://www.sciencedirect.com/science/article/pii/S0022000002000193). It is not claimed to be the smallest such graph. The argument deliberately uses the *full compatibility table*, including its true self-compatibility entries.

**Seed matrix.** Index U by {∞}∪F₁₁. The row and column indexed by ∞ are identically +1. For i,j∈F₁₁ put U_ii=−1 and, when i≠j, U_ij=χ(j−i), where χ is +1 on the nonzero squares {1,3,4,5,9} and −1 on the other nonzero elements. For the following calculation extend χ(0)=0 and write Q_ij=χ(j−i).

Each row of Q sums to zero, Qᵀ=−Q because −1 is a nonsquare, and QQᵀ=11I−J, where J is the all-ones matrix. For the last identity the diagonal sums are 10; for i≠k the substitution t=(z−i)/(z−k) bijects F₁₁∖{k} to F₁₁∖{1}, so the sum over z of χ((z−i)(z−k)) is Σ_(t≠1) χ(t)=−1. The omitted term z=k is zero. The bottom-right block of U is Q−I; its rows have sum −1. Therefore the finite rows of U are orthogonal to the ∞ row, and their row Gram matrix is J+(Q−I)(Q−I)ᵀ=12I. Hence UUᵀ=UᵀU=12I.

**The graph.** On the 144 ordered pairs (i,j) of seed indices define the symmetric sign matrix

    S_((i,j),(k,l)) = U_il U_kj.

Its diagonal entries are +1. Connect distinct vertices exactly where this entry is +1. The full pairwise compatibility table for a hypothetical binary-qubit realization must equal S, including the diagonal because a measurement is always jointly measurable with itself. For two arbitrary vertices (i,j),(p,q),

    (S²)_((i,j),(p,q))
      = Σ_(k,l) U_il U_kj U_kq U_pl
      = (UUᵀ)_ip (UᵀU)_jq
      = 144 δ_ip δ_jq.

Thus ||S||₂=12 and sign-rank(S)≥144/12=12. On the other hand the two families in the [eleven-feature lemma](PROOF.md) may be equal; treating them as the row and column copies of this one measurement set shows sign-rank(S)≤11. This is a contradiction. Although some resulting *real score matrix* need not be symmetric after making boundary zeros positive, sign-rank only asks for a matrix realizing the symmetric strict signs and requires no symmetry of that real witness.

This graph and its flag complex are therefore unrealizable by binary qubit POVMs. The existence of a finite many-outcome qubit realization is consistent with this lower bound ([unrestricted construction](https://github.com/mxym/math/pull/118)).

The design is classical: the seed is [Paley's quadratic-character construction](https://doi.org/10.1002/sapm1933121311), and the symmetric constant-diagonal Hadamard square is a reordered tensor product, as in [Goethals–Seidel (1970)](https://doi.org/10.4153/CJM-1970-067-9) and [Kharaghani (1986), Corollary 2](https://doi.org/10.1017/S1446788700028044). The claim here concerns its incompatibility with binary qubit realizations, not the construction or novelty of the sign matrix.
