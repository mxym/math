# Supported minors and power-saving sparsity for all five-label components

Suppose a Bożek [exceptional autonomous component](https://arxiv.org/abs/1909.09900) has k distinct labels at even N. In particular, its labels are odd primes coprime to N; N−p_i is composite and has all its prime divisors in the component. Write A_{ij}=v_{p_j}(N−p_i), B=I−A, and ν=corank_Q B. The directed factor graph is strongly connected and loopless. We count **centers of actual EACs**, not failures of binary Goldbach.

**Supported-minor lemma.** Fix k, α≥0. Up to X, the number of centers possessing such a component and an index set S₀ with

    rank_Q(B_{*,S₀ᶜ}) < rank_Q B,       ∏_{i∈S₀}p_i ≤ X^α

is at most X^{α+o(1)}. In particular it suffices that the product of the ν+1 smallest labels be at most X^α, because their complement has fewer than k−ν columns.

Fix a small constant η>0. Enlarge S₀ to S by adjoining every label at most N^η; the product cost is at most X^{α+kη}. Put t=rank_Q B_{*,Sᶜ}. Pick t independent columns J there. Since t<rank_Q B, some column i in S extends J independently. In J followed by i, pick t+1 rows on which the square minor is nonzero. Take the signed t-minors of those rows on J, deleting one row at a time, with the cofactor signs for expansion by column i. Their linear combination of the selected rows of B is a vector u in its integral row lattice. It is zero on J and therefore on every column of Sᶜ (the same column dependence on J restricts to the chosen rows). On i it is precisely the nonzero minor. When t=0 this just takes one nonzero row with weight one.

Every entry on J has absolute value ≤1+1/η since p_j>N^η and p_j^{A_{ij}}≤N. Thus the signed weights are bounded by a constant depending only on k,η, **not** on the small labels. In particular

    |u_j| ≤ C(k,η)(1+ log X/log p_j)       (j∈S).

The exact factorization of each row gives ∏p_j^{B_{ij}}≡−1 (mod N), with denominators invertible. Consequently N divides the nonzero integer

    W = ∏_{j∈S, u_j>0}p_j^{2u_j} − ∏_{j∈S, u_j<0}p_j^{−2u_j}.

The squaring removes the sign. Prime factorization and u≠0 ensure W≠0, and the bounds just proved give |W|≤X^{O_{k,η}(1)}. The ordinary divisor bound gives X^{o(1)} possible positive N per W, uniformly for fixed k,η. One proof of this weak divisor bound: for every ε>0, on sufficiently large primes p each factor a+1≤2^a≤p^{εa}; for each remaining prime bound (a+1)/p^{εa} by its fixed finite supremum.

To count the W, choose S,S₀ in finitely many ways. Ordered tuples of d=|S| positive integers with product ≤Y=X^{α+kη} are at most Y(1+log Y)^{d−1}, by summing the reciprocal products of the first d−1 entries. This overcounts the possible distinct primes, including their order. There are O_{k,η}((1+log X)^k) coefficient-tuples u per tuple of labels. Thus the number of centers is ≤X^{α+kη+o(1)} for each fixed η. Taking an arbitrarily small fixed η before X tends to infinity proves the lemma.

**Application.** The number of even N≤X with a five-label EAC of *any* signature is at most X^{3/4+o(1)}. Components with det B≠0 or det A≠0 already satisfy the stronger X^{1/2+o(1)} estimates from [order divisors](EACNonsingularSquareRoot.md) and the [Jacobian bound](EACJacobianSquareRoot.md). Suppose both vanish. Eigenvalue 1 is simple algebraically: if it occurred twice, the five eigenvalues, counting multiplicity, would be 0,1,1,ρ,−ρ−2 by trace zero, impossible since ρ≥2 is the Perron spectral radius (all row sums ≥2). Hence ν=1. Write the smallest labels as m₁<m₂. The complementary row of m₁ contains no m₁, and is composite, so m₂²≤N−m₁<N.

The [five-vertex heavy-row theorem](EACFiveDoubleSingular.md) gives at least two different rows with Ω(N−p_i)≥3. They cannot both be pure powers of m₁: different powers have ratio at least m₁≥3, whereas all complementary rows lie in [2N/3,N) (every label divides an odd composite row, so is <N/3). Thus one heavy row uses a factor ≥m₂ as well as at least two other factors ≥m₁, counting multiplicities. It gives m₁²m₂<N. Now (m₁m₂)²<Nm₂<N^{3/2}, and the lemma applies to the first two labels. Nothing here says that every Goldbach exception has a five-label EAC, or that any such EAC is itself forbidden.

The count is of actual factor-closed components at all centers, distinct from July–August [missing-representation estimates](https://arxiv.org/abs/2607.27282) and the August [terminal exponent-matrix claims](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460), whose full text remained unavailable. See the linked earlier notes for the underlying graph definition and literal support bounds.
