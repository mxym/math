# A six-label single-seed orbit: the nonterminal branch requires a macroscopic partner

Fix an odd prime p, finite prime set S and ε>0. Consider unbounded even N, coprime to p, with N_S≥N^{1/2+ε}. Start from p and iteratively adjoin every prime factor of N−x for reached inputs x. Suppose all reached rows are composite, coprime to N, and the resulting orbit has exactly six labels. These are necessary assumptions at a hypothetical Goldbach failure with such a closure size, not a statement that the size is always six.

For all sufficiently large such N, either the whole orbit is one strongly connected exceptional autonomous component (EAC), or **p belongs to a two-label source cycle feeding one four-label terminal EAC**, with multiplicity one on both internal source arcs. In the latter case the other source label q satisfies q≥N^η for some η>0 depending on the fixed data. Of the four terminal labels r₁<r₂<r₃<r₄, the two smaller ones grow to infinity but are N^{o(1)}, whereas the two larger ones are ≥N^η (reduce η as needed). All six labels are o(N) in the nonterminal case. In particular the configurations with a bounded or subpower upstream partner, or with three macroscopic labels in the four-label terminal component, cannot persist. This is **not** an exclusion of the remaining nonterminal case or of the six-label terminal case.

## The extremal graph decomposition

Let A record exponents in prime complements and B=I−A. By [moving-seed independence](PrimeOrbitMovingSeed.md) and the upward-forest feedback upper bound there, ν=nullity B=2. To track this extremal case, partition the graph into strongly connected components D. The full rational nullity is ≤Σ_D ν_D for the diagonal blocks I−A_D, by block triangularity (or solving the kernel equations block by block). An acyclic singleton has ν_D=0. For cyclic D of size j, a feedback set F_D exists of size ≤⌊j/2⌋ by the upward-edge forest construction restricted to D. First-return elimination on the internal matrix gives ν_D≤|F_D|, with equality only when the internal first-return matrix is the identity. That first-return matrix is irreducible: directed paths in D between members of F_D split at each first visit to F_D. Consequently equality requires |F_D|=1. In that case there is exactly one weighted first-return walk, with weight one. Each internal arc in an SCC lies on some return walk to its chosen vertex; by decomposing into first returns, the sole walk uses each such arc. The complement is acyclic, so the walk is simple except for its repeated endpoint. Thus D is a simple directed cycle with unit internal multiplicities. Equivalently, an irreducible integer matrix of spectral radius one is a unit-weight permutation cycle.

Every terminal SCC has ν_D≤⌊j/2⌋−1 since its internal row sums are ≥2; no singleton can be terminal. Since the total ν=2 is only one below the trivial six-vertex bound 3, there must be exactly one terminal SCC, every SCC size must be even, there is no acyclic singleton, and every nonterminal SCC attains its full half-size bound. Thus every nonterminal SCC is precisely a unit-weight 2-cycle. [Bożek, Theorem 3.7](https://arxiv.org/abs/1909.09900) gives 2200 as the only center for an all-composite two-label terminal EAC. It is irrelevant at sufficiently large N. The only nonterminal option is now 2+4. The forward single seed p must be in the source, and its terminal component has ν_D=1. For q the other source label, write
     
    N−p=q U,        N−q=p V.

U,V are nonunit integers entirely factored over the terminal labels, since both rows are composite, the two internal arcs have multiplicity one, and loops are impossible.

## No third macroscopic label at the terminal

Let r=r₁. Uniformly along any such unbounded sequence, r→∞. Otherwise after taking a subsequence a fixed prime lies in the size-four terminal component, and moving-seed independence there forces nullity at least two, impossible by its feedback bound. Since every terminal label occurs in a composite row internal to the component, each is ≤N/r (after removing one occurrence, a factor ≥r remains). Also q≤N/r since U≥r. Hence all terminal log-complements and log(N−q) equal L+O(1/r) with L=log N.

The four-by-four terminal exponent matrix M is nonsingular. Otherwise M would have eigenvalues 0 and 1, and also its Perron spectral radius ρ≥2. Its diagonal is zero, forcing its remaining eigenvalue to be −(ρ+1), an impossibility. This uses both size four and ν_D=1.

Suppose three terminal labels exceed N^δ along an infinite sequence, for some fixed δ>0. Put T=L/log r. All columns of M other than possibly the r-column have entries bounded only in terms of δ, since the corresponding factors have size ≥N^δ. The r-column has entries O(T). Exactly the same entry bounds apply to the vector v of exponents of V=(N−q)/p. Denote D=|det M|; expansion gives D=O_δ(T). For z=(log r₁,…,log r₄)ᵀ we have Mz=L1+e, with each |e_i|=O(1/r).

The cofactor formula for the coordinate log r omits its potentially large column in every cofactor. Thus D log r = mL+O_δ(1/r), with m an integer bounded in terms of δ. Because D≥1 and r→∞, necessarily m≥1; in particular D≥c_δ T for large N. The coefficients of vᵀ M^{-1} are ratios of row-replacement determinants to det M: in every numerator only the *one same column* can be O(T), hence all these ratios are O_δ(T/D)=O_δ(1). Now log p=log(N−q)−vᵀz gives
     
    log p = (j/D)L + O_δ(1/r),      j∈ℤ.

Since D=O_δ(T)=o(L), a nonzero j is impossible for fixed p; but j=0 would give log p→0. This rules out three terminal labels ≥N^δ on any unbounded sequence.

## Conclude which of the labels grow polynomially

The [macroscopic rank theorem](PrimeOrbitMacroscopicRank.md) yields fixed positive exponents for at least ν+1=3 labels of the six-orbit and at least ν_D+1=2 inside the four-orbit. Adjust the exponents by taking a smaller common threshold. Because the source label p is fixed, the partner q must be among the three macroscopic labels for all sufficiently large N: otherwise three would be in the terminal, just ruled out. For every fixed δ>0 at most two terminal labels exceed N^δ eventually, proving r₁,r₂=N^{o(1)} along every such sequence. All lower and upper claims follow. No restriction on the individual exponents in the two subpower columns was imposed.

**Comparison checked through November 21, 2026.** [Kelanemer, August 12, revised September 6](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) describes a nearby terminal exponent-matrix reduction in the accessible abstract. This note treats a six-label forward orbit of a fixed seed at an S-rich center, including the nonterminal source. The full Kelanemer text was unavailable on this check, so no priority or comprehensive nonoverlap claim is made. The [two-retained-prime result](EACTwoRetained.md) gives a different sparseness condition and does not imply the cofactor argument here.
