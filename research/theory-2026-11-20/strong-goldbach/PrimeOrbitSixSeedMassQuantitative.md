# A quantitative seed-power bound at arbitrary centers with five polynomial-size moving labels

Fix p an odd prime, a finite prime set F and δ>0. For a six-label strongly connected all-composite factor component at even N coprime to p, with p one label and the other five all ≥N^δ, put

    L=log N,    H=1+log(N/N_F),    J=1+log max(1,L/H).

There is a constant depending only on the fixed data such that the largest p-adic exponent in any of the six rows is at most

    C H J⁴.

No bounded row-arity hypothesis and no smoothness assumption are made. The bound is useful when N_F is large: if N/N_F≤(log N)^A with fixed A it gives O((1+log log N)^5) for the largest exponent, hence also for total row arity since the nonseed exponents are bounded. This is a bound on exponents, not on p to those powers, nor an exclusion for every unbounded exponent or a Goldbach representation. We make no effective numerical claim for C.

We use [the subpower mass theorem and its at-most-three-cold algebraic obstruction](PrimeOrbitSixSubpowerSeedMass.md). If the present statement failed, there would be an unbounded sequence on which the ratio of the largest exponent to HJ⁴ tends to infinity. Since every exponent is O_p(L), necessarily H/L→0. The linked theorem applies on this sequence: a_max=o(L), col A′=col A, and col B′=col B with B=I−A (the prime columns omit the seed). Pass to a subsequence with the five bounded columns A′ fixed. Order the five nonseed p-exponents decreasingly as a_(1)≥…≥a_(5)≥0, with a_(6)=0; these are the seed column entries on nonseed *inputs*. The seed input itself has p-exponent zero.

For every j=2,3,4,5 replace the j largest-exponent input labels by the variable T. This leaves at most three cold variables, even if there are ties. The linked algebraic impossibility works for *each* choice of the collapsed rows: its algebraic proof uses the actual arities ≥2 and strong connectivity, not that the collapsed exponents were positive on the L-scale. The Nullstellensatz and determinant construction now gives a nonzero P(T) in Z[T] of bounded degree with
    
    log max(2, ||P||∞) ≪ 1+a_(j+1),        v_p(P(N)) ≥ a_(j).

The constants are uniform across the finitely many projected charts and cuts. If a_(j)=0 there is nothing to show. Since a_(j+1)=o(L), P(N)≠0 by dominance of its highest power. A constant P yields a_(j)≪1+a_(j+1) immediately.

Otherwise factor P(T)=b∏_i(T−β_i) in an algebraic closure of Q_p, retaining multiplicities, and normalize v_p(p)=1. The number of factors and each [Q(β_i):Q] are bounded. The standard Mahler measure bound M(P)≤||P||₂, together with factorization into primitive integer irreducibles, gives h(β_i)≤log M(P)≪1+a_(j+1) for absolute logarithmic height (also if P has content). The contribution v_p(b) is O(1+a_(j+1)); a zero root contributes 0 and nonunits with nonpositive difference-valuation cannot increase the bound. For each root β with v_p(N−β)>0 we have v_p(β)=0 and β≠N. Write V=N/N_F and combine the two moving factors into the single designated last base γ=V/β, so

    v_p(N−β)=v_p(N_F γ−1),       1≤h*(γ)=max(1,h(γ))≪H+a_(j+1).

Use the prime bases dividing N_F, with their positive exponents, and last base γ with exponent 1. For large terms at least one such fixed prime occurs since N_F=N^{1−o(1)}; pass to a fixed subset of F. The exponent maximum B (with 3 adjoined) is ≍L. The number of bases is ≥2; if γ=1 one may instead bound the expression with a redundant base 1 by the same statement (or use a fixed-base log estimate; in the single prime-base case use LTE after raising to p−1). The product N_F γ is not 1. Apply [Bugeaud, *B′*, Theorem 1.3, pp. 4–5, (1.8)–(1.9)](https://arxiv.org/pdf/2209.00275), a formulation of [Yu's p-adic logarithm estimates](https://doi.org/10.1515/FORUM.2007.009). Its constants depend only on the field degree in addition to the displayed local prime, number of bases and heights, so the varying β-fields of bounded degree are allowed. The last exponent 1 has minimal p-adic valuation and we can take B_n=1. The alternative (1.8) would imply B≪h*(γ)=o(L) since all earlier base heights are fixed, impossible. Therefore (1.9) gives
    
    v_p(N−β) ≪ h*(γ) log max(3, B/h*(γ)).

The implicit constants are uniform. For h≤C U=o(L), the right side is O(U(1+log(L/U))) by monotonicity of t log(eL/t) up to t=L, with harmless absolute constants. Summing over the bounded number of roots and including the leading coefficient yields, with U=H+a_(j+1),

    a_(j) ≪ U [1+log(L/U)] ≤ (constant) (H+a_(j+1)) J.

Starting at a_(6)=0, four steps give a_(2)≪HJ⁴.

To bound the largest entry, let h index it. In the linked five-by-five spectral argument e_h cannot belong simultaneously to col A′ and col B′. Thus at least one of these two *fixed* spaces admits a rational left annihilator d with d_h≠0. In the first case d·a=0 since a∈col A′; in the second d·a=d·e₀ since e₀−a∈col B′. Either equality gives a_(1)≪1+a_(2). Because only finitely many A′ and h are possible, this costs a uniform constant. We contradict the postulated unbounded ratio and obtain the stated bound after absorbing finite small heights.

This is a quantitative refinement within the [prior Bożek prime-factor component framework](https://arxiv.org/abs/1909.09900). See the linked subpower proof for comparison to Kelanemer's nearby 2026 structural programme and its public abstract.
