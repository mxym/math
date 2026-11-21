# Removing complementary primes while preserving finite-complexity counts

Checked mathematical note, 2026-11-21. This is a perturbation statement about a subset of actual primes, distinct from the random wheel model. It quantifies which prime statistics can survive an artificially missing even sum. It supplies no lower bound for a representation by the full set of primes.

## Statement

Let X tend to infinity, and let E be any set of even integers in [X,2X]. For each e in E delete the larger prime from every bona fide pair of primes summing to e, deleting the single prime in a diagonal representation. Let P_X be the remaining subset of the primes up to 2X. Write a(p)=log p on the original primes up to 2X and a_E(p)=log p on the remaining primes up to 2X. Both weights are zero at all other integers, including primes above 2X.

1. Every e in E is absent from P_X+P_X. No prime below X/2 was deleted, and all representation counts for targets at most X/2 are unchanged. For each 0<η<1 the number of deleted primes is O_η(|E| X/(log X)^(2−η)).
2. For every 0<η<1 and every even t≤2X outside E, the weighted ordered binary count changes by at most O_η(|E| X/(log X)^(1−η)), uniformly in t. For t≤X/2 the change is zero. Thus if |E|≤(log X)^(1−δ), any genuine off-target main term of size comparable to t is preserved up to o(t), for every fixed δ>0. An actual lower bound of that size, when available, still gives existence. No main term for all other binary targets is presumed.
3. Let ψ_1,…,ψ_k be integer affine-linear forms on Z^d with nonzero, pairwise nonproportional homogeneous parts. Fix d,k and a polynomial bound on their coefficients. Let B be an axis-parallel box of side scale H≥X^θ, with fixed θ>0. For any auxiliary weight F of absolute value at most 1,
   
       |Σ_{n∈B} F(n) (∏_i a(ψ_i(n)) − ∏_i a_E(ψ_i(n)))|
           ≪_{θ,η,d,k} |E| H^d/(log X)^(1−η).
   
   Constants may depend on the fixed polynomial exponent and box side comparability. The bound is uniform over all shifts, locations and forms meeting the stated hypotheses. One may impose arbitrary further cutoffs on n by including them in F.
4. If |E|≤(log X)^(1−δ) then for all sufficiently large X every odd t in [7,2X] is still a sum of three primes from P_X. Every established fixed finite-complexity prime asymptotic with error o(H^d) for the same range of prime values and boxes is preserved at that scale. In particular all fixed Gowers cube statistics of the actual-prime weight are preserved in main order.

For a genuine deletion one may take E={X} with X=2p and p prime, so the diagonal representation of X ensures the deletion is nonempty. The theorem does not assert a bound suited to all-log-saving Bombieri–Vinogradov tests after deletion. Nor does it guarantee previously valid binary sums with only a few representations remain covered.

## Elementary sieve estimate

Write L=log X. Suppose r fixed nonconstant integer affine-linear forms have the following property. Outside primes dividing a nonzero integer D of size X^O(1) and a fixed set of small primes, each zero hyperplane has density 1/p, and the union of the r zero sets has density ν_p = r/p + O_r(p^−2). Then, uniformly over boxes of side H≥X^θ, their simultaneous positivity and primality occur at most

       O_{r,d,θ,η}(H^d L^(−r+η))

times, provided the forms considered as prime values are bounded by O(X). The polynomial bound on D suffices for uniformity.

Here is a short Bonferroni proof avoiding any uniformity assumption on large sieve moduli. Put α=1−η/(2r), y=exp(L^α) and choose an even J=L^β+O(1) with 0<β<1−α. Omit all bad primes and fixed p≤2r. If any required prime value is at most y, freeze all other coordinates besides one with nonzero coefficient. There are O(y+1) possibilities in that coordinate, so such points number O_r((y+1)H^(d−1)). Otherwise every good prime ≤y avoids all the forms.

Expand this condition to even order J for an upper bound. For each squarefree modulus s supported on good primes, the CRT density of simultaneous bad residue conditions is ∏_{p|s}ν_p. A residue class in a box of side H has count equal to volume divided by s^d up to O_d((H/s)^(d−1)), since s≤Y=y^J=X^o(1)≪H. Summing over at most s^d residues and then over s≤Y gives total error O_d(H^(d−1)Y²). Prefix rounding a box gives the same estimate.

For the Euler product density the discrepancy between the even truncated sum and the full product is at most the next symmetric sum. It is bounded by (Σ_{p≤y}ν_p)^(J+1)/(J+1)!, which is O_A(L^−A) for every fixed A, since Σν_p=O_r(log L) and J grows as a power of L. Also

       ∏_{good p≤y}(1−ν_p) ≪_r (log y)^−r ∏_{p|D}(1−1/p)^−r.

This is Mertens and the summable O_r(p^−2) difference in logarithms. The omitted-prime factor is O_r((log L)^r): split the prime factorization of D at L, use Mertens below L, and bound the sum of reciprocal prime divisors above L by O(log|D|/(L log L)). The main term is consequently O(H^d L^(−r+η/2)(log L)^r), bounded as claimed. The error terms are smaller by a power of X. The same argument applies to an interval as d=1.

## Applications of the estimate

For the deletion count each removed prime p has a true prime counterpart e−p. For the two one-dimensional forms p, e−p the roots are distinct modulo all sufficiently large p' not dividing e. The estimate with r=2 gives the unweighted bound. Every e-pair had one of its endpoints deleted and the rule p≥e/2≥X/2 proves the exact statements about absence and the small interval.

For the off-target binary difference any lost pair contains a removed prime p. For some e∈E, all three of p, t−p and e−p are prime, with t≠e and t positive. Their three roots are distinct at good primes outside divisors of the nonzero integer et(e−t). Apply the one-dimensional estimate with r=3, multiply by O(L²), and sum over the marked choice and e. Count all ordered pairs, including diagonals, by the same upper bound. If a repeated form value is prime and exceeds y, the residue test remains necessary, so no exceptional equality of values requires a new term.

For the general form statement, telescope or simply majorize the nonnegative product difference by the sum over the deleted index i. For each i and e∈E consider the original k forms plus e−ψ_i, all required prime. Take D to be e times a product of a selected nonzero homogeneous coefficient from each form and one selected nonzero 2×2 minor for each pair of nonproportional homogeneous coefficient vectors. This product is nonzero and polynomially bounded. Each good prime sees r=k+1 affine hyperplanes of density 1/p. Distinct independent pairs intersect in density 1/p². The sole proportional pair ψ_i and e−ψ_i is disjoint because p does not divide e. The union estimate follows by the first two Bonferroni terms. For k=1 there are no minors and the proportional-pair calculation suffices. Multiply the resulting count by O(L^k) and sum over i and e; the bound follows.

For all odd t≥X/2 up to 2X the unperturbed weighted ternary count is ≫X² uniformly by the ternary asymptotic. One can use the finite-complexity theorem on ψ=(u,v,t−u−v) in the triangular region with all entries positive. The homogeneous parts are pairwise nonproportional. The local factors are 2 at the prime 2 for odd t and at odd primes are 1−1/(p−1)^2 when p divides t and 1+1/(p−1)^3 otherwise. Their product is bounded below uniformly. Choose η<δ to preserve positivity after deletion. Below X/2 use the unchanged prime set and Helfgott's exact theorem. If one uses a statement formulated with von Mangoldt weights, removing prime-power terms costs o(X²) here by fixing all but one coordinate in the form that takes a proper prime-power value. The same convention change is negligible for other fixed finite-complexity systems. Cube forms a+ω·h for distinct binary vectors ω have pairwise nonproportional coefficient vectors. Apply the form estimate to a box with appropriate bounded cutoffs, splitting into finitely many boxes if working modulo an ambient cyclic group of size comparable to X.

## Scope and comparisons

[Green–Tao, Linear equations in primes](https://annals.math.princeton.edu/2010/171-3/p08) and [Green–Tao–Ziegler, inverse Gowers theorem](https://annals.math.princeton.edu/2012/176-2/p11) supply the baseline fixed finite-complexity asymptotics. [Helfgott](https://arxiv.org/abs/1312.7748) supplies exact small odd coverage. [Matomäki, Shao, Tao and Teräväinen, small-scale pattern distribution](https://doi.org/10.1112/jlms.13001) supplies related baseline short-scale asymptotics in its stated ranges. The loss bound works for any power-sized box and makes no claim that its unperturbed asymptotic is available at every such scale.

Compare the project’s [isolated additive exception](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/IsolatedAdditiveException.md), which gives exact single-hole coverage and uniform model main terms away from it by allowing synthetic primes, and the [arithmetic parity witness](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/ArithmeticTwoWeightParityWitness.md), which preserves much sharper distribution in progressions in a composite-supported model. Here the points are genuine primes and every rank-fixed nondegenerate pattern is stable, so the obstruction applies to a different class of proposed deductions. The distinction is insufficient closure under tests for the entire prime set. Prime-specific identities or errors sensitive to this deletion may still force positivity. A bounded July–November 21, 2026 literature search did not identify an exact matching formulation. The underlying sieve ingredients are standard and no priority claim follows.

## Independent check and dated comparison

The original and thinned weights have identical support cutoff. Lost tuples were counted by the extra prime form, not by replacing actual shifted-prime distribution with independence. The nonzero determinant product, Chinese-remainder truncation, uniform omitted-prime factor and exact small-odd versus asymptotic large-odd split were checked independently. No all-log-saving distribution or exact binary coverage away from the designated targets is inferred.

The dedicated July–21 November search compared, in addition to the cited finite-complexity and ternary results, the [recent quaternary density paper](https://www.sciencedirect.com/science/article/abs/pii/S0022314X2600209X) and [the October local-structure preprint](https://www.preprints.org/manuscript/202610.3061), which estimate representations under different conditions. [The April 2026 inverse-Gowers revision](https://arxiv.org/abs/1009.3998v5) is a baseline, not a hypothesis for the elementary loss proof. Repository matches for earlier two-weight or wheel diagnostics are distinct; no exact duplicate was located, and the comparison establishes no global priority.
