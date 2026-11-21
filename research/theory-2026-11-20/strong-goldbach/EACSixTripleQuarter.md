# A quarter-power minimum for every large homogeneous-triple six-label component

Suppose a six-label [exceptional autonomous component](https://arxiv.org/abs/1909.09900) has prime labels p=x₀<x₁<⋯<x₅=M at an even center N. Its prime-factor graph is strongly connected; all labels are odd primes coprime to N and each N−x_i factors entirely in the component. Assume each row contains exactly three prime factors, counting repetitions. Then for all sufficiently large N,

    M ≥ 2p²,                p < (N/2)^(1/4).

This is a pointwise necessary condition without a smoothness, determinant or fixed-seed hypothesis. It does not prohibit all homogeneous-triple components, and does not apply unchanged to components mixing two- and three-factor rows. See separately the [semiprime-only result](EACSemiprimeQuarter.md). The proof uses the actual order of the prime factors and two limiting moment identities, not distribution heuristics for primes.

## 1. The complete antichain

Assume M<2p². Write each complementary product as a weakly increasing triple of factor indices. Two *different* comparable index triples would have products differing by at least 2p²: change one strict index, increasing one odd prime by at least 2 while the other two factors are ≥p, and no other change decreases the product. Yet the products differ exactly by the difference of the two input labels, of magnitude <M. Identical triples are impossible because their row inputs would coincide. The six unordered output triples therefore form an antichain in the componentwise order on the 56 weakly increasing length-three tuples from {0,…,5}.

The [exact checker](check_eac_six_triples.py) lists all 16 six-element antichains. Its recursion chooses each next tuple in the fixed lexicographic order and retains every later incomparable candidate, discarding a prefix only if too few candidates are left. For each of 16×6! input assignments: discard loops because x_i∤N−x_i; then retain assignments in which each factor x_j has at most one *distinct* parent x_i<x_j. This follows since every such parent equals the unique least nonnegative residue N mod x_j. Repetitions of a factor within a row count as one parent, not two. Test strong connectivity by forward and reverse reachability. In the replay 766 assignments are loopless; 14 pass the parent test, and all 14 are strongly connected. No order on incomparable products was assumed.

Let A_ij count occurrences of label j in row i. The checker verifies by rational Gaussian elimination that each remaining A has rank five; its right kernel is spanned by a vector v with strictly increasing coordinates, normalized so v₁−v₀=1. The integer offsets w_i=v_i−v₀ are either (0,1,2,3,4,6) in nine assignments or (0,1,2,3,4,5) in five. Take any nonzero integral vector c in the left kernel; since A1=3·1, Σc_i=0. For f(T)=Σ_i c_i T^{w_i}, the monic gcd of f(T) and f(T²) is T−1 in eleven assignments and T²−1 in three. The scaling of c does not affect the gcd. Thus the only common positive root in any chart is 1. As an additional independent necessary test within this enumeration, I−A is nonsingular in all 14; this is not needed for the moment proof.

## 2. Why the shape test rules out every chart

Suppose that one of the fixed matrices occurs along an unbounded sequence. Put L=log N and let x denote the vector of prime labels, using logarithms coordinatewise. Every label occurs in some composite row, so M≤N/3. The exact vector equation is

    A(log x−(L/3)1) = (log(1−x_i/N))_i.

Taking a fixed linear right inverse on im A gives a scalar parameter t with

    log x_i = L/3+t v_i+O_A(M/N).

Here the initial error is O_A(1); strict ordering of the labels and v₁−v₀=1 bound t below. It cannot tend to +∞ on a subsequence. In that case every consecutive ratio x_{i+1}/x_i tends to infinity. The exact left-kernel identity Σc_i log(1−x_i/N)=0 then has a single largest term in magnitude on the support of c, indexed by its largest i, which dominates the sum of all others: x_i/N ≤ −log(1−x_i/N) ≤ (3/2)x_i/N. This is impossible. Thus t remains bounded and all x_i are comparable to N^(1/3), with constants on the fixed sequence. The shape error above is now O_A(N^(−2/3)) (constant may depend on the bound for t).

Expand the exact left-kernel identity once: Σc_i x_i=O_A(M²/N)=o(1), so this integer vanishes exactly for large N. Expand again: after multiplying by N² the quadratic term is −(1/2)Σc_i x_i² and the remainder is O_A(M³/N). Hence Σc_i x_i²=O_A(M³/N)=O(1). Along a subsequence t→t₀, divide the two moment identities by N^(1/3) and N^(2/3), respectively. For T=exp(t₀) they imply f(T)=f(T²)=0 after removing the common nonzero factors T^{v₀}, T^{2v₀}. Therefore T=1.

Along this subsequence all ratios x_i/x_j tend to one. Eventually every two inputs differ by less than p, so a prime factor cannot be shared between two distinct rows: it would divide their nonzero difference and is at least p. Six nonempty disjoint row supports on six available labels are necessarily all singletons. This contradicts the enumerated charts; alternatively an all-singleton three-factor output matrix has rank six (three times a permutation), not five. We have ruled out an unbounded sequence with M<2p². Since some row contains M, its other two factors are ≥p, whence Mp²≤N−3<N. The two claimed inequalities follow.

Replay: `python -O check_eac_six_triples.py` (standard Python; the verifier never relies on removable assertions).

## Comparison

[Bożek](https://arxiv.org/abs/1909.09900) introduced the graph framework and classified two-label components. This proof concerns homogeneous triple rows at six labels, rather than the [semiprime-only pointwise obstruction](EACSemiprimeQuarter.md) or the [all-center sparse subset bound](EACSixAllCenters.md). [Kelanemer, SSRN 7274460](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) discusses closely related terminal exponent matrices in a 2026 preprint; its abstract was accessible but the full text was not, so no priority or exhaustive nonoverlap claim is made. The November [almost-prime sieve preprint](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) studies additive representations and does not enter this finite multiplicative-closure calculation.
