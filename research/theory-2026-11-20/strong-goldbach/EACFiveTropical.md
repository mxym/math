# A two-thirds product gate in the doubly singular five-label branch

For an actual [Bożek EAC](https://arxiv.org/abs/1909.09900) with five labels, write m₁<m₂ for its two smallest primes, A for its complementary factor-exponent matrix and B=I−A. If det A=det B=0, then, for each fixed δ>0, all sufficiently large centers N of such components satisfy

    m₁m₂ < N^{2/3+δ}.

Consequently the number of even N≤X having **any** five-label EAC is at most X^{2/3+o(1)}. This does not assert that the five-label branch is empty, that every Goldbach counterexample needs such a component, or an upper bound on Goldbach exceptions by this argument.

### Finite chart reduction in the hypothetical large-product branch

Suppose for some fixed δ>0 there are unbounded centers with m₁m₂≥N^{2/3+δ}. Put P=m₁ and name the other labels arbitrarily. All rows have total exponent at least 2. There is no self-loop, and in the P row every factor is ≥m₂. Hence m₂<√N and P>N^{1/6+δ}. Any product of six factors from these primes exceeds N; every row therefore has total exponent ≤5. Also m₂>N^{1/3} (because m₂≥P), and Pm₂²>N. A row not containing P can only be a product of two nonminimal primes, with repetition allowed. A row containing P can only be P^e (2≤e≤5) or P^e Q (Q nonminimal, 1≤e≤4). For the P row this gives the 10 unordered pairs on four labels. For each other row exclude its input as a possible factor: there are six unordered pairs on three nonminimal labels, four admissible pure powers, and 4·3 mixed products. This gives exactly 10·22⁴ labeled charts, before tests.

Keep only pairwise distinct rows (N−p_i distinct), strongly connected support, det A=det B=0, at least two rows of total ≥3 and two disjoint mutual edges; the last two conditions are the [heavy-row theorem](EACFiveDoubleSingular.md). Relabeling the four nonminimal vertices permutes rows and columns **simultaneously** and preserves every hypothesis. Taking the lexicographically smallest row-major chart per such orbit leaves 45. The first checker regenerates all charts and computes both determinants by the signed permutation formula; the largest absolute monomial in either determinant is ≤5⁵.

### Exact limiting certificate

Pass to a single chart on an unbounded subsequence (there are finitely many), and pass to a convergent subsequence of its five log-label vectors w_j=log(p_j)/log N in [0,1]⁵. Each label divides another composite row, and so is below N/3. Since log(N−p_i)/log N tends to 1 uniformly, the limit satisfies Aw=1. With index 0 for P, it must obey

    1/6 < w₀ ≤ 1/3,     w₀ ≤ w_j ≤ 1,
    w₀+w_j > 2/3 for every j>0.

The first strict inequality and the last strict inequalities hold even at the limit by the fixed margin δ. The upper bound 1/3 uses at least one row of total ≥3 with all weights at least w₀.

The second checker performs rational row reduction of Aw=1, checking both the particular solution and null direction directly whenever consistent. All 45 systems have rank 4. Of them 40 are inconsistent. For the remaining affine lines write w_j=a_j+b_j t with t one free coordinate in [0,1]. Intersect the closed half-intervals cut out by the displayed inequalities with strictness relaxed. Two of the five intersections are empty. On two more charts strictness fails everywhere: testing the midpoint of a closed interval suffices, since a nonnegative affine function vanishing there vanishes on the interval. The two boundary-only row-major codes are 0001100101020003010030010 and 0000200011000203010031000. This does not claim that either boundary chart occurs.

The only strictly feasible chart is

    00002
    00011
    00020
    20100
    21000

on coordinates P,Q,R,D,E, respectively. Its rows at Q and R give Q+DE=R+D², hence R−Q=D(E−D). Its rows at D and E give D+P²R=E+P²Q, hence E−D=P²(R−Q). Since D,E are distinct and P²D>1 these equations contradict each other at every height. This rules out the chosen subsequence. The argument is uniform over all realizations and all matrices at each fixed δ; it does not assume a numerical cutoff for the finitely many possible small exceptions.

In the doubly singular branch B has corank one by the trace/Perron argument in [the supported-minor lemma](EACSupportedMinorFive.md). For any fixed δ that lemma therefore gives at most X^{2/3+δ+o(1)} eligible centers, together with a bounded set depending on δ. Components with either matrix nonsingular already satisfy the square-root bounds linked there. Letting δ be arbitrarily small gives the announced exponent.

### Replay

Run these commands from this directory:

    c++ -O2 -std=c++17 check_eac_five_tropical.cpp -o /tmp/eac-five-tropical
    /tmp/eac-five-tropical > /tmp/eac-five-rows.txt
    python3 -O check_eac_five_tropical.py < /tmp/eac-five-rows.txt

The stage counts are 2,342,560 raw, 45 canonical, then 40 inconsistent, 2 empty intervals, 2 boundary-only and 1 strict chart, eliminated by the two integer identities above. The programs depend only on the C++ standard library and Python's exact Fraction.

See the [previous note's scope](EACSupportedMinorFive.md), including related 2026 exponent-matrix work, which is not assumed here. The exponent (2/3) concerns actual centers with a five-label factorization component, not the exceptional set of the binary Goldbach conjecture.
