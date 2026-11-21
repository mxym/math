# Six-label autonomous prime-factor components with at most three factors: an exact rank obstruction and a fixed-seed orbit consequence

Let N be even. A [Bożek exceptional autonomous component](https://arxiv.org/abs/1909.09900) is represented here by distinct odd prime labels coprime to N, with every N−x composite, all of its prime divisors again labels, and the directed arcs x→y for y|N−x strongly connected. Write A_xy=v_y(N−x), B=I−A, and Ω for the number of prime factors *with multiplicity*.

**Finite rank theorem (all heights).** If there are exactly six labels and all Ω(N−x)≤3, it is impossible that both det A=0 and dim ker_Q B≥2. This includes all numbers of pair and triple rows, including either homogeneous endpoint. It does not rule out singular A alone, corank two alone, or all six-label components.

**Fixed-seed consequence.** Fix an odd prime p, a finite set F of rational primes and ε>0. For all sufficiently large even N coprime to p with N_F=∏_{ℓ∈F}ℓ^{v_ℓ(N)}≥N^{1/2+ε}, follow every prime factor of N−x iteratively from p. If the whole orbit consists of composite-complement rows, then it has **at least seven labels, or exactly six and some row has Ω(N−x)≥4**. In fact, for every fixed D, any such six-orbit with Ω≤D throughout must itself be strongly connected, with det A=0 and dim ker_Q B=2. The last assertion does not exclude singular charts of arity ≥4. No smoothness restriction is placed on the complementary factor N/N_F. Neither the existence of a Goldbach representation nor the disappearance of large orbits follows. In the narrower fixed-F-smooth setting an [earlier theorem](PrimeOrbitSixSmoothExclusion.md) already rules out every six-orbit.

## Exhaustive combinatorial certificate for the rank theorem

Index the six primes 0,…,5 in increasing order. The following necessary conditions use no model of their approximate sizes.

* Row i is a multiset of two or three indices other than i: the self-factor would divide N, contrary to coprimality. Thus there are 15+35=50 choices per row. All six indices occur as outputs, since the support is strongly connected.
* For i<j with rows of the same arity, the product of row i is *larger* than that of row j. Discard when its sorted list of factor indices is componentwise ≤ the other one. Equality also fails. We need not test rows of different arities.
* For each output h, at most one *distinct* input smaller than h contains it, because such a prime input is the unique least nonnegative residue of N modulo the prime with index h. Repetitions in the same row constitute only one input.
* Test strong connectivity on the oriented support. Use the following extra spectral filter **only** in seeking the joint condition det A=0, dim ker B≥2. The Perron root ρ is at least 2 and is strictly greater than 2 if any row sum is 3 (left positive Perron vector times A1). Among the eigenvalues, with algebraic multiplicity, are 0,1,1,ρ. If the other two are λ,μ, their sum is −(2+ρ) since A has zero diagonal. Their product is real and ≤ρ², whether both are real or they are a conjugate pair. Thus tr(A²)=2+ρ²+(2+ρ)²−2λμ≥4ρ+6. The integer R=∑_{i<j}A_ij A_ji=tr(A²)/2 must be ≥7 for all pairs and ≥8 as soon as one triple occurs. The latter weak bound is fine also for all triples.

The [ascending verifier](check_eac_six_rank_forward.cpp) independently chooses each row in sorted-index order, enforces the two pairwise conditions as soon as both inputs are assigned, and checks all labels used, then connectivity and the necessary trace bound. The counts below are before imposing anything about actual prime values. The penultimate column requires rank B≤4 by all 36 integer 5×5 minors; the last requires det A=0 in addition.

| Triple rows | All used, pairwise tests | Strongly connected | Trace screen | Rank B≤4 | Both |
|---:|---:|---:|---:|---:|---:|
| 0 | 3037 | 2047 | 0 | 0 | 0 |
| 1 | 166996 | 129335 | 211 | 0 | 0 |
| 2 | 2011222 | 1641112 | 23250 | 0 | 0 |
| 3 | 7908149 | 6725296 | 264878 | 12 | 0 |
| 4 | 11468392 | 9917641 | 870319 | 39 | 0 |
| 5 | 4799513 | 4241509 | 672671 | 17 | 0 |
| 6 | 362583 | 320515 | 86337 | 8 | 0 |
| Total | 26719892 | 22977455 | 1917666 | 76 | 0 |

The [reverse verifier](check_eac_six_rank_reverse.cpp) instead enumerates each base-four row encoding in [0,4095], retaining precisely the permitted exponent vectors. It selects inputs in *decreasing* order; incompatibility across same-arity rows is detected using count prefixes (the sorted earlier factors are componentwise ≤ later factors iff all earlier prefix counts are ≥ the later ones). Both smaller inputs to a common larger target are forbidden by bit masks. Incremental Gaussian elimination over F_101 discards a prefix only when its rank is ≥5; then some integer minor is nonzero as well. At a complete low-modular-rank chart test connectivity by forward and reverse searches, the trace bound, all exact rank minors, and det A by signed permutation sums. There were exactly 76 modular candidates and no false positives. Every surviving row tuple and signed determinant agrees with the first implementation. The determinant histogram is −18:1, −12:25, −10:2, −9:17, −8:16, −7:8, −6:7. In particular all 68 mixed tuples and 8 all-triple tuples fail the joint condition.

The forward verifier's fraction-free elimination has exact divisions (Bareiss with row pivots). Minors through order 5 are at most 10^(5/2) in absolute value by Hadamard (squared row norms ≤10); multiplying and subtracting two minors safely fits the signed 64-bit intermediate. The reverse signed permutation sums have even the crude bound 6!·3⁶<525000. The finite exercise is purely over integers. Neither search identifies graphs up to a label permutation or uses a weight tier.

**Replay** from this directory, using any C++17 compiler and POSIX shell:

```sh
g++ -std=c++17 -O3 check_eac_six_rank_forward.cpp -o /tmp/six-forward
g++ -std=c++17 -O3 check_eac_six_rank_reverse.cpp -o /tmp/six-reverse
/tmp/six-forward > /tmp/six-forward.txt && /tmp/six-reverse > /tmp/six-reverse.txt
cmp /tmp/six-forward.txt eac_six_arity_ledger.txt
grep '^chart ' /tmp/six-forward.txt > /tmp/six-1.txt
grep '^chart ' /tmp/six-reverse.txt > /tmp/six-2.txt
cmp /tmp/six-1.txt /tmp/six-2.txt
```

Each chart line gives its six rows as base-four integers (column 0 most significant), then its exact signed det A. See the [complete 76-chart ledger](eac_six_arity_ledger.txt).

## From the finite obstruction to actual prime orbits at F-rich centers

Suppose contrary to the fixed-D structural assertion that there is an unbounded sequence of six-label all-composite forward orbits with every Ω≤D that are either nonterminal or have invertible A. Fix each finite choice of component shape and exponent chart on a subsequence. Every label reached is coprime to N, by induction from the seed. The [moving-seed theorem](PrimeOrbitMovingSeed.md) proves rank-nullity ν=dim ker B≥2 under this F-rich assumption, and its upward-forest feedback bound gives ν≤floor(6/2)−1=2. It rules out orbits with fewer than six labels for all sufficiently large N.

**Nonterminal case.** The [six-label fork](PrimeOrbitSixLabelFork.md), with exactly this F-rich hypothesis, leaves only a two-label source cycle containing p feeding one four-label terminal component. Its own terminal exponent matrix M is nonsingular, and its two least labels r,s both tend to infinity but satisfy log r,log s=o(log N). Every terminal label divides an odd composite internal complement and is at most (N−3)/3. Writing x for its four labels, we have
     
    M log x = (log N)1 + (log(1−x_i/N))_i.

The correction is uniformly bounded. All entries of this **terminal block** M are ≤D, so we fixed a single invertible M on the sequence. Each component of log x is w_i log N+O_M(1) with w=M^{-1}1. Vanishing logarithmic weights for r and s give log r,log s=O_M(1), contrary to divergence. No invertibility of the entire reducible matrix was used.

**Terminal case with invertible A.** Now the same argument over the fixed six-by-six A gives log x=w log N+O_A(1), w=A^{-1}1. Thus w_p=0, and any second weight-zero label is bounded. Fixing its prime value along a subsequence would give a six-label joint orbit for *two* prescribed seeds, contrary to the [multi-seed theorem](PrimeOrbitMultiSeedMinimal.md) (at least seven). Strong connectivity guarantees the same full orbit from those seeds. Hence the five nonseed primes all have positive weights, bounded below by a common positive δ on this subsequence.

Invoke the [at-most-one-high lemma](PrimeOrbitSixTerminalFiveMacroscopic.md), **only its geometric first section**: it uses strong connectivity, ν=2, compositeness and the five positive lower weights, not smoothness of N. Thus at most one weight equals 1. If none do, the correcting vector above tends to zero, so its p-coordinate after multiplication by A^{-1} gives log p→0, impossible. If y is the unique weight-one label, it occurs in a row with a different input x, necessarily of weight <1. It occurs just once; all remaining factors have weight zero, so N−x=p^a y with a≥1 fixed on the exponent chart. This gives y/N→p^{−a}. All other corrections tend to zero. The p-coordinate of the exact inverted equations now yields
     
    log p = (A^{-1})_{p,y} log(1−p^{−a}).

The coefficient is rational. Clearing its denominator and taking a prime valuation at any divisor of p^a−1>1 (coprime to p) makes its numerator vanish, contradiction. This rules out all six-terminal invertible fixed-arity charts on such a sequence, with no assumption N is F-smooth.

We have proved the fixed-D structural assertion by the subsequence criterion. For D=3 apply the unconditional finite rank theorem to the remaining six-terminal possibility det A=0, ν=2: none exists. Taking the contrapositive gives the claimed orbit-size/row-multiplicity alternative. No upper bound on the arities in a general prime closure is assumed.

## Comparison

See [Bożek's original graph framework](https://arxiv.org/abs/1909.09900), the distinct repository results on [all-semiprime](EACSemiprimeQuarter.md), [all-triple](EACSixTripleQuarter.md), and [invertible exponent matrices](EACInvertibleQuarter.md), and the earlier [size-six exclusion at fully smooth centers](PrimeOrbitSixSmoothExclusion.md). [Kelanemer, SSRN 7274460, August–September 2026](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) also works with terminal exponent matrices; only its indexed abstract was accessible, so we make no comprehensive nonoverlap or priority claim. The November [almost-prime sieve](https://aixiv.science/pdf/aixiv.261111.000001v1.0.pdf) instead concerns additive representations. None of these comparisons turns the restriction on a small orbit into a restriction on the size or arity of every possible orbit.
