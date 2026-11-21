# An all-height compact-core classification for Goldbach factorization graphs

Let N be even. Use the orientation p→q if q is a prime divisor of N−p, for primes p≤N−2. This reverses [Bożek, §§2–3, arXiv:1909.09900v1](https://arxiv.org/abs/1909.09900v1). A set is factor-closed when it contains every outgoing neighbor of every member. A nonempty strongly connected factor-closed set is a terminal SCC in our orientation. A **special component (EAC)** means Bożek's nontrivial, non-Goldbach autonomous component, not a counterexample to Goldbach. Such a component has at least two distinct primes, all odd and coprime to N, and every N−p on it is composite. Indeed q|N cannot divide N−p for p prime coprime to N; and if p divides N its only possible incoming neighbor is p itself. If a coprime row is prime, its two labels form a closed true Goldbach pair. A singleton closed row can occur at N=p+p^e and is not an EAC. In particular large N can have small trivial components: no result below denies this.

**Theorem.** Over *all even centers N, without an upper cutoff*, the only EACs all of whose labels are ≤53 are
- N=128, with labels 3,5,7,11,13,23,29,41;
- N=2200, with labels 3,13.

Both centers are Goldbach numbers: 128=19+109 and 2200=47+2153. Bożek already found these components in his search through 10^8; the point is exhaustiveness by *label bound* rather than by center bound. Bożek's Theorem 2.6 guarantees an EAC at a hypothetical missing N; it does not place its labels below 53. Theorem 3.7 of that paper already identifies the unique two-label EAC, at N=2200, via Scott's theorem.

**Two-row obstruction.** The *largest even* N permitting two distinct odd prime labels p<q≤53 for which both positive integers N−p,N−q are 53-smooth is **4,020,958,408,470**. Rows of value 1, if allowed by this auxiliary statement, cause no issue. Here 53-smooth means having no prime factor larger than 53. The maximizing witness is p=3,q=47, g=11, using 4+365541673493=365541673497. The equality N=3+11·365541673497 gives the center and N−47=11·365541673493. This is not an EAC claim.

Consequently at any larger even N, for a factor-closed set C consisting of odd rows p≤N−2 (no strong connectivity or nontriviality required), all but at most one p in C∩[3,53] have a prime factor >53 of N−p. Two different such small rows cannot use the same large factor, which would divide their difference of at most 50. These factors belong to C, giving
$$
 |C\cap[3,53]|\le 1+|C\cap(53,\infty)|.
$$
This applies to every hypothetical Goldbach exception since [Oliveira e Silva–Herzog–Pardi](https://doi.org/10.1090/S0025-5718-2013-02787-1) verified all even integers from 4 through 4·10^18.

### Exact normalization and catalogue premise

Put U=N−p, V=N−q, d=q−p, and g=gcd(U,V). Then g is odd, g|d, V/g+d/g=U/g, and the three entries are pairwise coprime. Their two sum entries can be sorted as a≤b; write c=U/g. The even summand h=d/g is identified uniquely by parity. The prime factors of d are ≤53. If U,V are both 53-smooth, we therefore have a primitive 53-smooth abc-triple, including the case when h is the **larger** summand. Conversely, for odd c and its even summand h in such a triple, any p<q≤53 with g=(q−p)/h an odd positive integer gives N=p+gc; both complements are then 53-smooth because g≤50. This is an exact bijective enumeration per prime pair, not a bound on how far to search for N.

The imported completeness result is von Känel–Matschke, [*Solving S-unit, Mordell, Thue, Thue–Mahler and Generalized Ramanujan–Nagell Equations via the Shimura–Taniyama Conjecture*, Memoirs AMS no. 1419 (2023), DOI 10.1090/memo/1419](https://doi.org/10.1090/memo/1419), [arXiv:1605.06079v1, §3.2.4 Algorithm 3.14 and §3.2.6](https://arxiv.org/abs/1605.06079v1), and the authors’ [public S-unit tables 1 and 2](https://bmatschke.github.io/solving-classical-diophantine-equations/). Table 1 lists all positive pairwise-coprime a≤b<c, a+b=c, supported on the first 16 primes (1,663,449 triples). Table 2 gives all such triples with rad(abc)≤10^7 (432,408). These are completeness results for that rational S-unit computation, not heuristic bounds on abc height or a use of the abc conjecture. Modularity for rational elliptic curves, historically called the Shimura–Taniyama conjecture in their title, is a theorem. The conditional Mordell–Weil-rank examples elsewhere on the data page are **not** either of these two S-unit tables. Our replay treats the authors' complete data as a published input; it checks authenticity and our reduction, not their original S-unit algorithm from scratch.

For the 53-smooth table, test every reconstructed center. There are 5,630 catalogue rows that can occur, giving 36,476 distinct even centers before any closure tests. For each center tabulate the complete factor lists of N−p by trial division by the 15 permitted odd primes. Keep only rows coprime to N with entirely permitted factors and total number of factors at least two (with multiplicity); delete recursively a row having some factor no longer present. An EAC in the permitted alphabet can never be lost. In the remaining graph, the reachable set R(p) is a closed SCC exactly when R(q)=R(p) for every q in R(p). The two components above are the complete result. A nonminimal closed union need not itself be strongly connected.

### A complementary radical condition

For the second public table the exact maximum of c/h with c odd and h the even summand is 162089505/4, attained at 4+162089501=162089505 (integer cross-products in the checker). Let C be an EAC at an exceptional center, R=∏_{r∈C}r, and p<q in C. If rad(R(q−p))≤10^7, the normalized triple just constructed has radical ≤10^7, hence
$$
 N=p+(q-p)c/h\le 10^7\bigl(1+162089505/4\bigr)<4\cdot10^{18}.
$$
Indeed R is squarefree and R≤rad(R(q−p)), so p,q≤10^7. This contradicts the verified range. Thus **rad(R(q−p))>10^7 for every such pair**. No lower bound on the radical of N itself is asserted. By Bożek's size-two theorem k=|C|≥3 at an exceptional center. For squarefree odd R with at least three prime divisors and R<91,869, direct enumeration always finds a prime pair p,q|R with rad(R(q−p))≤10^7. The first purely arithmetic survivor is R=91,869=3·113·271, minimum pair-radical 10,105,590. It is not declared realizable.

### Replay (standard Python only)

Download the unchanged, attributed source tables from the [authors' website](https://bmatschke.github.io/solving-classical-diophantine-equations/) using their table links, placing them in a data directory as follows. The inputs are not redistributed here.

```sh
base=https://bmatschke.github.io/solving-classical-diophantine-equations/s-unit-equation
curl -fL "$base/solutions_2_3_5_7_11_13_17_19_23_29_31_37_41_43_47_53.txt" -o abc53.original.txt
curl -fL "$base/solutions_uptoRadical_10000000.txt" -o abc1e7.original.txt
python3 check_eac_sunits.py .
```

- 53-smooth table: 84,566,541 bytes; SHA-256 `80f3cd4e2535285f9a5c5811d9646b60523f7caef6fb0506202af761a743da98`.
- Radical table: 15,689,091 bytes; SHA-256 `c28a87a2015c987d6665647117094cab4e9072a7d23301c5d89f892d3d2b2fb3`.

The script streams the raw bytes, checks digest, row counts and the abc identities/coprimality, then emits the exact extrema, complete SCC list, and radical-product bound. No numerical optimization or unverified solver is used. The source tables’ own header credits the authors and specifies CC BY-NC 3.0; only download instructions, checker and small numerical conclusions are supplied.

The structural restriction above is distinct from the analytic exceptional-set estimates in [Bhowmik–Grimmelt (2026)](https://doi.org/10.1007/s10476-026-00191-z) and [Althöfer–Chen–Perelli–Pintz, arXiv:2611.09386v1](https://arxiv.org/abs/2611.09386v1). It does not bound all exceptional centers or prove that potentially large components cannot occur.
