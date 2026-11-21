# A single bipartite cofactor component forces a quarter-power minimum

Fix k. Let an even N support a strongly connected [Bożek exceptional autonomous component](https://arxiv.org/abs/1909.09900) on k distinct odd primes, all coprime to N, and suppose every N−x has exactly two prime factors, with multiplicity, both in the component. Let H be the undirected cofactor graph: its edge uv, a loop if u=v, records the unique row N−x=uv. Put p=min labels and M=max labels.

**Theorem.** If H has exactly one bipartite connected component, then M≫_k N^(3/4), and hence p≪_k N^(1/4). Equivalently, on any such sequence with M=o(N^(3/4)) (in particular p/N^(1/4)→∞), there must eventually be at least two bipartite cofactor components, so the unsigned edge-incidence exponent matrix A has rational nullity at least two. This is a pointwise restriction on actual factor sets, not a Goldbach result.

**Six-label corollary.** Every all-semiprime six-label EAC satisfies p≪N^(1/4). For a six-label EAC at any sufficiently large N, whether semiprime-only or not, p≤N^(1/3): otherwise all its odd composite rows would necessarily be semiprime and the quarter-power bound would contradict p>N^(1/3). This strengthens the former large-minimum counting step in [the all-centers census](EACSixAllCenters.md).

## The star and a common range for the other primes

H has exactly k vertices and k distinct edges and no isolated vertices. Its component containing M is a star S with m≥2 vertices, m−1 edges and no loops, by the [all-height semiprime star lemma](EACSemiprimeStar.md). In fact its center s can be chosen to equal p: some product involving p is at most pM but at least N−M, while the edge sM gives (s−p)M≤(N−x)−(N−M)<M. Thus s=p. In the single-edge case use this choice of center. Also pM<N, and M²≥N−M.

It suffices to rule out a sequence with N→∞, M=o(N^(3/4)), and S the unique bipartite component. Denote by U all n=k−m vertices outside S. Each lies in a nonbipartite component. For an edge uv with row input x we have

    log(u/√N)+log(v/√N)=log(1−x/N)=O(M/N).

Within any nonbipartite component each vertex has an odd closed walk of length bounded in terms of k (take a path to an odd cycle and return; a loop is an odd cycle). Alternating the displayed equations along it bounds twice the starting log by O_k(M/N). Thus all vertices in U are √N+O_k(M/√N), regardless of their component.

Two different inputs in U cannot both give edges of S: the star center s divides their difference, yet the difference is O_k(M/√N)=o(s), since s≥(N−M)/M and M²=o(N^(3/2)). The leaves of S lie in an interval of width ≤M/s=O(M²/N), since the difference of their products with s is a difference of row inputs.

## Equal-sum reflection

Let T=⌊√N⌋. For any outside edge write u=T+i, v=T+j for integers i,j=O_k(1+M/√N). Consider two distinct outside edges associated to two inputs **both in U**, or to two inputs **both leaves of S**. Subtract their reflected products. The input difference is O_k(1+M/√N+M²/N), and the difference of the two products of offsets ij is also O_k(1+M²/N). Consequently the absolute value of T times the difference of the two integer offset sums is o(√N). Since T∼√N the sums coincide exactly. Thus all outside edges from the first input type have one common sum u+v; likewise separately for the leaf input type.

There are k−(m−1)=n+1 outside edges. Hence n≥2 (zero or one outside vertex cannot support n+1 distinct unordered pairs, even with a loop). At least n−1 of the U inputs must give outside edges, since at most one gives a star edge. For a fixed sum on n distinct values the unordered pairs, with loops allowed, are disjoint other than possible equality of a pair with itself: choosing one value determines its partner. There is at most one loop. Thus there are at most ⌈n/2⌉ pairs. It follows that n≤3.

If n=3, at least two distinct outside edges from U have the same sum. On three distinct ordered integers this is possible only for the square of the middle value and the product of the two extremes of an arithmetic progression (their factor *sums* coincide). Write the values as v−d,v,v+d. Their product difference equals d² and their inputs both lie in U, whose full diameter is 2d, so d≤2. All labels are odd primes, hence d=2, but one of v−2,v,v+2 is divisible by 3, whereas all three tend to infinity.

If n=2, write U={u,v}, u<v. All three edges u²,uv,v² occur. Their factor sums are pairwise different, so at most one has an input in U, and at most one has a leaf input. The only remaining input is the single star center. Thus both a U input and the star-center input supply two different outside products. Because M²≥N−M and sM<N, the center s is at most (1+o(1))√N; both u,v are (1+o(1))√N. The absolute gap of those inputs is therefore at most (1+o(1))√N. But different products from the three have gap at least u(v−u)≥(2−o(1))√N, a contradiction.

This forbids M=o(N^(3/4)) on every unbounded sequence of this fixed k, hence gives M≫_k N^(3/4). The inequality pM<N gives the asserted minimum bound. The statement about nullity follows directly: the kernel of the edge-incidence matrix consists on each connected bipartite component of an alternating constant on its sides, and is zero on every component containing an odd cycle.

Finally at k=6 a second bipartite component is impossible, independently of the sizes. Each of it and S would use at least two vertices. A second bipartite component on at most four vertices has at most as many distinct edges as vertices. If either component uses at least three vertices, at most one other vertex remains, contributing at most one loop; the star's deficit cannot be absorbed. If both use two vertices, both have a deficit of one and the last two vertices can supply at most three edges. This proves the corollary.

The elementary six-vertex component enumeration can also be replayed in the [census checker](check_eac_six_all_centers.py). No bound on the maximum size of an EAC is assumed or concluded for a Goldbach exception.
## Comparison

The source graph and classification of the two-label case are due to [Bożek](https://arxiv.org/abs/1909.09900). The earlier [semiprime star lemma](EACSemiprimeStar.md) gives one bipartite component (and singularity); the new argument forces a second in the specified range. [Bahbouhi, November 2026 v1](https://www.preprints.org/manuscript/202611.0975) decomposes rough additive complements into primes and semiprimes, not factor-closed graph components. The [AMRAL September 30 semiprime transport discussion](https://amral.evemisslab.com/en/goldbach/srbrd/) concerns a different offset geometry. [Kelanemer's 2026 terminal-matrix preprint](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) is related; the search indexed the abstract but full text was not accessible, so no claim of comprehensive nonoverlap or priority is made.
