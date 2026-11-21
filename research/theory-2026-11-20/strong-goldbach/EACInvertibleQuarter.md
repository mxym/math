# A quarter-power small prime in every bounded-size component with invertible exponent matrix

Fix k. If an even N has a nontrivial [Bożek exceptional autonomous component](https://arxiv.org/abs/1909.09900) of at most k labels with invertible exponent matrix A, then its least prime label satisfies

    p ≤ N^(1/4)+O_k(1).

Here A_ij=v_{x_j}(N−x_i), with all prime factors in the component, all labels distinct odd primes coprime to N, and every row composite. This applies without smoothness, residue, symmetry or seed hypotheses and is pointwise, not an estimate on the number of centers. The matrix is A, **not** I−A. Singular matrices remain outside the theorem.

## 1. The only weight pattern above a quarter

Only p≥N^(1/4) and N arbitrarily large need consideration. Every row then contains two or three factors, since four factors would have product ≥N. There are finitely many resulting integer matrices for fixed k. In an unbounded sequence fix the matrix, sort the labels increasingly, and write M for the largest. Since every label occurs in a composite row with another factor at least p, Mp<N. In particular M/N→0. Put w=A^(-1)1; taking real logarithms in the exact positive factorizations gives

    log x = w log N + A^(-1)(log(1−x_i/N))_i
          = w log N + O_A(M/N).

All weights w_i are ≥1/4 and at most 3/4. If the smallest w_i equals 1/4 this estimate already yields p≤N^(1/4) exp(O_A(1/p))≤N^(1/4)+O_A(1). If any w_i<1/4 the assumed large sequence cannot exist. Thus it is enough to exclude the strict case min w_i>1/4. In particular a sequence with p/N^(1/4)→∞ necessarily has strict weights on every fixed surviving chart.

If all rows are semiprime, A is singular by the [maximal-star incidence proof](EACSemiprimeStar.md). If every row is triple, A1=3·1 gives w_i=1/3 for all i. All labels are then N^(1/3)+O_A(N^(−1/3)) by the log estimate, impossible for distinct integers. It remains to treat mixed rows.

Call weights less than, equal to, or greater than 1/2 low, mid and high. Since all weights exceed 1/4 and the output weights in each row sum to one, every triple uses only lows; a pair uses either a low and a high or two mids. The vector assigning 1/3 to every low, 1/2 to every mid and 2/3 to every high therefore ALSO solves A w=1. Invertibility forces it to be the true w. Write n=N^(1/3) and t,s,h for the numbers of lows, mids and highs. There is at least one low since there is a triple.

## 2. First corrections and the low block

From x_i=N^{w_i}(1+o(1)), expand the same inverse-log identity to first order:

    log x_i = w_i log N + c_i/n + o_A(1/n),
    c=−A^(-1)1_H,

where 1_H indicates the high *input* labels. Indeed x_i/N=n^(−1)(1+o(1)) on highs and o(1/n) elsewhere. Thus low values have the form n+c_i+o(1); mid values are n^(3/2)+O_A(n^(1/2)); highs are n²+c_i n+o_A(n). Whenever two distinct lows exist, the difference of their constants is a nonzero even integer: the difference of their odd prime values converges to this constant and cannot vanish.

Any high occurs on exactly one row. It is a member of a low-high pair and is >M/2 for large N, and it cannot divide the difference of two distinct odd inputs: that positive even difference would be at least twice the high and at most M−p. There are therefore exactly h low-high rows, one per high.

After permuting rows and columns, the triple rows use just the low-column block C, the h low-high rows have an identity on the h high columns, and the remaining mid-pair rows use just the mid-column block E. Eliminating the exclusive high columns shows C and E are square and invertible over Q: the remaining block diagonal matrix must have full column and row rank. This includes the case of an empty mid block or no high columns. In particular the number of triple rows is t and the number of mid-pair rows is s. E is the unsigned incidence matrix of the mid-pair graph, with a 2 at a loop. Every one of its connected components is nonbipartite: a bipartite component would give the alternating nonzero right-null vector (and an isolated vertex likewise).

The three low factors in a triple multiply to n³+n²(c_i+c_j+c_l)+o(n²). Their product is N minus its input, so the sum is −1 if that input is high and 0 otherwise. Across all triple rows the sums differ by even integers, since every pair of low constants differs by an even integer (trivially true for a single low). Hence all sums are equal, as 0 and −1 differ by one. All row sums of C are 3; C invertible and C c_low constant imply all low constants are equal. Distinct lows had nonzero constant differences. We conclude **t=1**, so p is the sole low, and its cube p³ is the only triple output. The h low-high outputs all take the form pH.

## 3. The mid rows and the last congruence

The h+1 inputs associated with p³ and pH all equal N mod p. None can be p by coprimality; at most one can be mid because mid differences are O_A(n^(1/2))=o(p). Therefore there is at least one mid, and these inputs comprise exactly all h highs and one mid. In particular if h=0 the single input of p³ must be a mid, and all the other inputs (including p) supply mid pairs; no high estimate is needed in this case. Generally the s mid-pair edges have inputs p and s−1 mids.

All these inputs are O_A(√N). Along any mid-pair edge uv=N−x, the sum log(u/√N)+log(v/√N) is O_A(1/√N). Every mid vertex has a bounded-length odd closed walk because its component is nonbipartite. Alternating along that walk yields u=√N+O_A(1) for every mid. Let T=⌊√N⌋. For two mid-pair edges whose inputs are mids, write their factor pairs as T+i,T+j and T+i',T+j'. Their input gap is bounded; their product gap is T(i+j−i'−j') plus the bounded quantity ij−i'j'. Thus their integer factor sums coincide for large N. The s−1 edges with mid inputs therefore comprise distinct pairs of one fixed sum on s values. Such pairs are disjoint, with at most one loop, so s−1≤⌈s/2⌉ and s≤3 (for s=1 no pair comparison is needed).

At s=3 the two equal-sum pairs are the middle square and the product of the two extremes of an arithmetic progression m−d,m,m+d. Their product gap d² equals a gap between two mids and is at most 2d. Thus d=2 since all three are odd, impossible for three growing primes by reduction mod 3. At s=2 the two distinct mid products on u<v have gap ≥u(v−u)≥2u; their inputs, p and one mid, have gap ≤v=(1+o(1))u, impossible.

Finally if s=1 write m for the mid. Its sole mid-pair row has input p: N=m²+p. We have m∼p^(3/2) and m≡N mod p, hence m≡1 mod p. Any high H also satisfies H≡N≡1 mod p. The input m has output either pH or p³. In the former case N−m=m²+p−m≡p mod p², so m≡1 mod p². In the latter case m²+p−m≡0 mod p²; substituting m=1+pa gives a≡−1 mod p, i.e. m≡1−p mod p². Neither residue is possible for p≪m≪p² with m/p→∞ and m/p²→0. This excludes the final possibility. The finite number of charts makes the O_k(1) statement uniform; no threshold or optimal constant is claimed effective here.

This covers all invertible signatures and arbitrary fixed size, rather than listing individual mixed two-/three-factor assignments. It does not prove that a Goldbach exception has an invertible component, nor exclude components with a small least prime.
## Comparison

The [previous invertible-matrix census](EACJacobianSquareRoot.md) bounds the number of centers in this scope; it does not impose this pointwise bound on the least prime. The [semiprime-only result](EACSemiprimeQuarter.md) controls certain singular graphs, while the [six-label triple result](EACSixTripleQuarter.md) also treats singular matrices in that homogeneous case. [Bożek](https://arxiv.org/abs/1909.09900) supplies the original graph framework. [Kelanemer's 2026 preprint](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) studies closely related terminal exponent-matrix conditions; the index was accessible but full text was not, so no priority or exhaustive-nonoverlap claim is made. [Nelson, November 2026 v2](https://arxiv.org/abs/2611.14580v2) instead studies additive relations in a prime-indexed ring.
