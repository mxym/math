# A 2-adic rank test with prescribed genuine-prime seeds

Let N be even, 2^a|N with a≥1. Let C be ANY finite set of k different odd primes coprime to N, all <N−1, closed under prime factorization of every N−p for p∈C. Assume these rows are composite. C need not be a strongly connected component. Write A_{ij}=v_{p_j}(N−p_i), B=I−A, D=max_i Ω(N−p_i), H=√(1+D²). Let S⊂C have s≥1 labels. There is an effectively computable K_s depending only on s such that
     
    a > K_s · (∏_{p∈S} log p) · log(max(3,2H^k))                      (1)

forces the classes of all s standard generators indexed by S to be linearly independent in ℚ^k/row_ℚ(B). In particular corank_ℚ(I−A)≥s. Every vertex set intersecting every directed cycle of C must then have at least s+1 members. Use natural logarithms.

**Actual-exception interpretation.** If N=2^a were a Goldbach exception, choose any prescribed fixed list of s distinct odd primes as seeds (for sufficiently large a). Form their joint forward closure by adjoining all prime divisors of every encountered N−p. At every step p is odd and coprime to N, N−p is odd composite rather than prime, and its prime factors are still odd, coprime to N and at most (N−3)/3. The seeds start below N−2. Thus the operation terminates in a subset of the odd primes below N−1 satisfying the hypotheses. Along any unbounded such sequence, if the generated closure has k=o(log N/loglog N), (1) holds because D≤log N/log 3, so the chosen seed directions are independent and every feedback set has size ≥s+1. Equivalently, failure of this rank or hitting-set conclusion forces k≫_S log N/loglog N. This is a necessary condition on the generated closure; it does not assert that all seeds reach the same terminal EAC or lie in one. It also applies under its exact conditions to any EAC that actually contains S and to suitable odd seeds coprime to a general even center. It gives no contradiction for large closures or high corank.

### A short supported integral relation whenever the classes are dependent

Let T be the columns outside S. Dependence means that the rational row space has a nonzero vector supported on S, equivalently rank B>t=rank B_{*,T}. Choose t independent columns J from T and one column i from S extending them. Choose t+1 rows K on which J followed by i gives a nonsingular minor. On these rows take coefficients equal to the signed t-row minors of the column block J, as in expansion in the last column (for t=0 the empty minor is 1). Their integral combination u of rows of B vanishes on J and hence on T; its i-th coordinate is the nonzero chosen determinant. Every coordinate of u is up to sign a (t+1)-row minor (zero for repeated columns) and satisfies |u_j|≤H^{t+1}≤H^k by Hadamard. The diagonal of A vanishes by coprimality, giving the asserted row norm. In particular u is an actual integral row combination, not just a vector in the saturation.

For every such row combination ∏_{p∈S}p^{u_p}≡±1 (mod 2^a): this follows directly from ∏_j p_j^{A_{ij}}=N−p_i≡−p_i, and negative integral powers cause no problem for odd units. Therefore Ξ=∏p^{2u_p}−1 satisfies v₂(Ξ)≥a. Unique prime factorization and u≠0 show Ξ≠0 even as a rational number.

### The local logarithm estimate

For n≤s nonzero exponents use [K. Yu, *p-adic logarithmic forms and group varieties II*, Acta Arith. 89 (1999), 337–378, Theorem 1 and its consequence on p. 337](https://bibliotekanauki.pl/articles/1390501.pdf), [DOI](https://doi.org/10.4064/aa-89-4-337-378). For n fixed, odd primes l_j, and integer exponents b_j, not all zero, the nonzero Ξ=∏l_j^{b_j}−1 satisfies
     
    v₂(Ξ) < c_n · (∏_{j=1}^n log l_j) · log(max(3,max_j |b_j|)) .

For completeness one can apply Theorem 1 in the field ℚ(ζ₃), satisfying Yu's auxiliary p=2 hypothesis (1.2): the prime over 2 is unramified of degree 2, so its valuation agrees with v₂ on rationals, d=2, e=1, f=2 and h′(l_j)=max(log l_j,log 2)=log l_j in (1.5). The explicit c_n=C(n,2,𝔭) of (1.10) suffices. Hypothesis (1.9) holds since all l_j are odd. No strengthened independence constant of (1.11) is needed. Apply this to b_j=2u_j at its nonzero coordinates. Take K_s=max_{1≤n≤s} c_n; the omitted factors log p exceed one, so restoring them weakens the bound. This contradicts (1), proving independence.

### Directed interpretation of corank

Let F meet every directed cycle. Its complement U is a directed acyclic graph and A_{UU} is nilpotent in a topological order. Eliminating the U coordinates of f in Af=f identifies the kernel with ker(I−K), where
     
    K=A_{FF}+A_{FU}(I−A_{UU})^{-1}A_{UF}.

Each entry of K counts walks from F until their first return to F, with multiplicity; the inverse is a finite sum of nonnegative powers. Each of the at least two first arcs counted with multiplicity out of each f∈F extends to a path back to F: a path in U cannot continue forever and all vertices have nonzero outdegree. Thus every row sum of K is at least 2, I−K is nonzero and its nullity is at most |F|−1. The graph is finite, nonempty and has no sink, so F cannot be empty. This argument does not require strong connectivity.

This [extends the dyadic Smith observation](EACDyadicSmith.md) to a lower bound on corank, but needs Yu’s local logarithm estimate. The comparison to the 2026 terminal-island work in that note applies here too: this is a bound on a concrete generated closure, not a characterization of what every large exception contains beyond the displayed necessary condition.
