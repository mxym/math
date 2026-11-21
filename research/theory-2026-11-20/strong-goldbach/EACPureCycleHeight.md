# An effective height obstruction for prime-power components of arbitrary size

Use the reversed prime-factor graph from [Bożek, §§2–3](https://arxiv.org/abs/1909.09900): at even N a label p points to every prime divisor of N−p. An exceptional autonomous component (EAC) here is a factor-closed strongly connected set of at least two prime labels, all coprime to N and with all complements composite. **An EAC is not a Goldbach exception.** Bożek's Theorem 2.6 forces some EAC at a hypothetical missing Goldbach number, not one with the properties imposed here.

**Theorem.** Suppose each complementary row of an EAC is a pure prime power. There is no bound assumed on its cardinality k. The exponents a₁,…,aₖ are pairwise coprime, and, for D=∏aᵢ,
    
    log N ≤ 100 D³ k .                                               (1)

In particular some label is at most exp(C log N/loglog N), with an effective absolute C (for sufficiently large N). For each fixed k some label is at most exp((100k)^(1/(3k)) (log N)^(1−1/(3k))). These are uniform, effective restrictions, not an exclusion of all such components or of all counterexamples. Moreover the theorem automatically applies to **every** EAC with max C < 3 min C, without a prior pure-power hypothesis.

### A cycle of powers and separated weights

Since every vertex then has just one outgoing neighbor, strong connectivity makes the graph one directed cycle. Index it so that
    
    xᵢ^{aᵢ}=N−xᵢ₊₁ (cyclic indices),     aᵢ≥2.                      (2)

In particular all xᵢ≤√N. If two exponents shared a divisor g≥2, the corresponding two different numbers N−xᵢ₊₁ would be g-th powers Uᵍ>Vᵍ. Their difference is at least 2V^{g−1} ≥ 2√(N−√N)>√N for N≥4: expand (V+1)ᵍ. The actual difference is less than √N. Thus the exponents are pairwise coprime. For a box index ν=(νᵢ) with 0≤νᵢ<aᵢ, let w(ν)=∑νᵢ/aᵢ. These D weights are distinct modulo 1: multiply an equality modulo 1 by D and reduce separately modulo each aᵢ. The fraction parts consequently run through all multiples of 1/D in [0,1). We need no assumption about smoothness or irreducibility of a curve.

For the narrow-cluster assertion, if one output prime ℓ divided two distinct rows, it would divide the positive difference of their two odd input labels. This difference is even, hence at least 2ℓ≥2 min C, contradicting the width. So the nonempty sets of distinct output primes of the k rows are pairwise disjoint subsets of C; all are singletons. In fact the same argument gives the pure-cycle criterion whenever no ℓ∈C divides a nonzero difference of two labels.

### An integer auxiliary polynomial

Treat t and the Xᵢ as indeterminates. Let m=2Dk. Consider the T distinct monomials tʲX^ν with 0≤νᵢ<aᵢ, integer j≥0, and j+w(ν)<m. Their weights j+w(ν) are distinct, with gaps at least 1/D. Since 0≤w<k, we have
    
    D(m−k) ≤ T ≤ Dm .

For each of these monomials first multiply by X₁^m, then replace every occurrence of Xᵢ^{aᵢ} by t−Xᵢ₊₁ until all terms have box exponents; choose the first possible index to be definite. Discard powers divisible by t^m. Each replacement on a single term lowers its total X-degree by at least one in both children, so it terminates and produces at most 2^{m+D} leaves. Indeed ∑(aᵢ−1)≤D−1. Encode the output in integer coordinates on the Dm box monomials with t-degree <m. This gives a Dm-by-T integer matrix with entries bounded by H=2^{m+D}; uniqueness of normal remainders is not needed. All replacements preserve evaluation under the defining equations.

Its rank r is at most (D−1)m, not Dm: formally there exist xᵢ(t)∈tℤ[[t]] with xᵢ₊₁(t)=t−xᵢ(t)^{aᵢ}. Starting at all zero, iteration converges t-adically since the difference of two powers of elements of tℤ[[t]] gains at least one order. Evaluation of box remainders on this solution mod t^m is a surjective linear map ℚ^{Dm}→ℚ[t]/(t^m), because the pure tʲ, 0≤j<m, already form a basis in its image. Every reduced column maps to zero because its original monomial contains x₁(t)^m. Thus T−r≥m/2.

For completeness we give a coefficient bound rather than invoking an ineffective integral-point theorem. Put K=4TH, A=K^{2D+1}. Restrict the matrix to r linearly independent rows; zero on these implies zero on every row over ℚ. The integral vectors with coordinates from 0 to A have at most (2THA+1)^r ≤ (KA)^r outputs on these rows. There are (A+1)^T inputs and A^{T−r}>K^r since r/(T−r)≤2D. Subtract two inputs mapping equally. We obtain a **nonzero** integer polynomial P in the T monomials, each coefficient of absolute value ≤A, such that the remainder of X₁^m P is zero modulo t^m. This means precisely that X₁^m P equals a multiple of t^m modulo the integer polynomial relations Xᵢ^{aᵢ}−t+Xᵢ₊₁. No bounds on denominators or bad reduction primes are implicit.

### Divisibility and dominance

Evaluate at (N,x). The remainder gives N^m | x₁^m P(N,x) and gcd(N,x₁)=1 gives N^m | P(N,x). For a monomial of weight h=j+w, its actual positive value lies between
    
    (1−N^(−1/2))^k N^h    and    N^h .

Assume N>(4TA)^D. Then √N≥2k so the lower factor is at least 1/2. The maximum weight in P is no more than m−1/D, giving |P(N,x)| ≤ TA N^{m−1/D}<N^m. But its unique top-weight monomial, with nonzero integer coefficient, has magnitude at least N^h/2; the other terms have total magnitude at most TA N^{h−1/D}<N^h/4. Thus P(N,x) is nonzero, contradicting divisibility. We have proved N≤(4TA)^D. In particular log N≤ D[log(4T)+(2D+1)log(4TH)]≤100 D³k: use T≤Dm=2D²k, D≥6, k≤log₂D, log(4T)≤2Dk, and (m+D)log 2≤3Dk. This argument even gives a direct finite search upper bound for any prescribed exponent list.

Let M=max aᵢ. From pairwise coprimality D divides lcm(1,…,M). The standard elementary Chebyshev bound log lcm(1,…,M) ≪ M has an effective constant. For example if Ψ(m)=log lcm(1,…,m), then Ψ(2n)−Ψ(n)≤log binom(2n,n)≤2n log2, since each prime power in (n,2n] contributes its prime to that binomial and there is at most one such power per prime. Sum on dyadic n and round up to get Ψ(M)≤4M log2. As k≤M, (1) implies M≫loglog N. Alternatively at fixed k, D≤M^k gives M≥(log N/(100k))^(1/(3k)). In both estimates use the label with exponent M in (2) to finish.

**Scope and comparison.** This is an arbitrary-cardinality *prime-power-row* result, not a restriction requiring every Goldbach exception to have all its rows of this kind. Bożek's known N=2200 two-cycle is consistent with it; at 128 the known EAC has some mixed rows. Earlier [three-label fixed-signature curve arguments](EACThreeSubpower.md) covered three labels even when rows are mixed, but did not give (1). General results for several perfect powers in a short interval, e.g. [Stewart, Acta Arith. 133 (2008)](https://uwaterloo.ca/pure-mathematics/sites/default/files/uploads/documents/aa133-2-01.pdf), do not impose (2)'s cyclic reuse of the bases. The proof here uses that reuse, coprimality with N, and elementary linear algebra. The accompanying exact control checks the reduction/origin rank mechanism on small synthetic exponent systems; it is not used to certify the bound computationally.

The closest retrieved 2026 graph record, [Kelanemer's terminal-island preprint](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460), works under a global counterexample hypothesis and uses an exponent-matrix framework. The full text could not be accessed for this comparison. The height calculation here is local, applies at represented centers as well, and does not presume a characterization of those terminal islands.
