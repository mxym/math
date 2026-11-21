# Rank-one returns force an exact balanced parametrization with a moving small alphabet

Let N→∞ be an unbounded sequence with a strongly connected closed prime-factor component of composite complements on 2t labels, where t≥2 is fixed and each label is coprime to N. Suppose nullity(I−A)=t−1 and, on the selected weight-convergent subsequence, there are **t weight-zero labels** S={s₁,...,s_t} and **t weight-one labels** R. Here weight means lim(log x/log N). Then eventually there are an even positive integer h=N^{o(1)} and W=1+hN such that rad(W)=∏_{s∈S}s, and for each s∈S

    v_s=1+hs divides W,         R_s=(W/v_s−1)/h is its distinct prime partner.

The t partners R_s are all the high labels. Neither common h nor the primes in S are required to be fixed. This is a rank-based extension, for this extremal nullity, of the [fixed-alphabet balanced parametrization](EACBalancedCores.md). It is a necessary condition, not a contradiction or a primality claim; its converse under the displayed primality/support conditions is the same direct factorization as in the linked theorem.

**Affine paths and first returns.** For large N each high factor is greater than √N; any row targeting one uses it with multiplicity one, and uses no other high label. Its remaining integral cofactor v≥3 is N^{o(1)}. There is no all-high directed cycle: if N−R_i=v_i R_{i+1} on a cycle of length j (indices cyclic), composing gives (∏v_i−(−1)^j)R_1 an integer multiple of N. Coprimality contradicts 0<∏v_i−(−1)^j=N^{o(1)}<N. Thus starting at s∈S and following the unique high successor, when there is one, always terminates after i≤t high targets in a row whose complement is supported on S. With x_0=s, write the resulting path primes

    x_j=(A_j N+(-1)^j s)/V_j,   V_0=1, A_0=0, V_j=v_j V_{j−1}, A_j=V_{j−1}−A_{j−1}.

Since v_j≥3 these give 0≤A_j<V_j and V_j=N^{o(1)}, including a path of length zero.

The outside block A_RR is nilpotent. The first-return matrix K=A_SS + A_SR(I−A_RR)^(-1)A_RS counts multiplicities of paths from one member of S to the first following visit to S. It is irreducible by strong connectivity, and its row sums are at least two since each outgoing arc of each s contributes at least one terminal path including multiplicity. Schur elimination gives nullity(I−K)=t−1. As K is t-by-t and its Perron root ρ≥2, K−I has rank one and is *strictly positive*: its columns are in the positive right Perron line of K−I and its rows are in the positive left Perron line, and its nonzero eigenvalue ρ−1 is positive. Therefore K−I=abᵀ with a,b strictly positive integer vectors and gcd_i a_i=1. For instance choose the primitive positive integer vector on its rational column line; every integral column is an integer multiple of it (Bézout).

Put W=∏s_j^{b_j}. The monomial associated to the s row of K is V_i(N−x_i): along the high path every outgoing small exponent is accumulated once, all continued high arcs have exponent one, and at its end the full complement factors on S. In particular

    W^{a_s}=V_i(N−x_i)/s=[(V_i−A_i)N+(-1)^{i+1}s]/s.                 (1)

No first-path disjointness was needed to derive this. Integrality and (s,N)=1 imply s|(V_i−A_i); since V_i−A_i>0 this forbids i=0, for which V_0−A_0=1. Thus each small input directly uses a high label, these t labels are distinct (a high common divisor would divide the difference of two small primes) and exhaust R.

There is no high-to-high edge. If R_s→R_t with s≠t, write N−s=v_s R_s, N−t=v_t R_t, N−R_s=w R_t with v_s,v_t,w=N^{o(1)}. Substitution gives

    N[(v_s−1)v_t−w v_s]=−s v_t−w v_s t.

The right side is a strictly negative integer of absolute value N^{o(1)}, impossible. Self edges are absent. Every path length in (1) is now one, so s|(v_s−1), h_s=(v_s−1)/s is a positive even integer, and W^{a_s}=1+h_s N. Each W^{a_s}≡1 mod N, W is a unit at N, and gcd(a_s)=1; Bézout gives W≡1 mod N. As W>1, W≥N+1. But every W^{a_s}≤N^{1+o(1)} by the cofactor bound, hence a_s=1 for all s for sufficiently large N. This proves the common h=(W−1)/N=N^{o(1)} and rad(W)=∏s_j since all entries of b are positive. Finally (1+hs)(1+hR_s)=1+hN proves divisibility and the displayed partner formula exactly.

**Dated comparison.** [Kelanemer, August 12, revised September 6, 2026](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460) considers neighboring exponent-matrix reductions. Its full text could not be accessed for comparison. The statement here concerns the specific logarithmic-size and rank hypotheses above and makes no priority or Goldbach-proof claim.
