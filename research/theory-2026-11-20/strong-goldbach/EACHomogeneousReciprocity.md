# A reciprocal prime-factor component cannot have constant row multiplicity

In a nontrivial exceptional autonomous component (EAC) of [Bożek's complement factor graph](https://arxiv.org/abs/1909.09900) at an even center N, write d_p=Ω(N−p), counting multiplicity. Each complementary row factors over the component's odd prime labels, all coprime to N. A row is *pure* if it is a power of one prime. Call the component reciprocal if q | N−p implies p | N−q for every arc, without requiring matching multiplicities.

**Theorem.** Let M be the largest label of a reciprocal EAC and a=d_M. For any two distinct pure rows with exponents b,c one has gcd(b,c)<a/2. In particular, there is no reciprocal EAC in which all pure rows have the same exponent, and none in which d_p is constant. Both component size and degrees are unrestricted. This does not exclude arbitrary EACs or imply binary Goldbach.

**Proof.** The underlying reciprocal support is a tree: two different neighbors of a vertex p are congruent to N modulo p and cannot both be smaller than p. Thus a largest vertex on an undirected cycle is impossible. There are no loops, by coprimality, and the component is connected. Its maximum M is a leaf with unique neighbor q<M. Write N=M+q^a. Because M divides N−q, it divides q(q^{a−1}−1), and therefore q^{a−1}−1. The cases a=2,3 are impossible: neither q−1 nor q+1 has a prime divisor greater than q. The nontrivial exceptional component has no prime rows (a prime complementary row gives a terminal Goldbach pair). Thus a≥4. Now q−1 is invertible modulo M, so M divides the positive geometric sum
     
     S=(q^{a−1}−1)/(q−1),   M≤S<(q/(q−1))q^{a−2}≤(3/2)q^{a−2}.

Take any two distinct pure rows, not necessarily at M. If g=gcd(b,c)≥a/2 then g≥2, and their complementary values are distinct positive g-th powers U^g>V^g, with V^g≥N−M=q^a. Hence
     
     U^g−V^g ≥ (V+1)^g−V^g ≥ g V^{g−1} ≥ 2 q^{a(1−1/g)} ≥ 2 q^{a−2} > M.

However this difference is the distance between their two input labels, less than M. This proves the claimed bound simultaneously for every pair. The tree has at least two leaves, each of which gives a pure row. If all pure rows have a common exponent, that exponent is a and its gcd with itself violates the bound. ∎

The power-gap argument itself needs only that every outgoing arc of the **maximum** has its reverse; this alone gives its unique smaller neighbor, pure row and same bound. Full reciprocity was used to guarantee a second pure row via the tree. Since two distinct pure rows exist in any reciprocal EAC, this conclusion is complementary to the [row-multiplicity-at-least-six restriction](EACReciprocalFive.md), not a global bound on all EAC degrees.

This uses the actual reciprocal prime support, not a claim about all exponent matrices in the [related 2026 graph project](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7274460). Its complete text could not be checked in this comparison. The power-gap argument does not depend on a computational center cutoff.
