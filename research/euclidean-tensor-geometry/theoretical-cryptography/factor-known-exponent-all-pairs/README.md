# Complete known-exponent factoring by all-pairs character refinement

Let \(N>1\), and suppose that an even positive integer \(E\) divisible by
\(\lambda(N)\) is supplied, with
\(\log E=(\log N)^{O(1)}\). Strip the exact power of two from \(N\).
For each odd prime \(p\mid N\), put
\[
 s(p)=v_2(p-1).
\]
Let \(P\) be the largest odd prime divisor. For each \(s\), let
\(P_{s,1}\ge P_{s,2}\) be the two largest primes in the layer
\(\{p\mid N:s(p)=s\}\), when that layer has at least two elements. Define
\[
 H(N)=\max\left(
 P,\ \max_{s:\,|\{p:s(p)=s\}|\ge2} P_{s,1}P_{s,2}
 \right).
\]

> **Theorem.** For every fixed \(\varepsilon>0\), the complete
> prime-power factorization of \(N\) can be recovered deterministically in
> \[
> H(N)^{1/(4\sqrt e)+\varepsilon}
> (\log N+\log E)^{O_\varepsilon(1)}
> \]
> bit operations.

The algorithm does not know the primes, their \(2\)-adic layers, or
\(H(N)\). It scans ordinary integer bases and stops when every current
block is certified to be a prime power; \(H(N)\) is only an
output-sensitive stopping-time parameter.

If the distinct odd primes are
\(p_1<\cdots<p_k\), then
\[
 H(N)\le p_{k-1}p_k\le\operatorname{rad}(N)
 \qquad(k\ge2).
\]
Also \(p-1\mid E\) for every \(p\mid N\), so
\[
 H(N)\le(E+1)^2.
\]
Thus the theorem strengthens the earlier complete bound based on
\(\min\{\operatorname{rad}(N),(E+1)^2\}\). If no two odd prime divisors
have the same value of \(v_2(p-1)\), then \(H(N)=P\le E+1\), giving
\[
 (E+1)^{1/(4\sqrt e)+\varepsilon}
 (\log N+\log E)^{O_\varepsilon(1)}.
\]
In particular, if \(E=N^\tau\), the general exponent is
\(\tau/(2\sqrt e)\), while the distinct-layer case has exponent
\(\tau/(4\sqrt e)\), up to an arbitrary \(\varepsilon\).

The proof uses the Lau--Wu unconditional bound for the least value
outside \(\{0,1\}\) of a nonprincipal character with cube-free modulus.
For each pair of hidden primes, the relevant character has either one
prime as conductor or the product of the two primes. Scanning all bases
up to the largest of these pairwise witness bounds refines every pair
simultaneously, so the proof gives complete factorization rather than
only a first split.

This remains an arithmetic-advice theorem: \(E\) is supplied. It is not
an ordinary deterministic polynomial-time factoring algorithm, makes
no statement about deployed systems, and carries no absolute priority
claim.

See [PROOF.md](PROOF.md) and [UPSTREAM.md](UPSTREAM.md). Run
python3 verify.py for exact finite checks of the pair-forcing and
complete prime-power refinement lemmas.
