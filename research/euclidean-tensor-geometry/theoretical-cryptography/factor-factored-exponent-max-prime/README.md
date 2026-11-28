# Deterministic known-exponent factoring with factored advice

Let \(N>1\). Suppose an even positive integer \(E\), together with its
complete prime factorization, is supplied and satisfies
\[
 \lambda(N)\mid E,\qquad \log E=(\log N)^{O(1)}.
\]
Define
\[
 P_E(N)=\max\bigl(\{p:p\mid N,\ p\nmid E\}\cup\{1\}\bigr).
\]

> **Theorem.** For every fixed \(\varepsilon>0\), the complete
> prime-power factorization of \(N\) can be recovered deterministically in
> \[
> P_E(N)^{1/(4\sqrt e)+\varepsilon}
> \operatorname{poly}_{\varepsilon}(\log N+\log E)
> \]
> bit operations.

The factorization of \(E\) is advice. The algorithm first removes every
prime divisor of \(N\) that occurs in the supplied factorization of
\(E\). Every prime left in the residual input occurs to the first power.
For a residual prime \(p\), the full valuation vector
\[
 \mathbf s_E(p)=\bigl(v_r(p-1)\bigr)_{r\mid E,\ r\ {\rm prime}}
\]
determines the integer \(p-1\), because \(p-1\mid E\). Hence distinct
residual primes have distinct vectors.

For each pair, one differing coordinate \(r\) gives a prime-conductor
character of \(r\)-power order. Lau--Wu's least-character-value bound
then supplies a separating ordinary integer base below
\(P_E(N)^{1/(4\sqrt e)+\varepsilon}\). Running every \(r\)-adic
power-gcd chain for every scanned base separates all pairs
simultaneously.

The algorithm does not enumerate the divisors of \(E\), and it does not
know \(P_E(N)\). It recognizes completion by deterministic primality
testing. In particular,
\[
 P_E(N)\le E+1,
\]
so a weaker input-only bound is
\[
 (E+1)^{1/(4\sqrt e)+\varepsilon}
 \operatorname{poly}_{\varepsilon}(\log N+\log E).
\]

This is an arithmetic-advice theorem. It does not construct or factor
\(E\), and it is not an ordinary deterministic polynomial-time
factoring algorithm. It concerns no concrete modulus or deployed
system, and no absolute priority claim is made.

See [PROOF.md](PROOF.md) and [UPSTREAM.md](UPSTREAM.md). Run
\`python3 verify.py\` for finite exact checks.
