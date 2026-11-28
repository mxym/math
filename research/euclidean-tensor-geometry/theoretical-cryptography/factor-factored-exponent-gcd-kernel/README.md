# GCD-kernel bound for factored-exponent factoring

Let \(N>1\). Suppose an even positive integer \(E\), together with its
complete prime factorization, is supplied and
\[
 \lambda(N)\mid E,\qquad \log E=(\log N)^{O(1)}.
\]
Let
\[
 \mathcal P_E(N)=\{p:p\mid N,\ p\nmid E\}.
\]
If this set has at least two members, define
\[
 G_E(N)=
 \max_{\substack{p,q\in\mathcal P_E(N)\\p\ne q}}
 \bigl(\gcd(p-1,q-1)+1\bigr); \tag{1}
\]
otherwise put \(G_E(N)=1\).

> **Theorem.** The complete prime-power factorization of \(N\) can be
> recovered deterministically in
> \[
> G_E(N)\operatorname{poly}(\log N+\log E)
> \]
> bit operations.

The algorithm does not know the primes or \(G_E(N)\). It strips the
prime divisors listed in \(E\), scans ordinary bases, and runs all
prime-adic power-gcd chains coming from the factorization of \(E\).

The key pair lemma is elementary. For distinct residual primes \(p,q\),
put \(g=\gcd(p-1,q-1)\), and orient the pair so that
\(q-1\nmid p-1\). The subgroup
\[
 H=\{x\in\mathbb F_q^\times:x^g=1\}
\]
has exactly \(g\) elements. Among \(1,\ldots,g+1\), some base \(b\) lies
outside \(H\). Then the order of \(b\) modulo \(q\) has a prime-adic
component larger than the corresponding component modulo \(p\), so one
of the supplied-exponent gcd chains separates the pair. If \(p\mid b\),
the initial saturated gcd separates it directly.

If the residual primes are \(p_1<\cdots<p_k\), then
\[
 G_E(N)\le p_{k-1}\qquad(k\ge2). \tag{2}
\]
More sharply, pairwise bounds
\(\gcd(p-1,q-1)\le L\) give deterministic time
\((L+1)\operatorname{poly}(\log N+\log E)\).

Combining this elementary stopping bound with the independent
prime-conductor Lau--Wu bound at commit
46afa65c4e8fd9999822dcdd8bfd492522cff0b7 gives, for every fixed
\(\varepsilon>0\),
\[
 \min\!\left\{
 G_E(N),\ P_E(N)^{1/(4\sqrt e)+\varepsilon}
 \right\}
 \operatorname{poly}_{\varepsilon}(\log N+\log E), \tag{3}
\]
where \(P_E(N)=\max(\mathcal P_E(N)\cup\{1\})\).

This is an arithmetic-advice theorem. It neither constructs nor factors
\(E\), is not an ordinary deterministic polynomial-time factoring
algorithm, and concerns no concrete modulus or deployed system. No
absolute priority claim is made.

See [PROOF.md](PROOF.md) and [UPSTREAM.md](UPSTREAM.md). Run
\`python3 verify.py\` for finite exact checks.
