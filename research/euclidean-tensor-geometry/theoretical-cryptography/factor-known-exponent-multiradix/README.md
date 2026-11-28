# Multiradix refinement for deterministic known-exponent factoring

Let \(N>1\), let \(E\) be a supplied even positive multiple of
\(\lambda(N)\), and assume
\(\log E=(\log N)^{O(1)}\). Choose a parameter \(z\ge2\) of size
\((\log N)^{O(1)}\). Trial division first removes every prime factor of
\(N\) not exceeding \(z\).

For each remaining prime \(p\mid N\), define its small-prime valuation
signature
\[
 \mathbf s_z(p)=\bigl(v_r(p-1)\bigr)_{\substack{r\le z\\r\ {\rm prime}}}.
\]
Let \(P\) be the largest remaining prime. In every signature class,
take the two largest primes \(P_{\mathbf s,1}\ge P_{\mathbf s,2}\), when
the class has at least two members, and put
\[
 H_z(N)=\max\left(
 P,\ \max_{\mathbf s}P_{\mathbf s,1}P_{\mathbf s,2}
 \right). \tag{1}
\]
If no prime remains, set \(H_z(N)=1\).

> **Theorem.** For every fixed \(\varepsilon>0\), the complete
> prime-power factorization of \(N\) can be recovered deterministically in
> \[
> H_z(N)^{1/(4\sqrt e)+\varepsilon}
> \operatorname{poly}_\varepsilon(z,\log N+\log E)
> \]
> bit operations.

The algorithm does not know the signatures or \(H_z(N)\). It enumerates
the small primes \(r\le z\), runs the corresponding \(r\)-adic
order chains on ordinary integer bases, and stops once every current
block is certified to be a prime power.

The case \(z=2\) is the quadratic-layer all-pairs theorem. Increasing
\(z\) refines the hidden classes. If all remaining primes have distinct
signatures, then
\[
 H_z(N)=P\le E+1,
\]
and the complete-factor bound becomes
\[
 (E+1)^{1/(4\sqrt e)+\varepsilon}
 \operatorname{poly}_\varepsilon(z,\log N+\log E).
\]
In general, if the remaining distinct primes are
\(p_1<\cdots<p_k\), then
\[
 H_z(N)\le p_{k-1}p_k\le\operatorname{rad}(N),
 \qquad H_z(N)\le(E+1)^2.
\]

The proof combines two ideas. If two primes have different signatures,
one small prime \(r\le z\) witnesses different \(r\)-parts of their local
orders; a prime-conductor character of order a power of \(r\) forces the
difference. If their signatures agree, their \(2\)-parts agree, and the
two-prime quadratic character separates them. Lau--Wu bounds the needed
base by the conductor to the power \(1/(4\sqrt e)+\varepsilon\).
All pairs are refined simultaneously.

This is an arithmetic-advice result: \(E\) is supplied. It neither
constructs \(E\) nor gives an ordinary deterministic polynomial-time
factoring algorithm. It makes no statement about a deployed system and
no absolute priority claim.

See [PROOF.md](PROOF.md) and [UPSTREAM.md](UPSTREAM.md). Run
python3 verify.py for finite exact checks.
