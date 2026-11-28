# Proof

## 1. Preprocessing

Validate every entry of \(\mathcal S\) as prime and remove duplicates.
Construct
\[
 E=\prod_{\substack{r\in\mathcal S\\r\le N}}
 r^{\lfloor\log_rN\rfloor}. \tag{3}
\]
For every prime power \(p^a\parallel N\),
\[
 \lambda(p^a)\mid\lambda(N).
\]
Every prime dividing \(p-1\), and also \(p\) when \(a\ge2\), therefore
belongs to \(\mathcal S\). Consequently
\[
 \lambda(N)\mid E,\qquad
 \log E\le|\mathcal S|\log N. \tag{4}
\]

Divide the full power of each listed prime out of \(N\). The remaining
integer \(M\) is squarefree: if \(p^a\mid M\) with \(a\ge2\), then
\(p\mid\lambda(p^a)\mid\lambda(N)\), contrary to the complete division
of listed primes.

Maintain a partition of \(M\) into coprime blocks. For every ordinary
integer base \(u\) in the range specified below, first split a block
\(D\) by
\[
 \gcd(D,u^{\lceil\log_2D\rceil}). \tag{5}
\]
This separates all prime factors of \(D\) dividing \(u\). On the
coprime remainder, for every \(r\in\mathcal S\) and
\(0\le j\le v_r(E)\), split by
\[
 \gcd(D,u^{E/r^j}-1). \tag{6}
\]

## 2. Pairwise separation under GRH

Assume GRH for Dirichlet \(L\)-functions. Bach's explicit subgroup
bound says that for a prime \(p\) and a proper subgroup
\(H<\mathbb F_p^\times\), there is a positive integer
\[
 u\le 2(\log p)^2 \tag{7}
\]
whose residue is outside \(H\). Finitely many small moduli can instead
be covered directly; this does not change polynomial complexity.

Take two distinct residual primes \(p,q\) in the same current block and
write
\[
 g=\gcd(p-1,q-1),\quad
 A=(p-1)/g,\quad B=(q-1)/g. \tag{8}
\]
The coprime integers \(A,B\) cannot both equal \(1\). Suppose first
that \(A>1\). The subgroup
\[
 H_p=\{x\in\mathbb F_p^\times:x^g=1\}
\]
is proper. Choose \(u\le2(\log p)^2\le2(\log N)^2\) outside \(H_p\).

If \(u\) is divisible by \(q\), (5) separates \(q\) from \(p\).
Otherwise \(u\) is a unit modulo both primes. Since
\(\operatorname{ord}_p(u)\nmid g\), some prime \(r\mid A\) satisfies
\[
 v_r(\operatorname{ord}_p(u))>v_r(g). \tag{9}
\]
Because \(\gcd(A,B)=1\),
\[
 v_r(\operatorname{ord}_q(u))
 \le v_r(q-1)=v_r(g). \tag{10}
\]
The prime \(r\) divides \(p-1\mid\lambda(N)\), so \(r\in\mathcal S\).
Since \(E\) is a common multiple of both orders, there is an index \(j\)
for which
\[
 \operatorname{ord}_q(u)\mid E/r^j,\qquad
 \operatorname{ord}_p(u)\nmid E/r^j. \tag{11}
\]
The corresponding gcd in (6) separates the pair. If \(A=1\), then
\(B>1\), and the symmetric argument in \(\mathbb F_q^\times\) applies.

Thus the scan
\[
 2\le u\le \lceil2(\log N)^2\rceil \tag{12}
\]
separates every pair of distinct residual primes. Repeatedly applying
the gcd refinements therefore leaves only singleton prime blocks.
Together with the prime powers stripped in Section 1, this gives the
complete factorization of \(N\).

## 3. Complexity

The base range (12) is polynomial in \(\log N\). The number of chain
entries is
\[
 \sum_{r\in\mathcal S}(1+v_r(E))
 \le |\mathcal S|+|\mathcal S|\log_2N. \tag{13}
\]
The exponent \(E\) has polynomial bit length by (4). Modular powering,
gcd, exact division, primality validation, and partition bookkeeping
are all polynomial in \(B\). Hence the whole deterministic algorithm
runs in time polynomial in (2).

The only unproved hypothesis used is GRH through (7). The completeness
of the support list in (1) is a separate input promise.
