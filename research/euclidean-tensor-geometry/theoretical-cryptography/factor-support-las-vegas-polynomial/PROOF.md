# Proof

## 1. From support to an exponent multiple

After primality validation and deduplication of \(\mathcal S\), set
\[
 E=\prod_{\substack{r\in\mathcal S\\r\le N}}
 r^{\lfloor\log_rN\rfloor}. \tag{3}
\]
For every \(p^a\parallel N\), all prime divisors of
\(\lambda(p^a)\) lie in \(\mathcal S\), and
\(\lambda(p^a)\le p^a\le N\). Hence each prime-power exponent required
by \(\lambda(p^a)\) occurs in (3), so
\[
 \lambda(N)\mid E,\qquad \log E\le|\mathcal S|\log N. \tag{4}
\]

Divide the full power of every listed prime out of \(N\). The residual
\(M\) is squarefree: if \(p^a\mid M\) with \(a\ge2\), then
\(p\mid\lambda(p^a)\mid\lambda(N)\), so \(p\in\mathcal S\), a
contradiction.

## 2. One randomized split

Let \(M\) be squarefree and composite. Sample \(a\) uniformly modulo
\(M\). If \(1<\gcd(a,M)<M\), a proper factor is already found. The
single residue \(a=0\) is discarded. We may therefore analyze a uniform
unit.

Write \(E=2^st\) with \(t\) odd. Since \(E\) is a multiple of
\(\lambda(M)\), the sequence
\[
 x_i=a^{t2^i}\pmod M,\qquad 0\le i\le s, \tag{5}
\]
ends at \(1\). Let \(x_{i-1}\) precede the first \(1\) (unless \(x_0=1\)).
Compute \(\gcd(x_{i-1}-1,M)\); it is a proper factor whenever the CRT
components do not all reach \(1\) at the same step.

It remains to bound the failure probability. For each prime \(p\mid M\)
put
\[
 h_p=v_2(\operatorname{ord}_p(a)). \tag{6}
\]
Under CRT the components of a uniform unit are independent. For odd
\(p\), write \(e_p=v_2(p-1)\). Cyclicity of
\(\mathbb F_p^\times\) gives the exact law
\[
 \Pr(h_p=0)=2^{-e_p},\qquad
 \Pr(h_p=k)=2^{k-1-e_p}\quad(1\le k\le e_p). \tag{7}
\]
Every atom in (7) is at most \(1/2\). For \(p=2\), \(h_2=0\)
deterministically.

The sequence (5) fails precisely when all \(h_p\) are equal. A
squarefree composite has at least one odd prime factor, so conditioning
on all other CRT components and using the largest atom of one odd
component,
\[
 \Pr(\text{failure}\mid a\in(\mathbb Z/M\mathbb Z)^\times)
 =\Pr(h_p\text{ all equal})\le\frac12. \tag{8}
\]
Thus every unit trial succeeds with probability at least \(1/2\).
Nonunits other than zero only improve the probability by yielding a
gcd factor.

## 3. Complete factorization and complexity

Repeat the split until it succeeds, then recurse on the two factors.
Primality testing and exact division prevent false outputs. There are
at most \(O(\log N)\) successful recursive splits. Each split needs an
expected constant number of trials by (8).

The bit length of \(E\) is polynomial in \(B\) by (4). Each modular
power, gcd, primality test, advice validation, and random sampling step
therefore has polynomial bit complexity. The whole algorithm is Las
Vegas with expected running time polynomial in \(B\), and its returned
factorization is always exact.

No analytic hypothesis is used.
