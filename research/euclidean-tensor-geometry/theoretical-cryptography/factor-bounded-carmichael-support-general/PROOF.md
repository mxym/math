# Proof

Write
\[
 N=\prod_{i=1}^t p_i^{a_i} \tag{6}
\]
with distinct primes \(p_i\). For every odd \(p_i\),
\[
 \lambda(p_i^{a_i})=p_i^{a_i-1}(p_i-1)
 \quad\text{and}\quad
 \lambda(p_i^{a_i})\mid\lambda(N). \tag{7}
\]
Therefore every prime divisor of \(p_i-1\) belongs to
\(\operatorname{supp}(\lambda(N))\), and hence to \(\mathcal S\).
Moreover \(p_i-1<N\), so if
\[
 p_i-1=\prod_{r\in\mathcal S}r^{e_{i,r}}, \tag{8}
\]
then
\[
 0\le e_{i,r}\le\lfloor\log_rN\rfloor. \tag{9}
\]
Thus the enumeration (5) contains \(d=p_i-1\), and its candidate
\(d+1\) is exactly \(p_i\). The prime \(2\) is also found, because the
all-zero exponent vector gives \(d=1\).

Whenever a candidate \(c=d+1\) is both prime and divides the current
cofactor, divide out the largest power of \(c\). This operation is
always correct. By the preceding paragraph it eventually processes
every distinct prime in (6), and the recorded valuations recover every
multiplicity \(a_i\). Hence the output is the complete factorization.

There are at most
\[
 \prod_{\substack{r\in\mathcal S\\r\le N}}
 (1+\lfloor\log_rN\rfloor)=C(N,\mathcal S) \tag{10}
\]
exponent vectors. Products exceeding \(N-1\) may be pruned, but this is
not needed for the bound. Candidate construction, deterministic
primality testing, exact division, and valuation extraction all have
bit complexity polynomial in
\[
 B=\log N+|\mathcal S|+\sum_{r\in\mathcal S}\log r. \tag{11}
\]
This proves (3).

If \(|\mathcal S|\le k\), every factor in (10) is at most
\(1+\log_2N\), which gives (4). No probabilistic or analytic hypothesis
is used.
