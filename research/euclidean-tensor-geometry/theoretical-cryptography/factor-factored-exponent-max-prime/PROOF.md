# Proof

Put
\[
 \vartheta=\frac1{4\sqrt e}.
\]

## 1. Validate and strip the advised primes

Write the supplied factorization as
\[
 E=\prod_{i=1}^{u}r_i^{S_i}.
\]
Multiplication and deterministic primality testing validate the advice
in time polynomial in \(\log E\). There are at most \(\log_2 E\)
distinct \(r_i\)'s and \(\sum_i S_i\le\log_2E\).

For every \(r_i\), divide its exact power out of \(N\). Record these
prime-power factors and call the remaining integer \(M\). Thus every
prime \(p\mid M\) satisfies \(p\nmid E\).

The residual integer is squarefree. The prime \(2\) is removed because
\(E\) is even. If an odd \(p^a\mid N\) has \(a\ge2\), then
\[
 p^{a-1}\mid\lambda(p^a)\mid\lambda(N)\mid E,
\]
so \(p\mid E\), and the preliminary step would have removed it. Also,
for every \(p\mid M\),
\[
 p-1\mid\lambda(p)\mid\lambda(N)\mid E. \tag{1}
\]

## 2. Full valuation signatures are injective

For a residual prime \(p\), define
\[
 \mathbf s_E(p)=\bigl(v_r(p-1)\bigr)_{r\mid E,\ r\ {\rm prime}}. \tag{2}
\]
Every prime divisor of \(p-1\) occurs among the \(r_i\), by (1). Hence
\[
 p-1=\prod_{r\mid E}r^{\,v_r(p-1)}. \tag{3}
\]
Consequently, \(\mathbf s_E(p)=\mathbf s_E(q)\) implies \(p=q\).
Distinct residual primes therefore differ in at least one coordinate.

This uses only the listed prime factors of \(E\); it does not enumerate
the divisors of \(E\).

## 3. The multiradix power-gcd chains

Maintain \(M\) as pairwise coprime blocks. For an integer base \(b\) and
a block \(D\), first put
\[
 L=\lceil\log_2D\rceil,\qquad U=\gcd(D,b^L). \tag{4}
\]
More generally, if \(p^a\parallel D\), then \(p^a\mid U\) exactly when
\(p\mid b\), since \(a\le\log_2D\). Thus (4) never cuts through a
prime-power component.

On a complementary block coprime to \(b\), take a listed prime \(r\mid E\)
and write
\[
 E=r^S T,\qquad r\nmid T.
\]
Compute
\[
 d_{r,j}=\gcd\left(b^{E/r^j}-1,D\right),
 \qquad 0\le j\le S. \tag{5}
\]
If \(p\mid D\), let
\[
 \rho_{p,r}(b)=v_r(\operatorname{ord}_p(b)).
\]
The prime-to-\(r\) part of \(\operatorname{ord}_p(b)\) divides \(T\), so
\[
 p\mid d_{r,j}
 \quad\Longleftrightarrow\quad
 \rho_{p,r}(b)\le S-j. \tag{6}
\]
Therefore unequal \(r\)-parts of two local orders are separated by one
of the nested gcds in (5).

The algorithm scans \(b=2,3,\ldots\), applies (4)--(5) for every listed
prime \(r\mid E\), and uses deterministic primality tests on the current
blocks. Since \(M\) is squarefree, completion is reached exactly when
every residual block is prime.

## 4. A prime-conductor witness for every pair

Take distinct residual primes \(p,q\). Their signatures differ, so
choose \(r\mid E\) with
\[
 t_p=v_r(p-1)<t_q=v_r(q-1)
\]
after interchanging \(p,q\), and put \(d=t_q-t_p\ge1\).
Because \(r^d\mid q-1\), the cyclic character group modulo the prime
\(q\) contains a nonprincipal character \(\chi\) of exact order \(r^d\).
Its conductor is \(q\).

Choose a generator \(g\) of \(\mathbb F_q^\times\), write \(b=g^h\), and
normalize \(\chi(g)\) to be a primitive \(r^d\)-th root. Then
\[
 \chi(b)\ne1\quad\Longleftrightarrow\quad r^d\nmid h. \tag{7}
\]
If (7) holds, then \(v_r(h)<d\), and
\[
 \rho_{q,r}(b)
 =t_q-\min\{t_q,v_r(h)\}
 >t_q-d=t_p
 \ge \rho_{p,r}(b). \tag{8}
\]
Thus (6) separates \(p\) and \(q\), provided \(p\nmid b\).
If \(p\mid b\), the saturation step (4) separates them instead.

Lau--Wu's Theorem 1 says that, for every fixed \(\eta>0\), the least
positive integer \(n_\chi\) at which a nonprincipal character of
cube-free conductor \(Q\) has value outside \(\{0,1\}\) satisfies
\[
 n_\chi\ll_\eta Q^{\vartheta+\eta}. \tag{9}
\]
Here \(Q=q\) is prime. Since a nonprincipal character modulo a prime has
a nontrivial value among \(1,\ldots,q-1\), its least such integer is
coprime to \(q\). Therefore \(\chi(n_\chi)\ne1\), and the preceding
paragraph applies with \(b=n_\chi\). Moreover,
\[
 Q=q\le P_E(N). \tag{10}
\]

## 5. All pairs and the running time

For every unordered pair of residual primes, (9)--(10) give a
separating base at most
\[
 C_\eta P_E(N)^{\vartheta+\eta}. \tag{11}
\]
The algorithm applies the same scanned bases and all listed
\(r\)-chains to every current block. Once all bases through (11) have
been processed, no block can contain two distinct residual primes:
their pair witness would already have separated them. Hence every block
is prime, and the algorithm stops without knowing \(P_E(N)\).

The number of listed primes, the total number of chain levels, the
number of blocks, modular exponentiation, gcd, and primality testing all
cost a factor polynomial in \(\log N+\log E\). Choosing \(\eta\) below
the requested \(\varepsilon\) and absorbing the fixed implied constant
in (9) proves
\[
 P_E(N)^{1/(4\sqrt e)+\varepsilon}
 \operatorname{poly}_{\varepsilon}(\log N+\log E). \tag{12}
\]

Finally, if \(p\mid M\), then \(p-1\mid E\), so
\[
 P_E(N)\le E+1. \tag{13}
\]
The cases \(M=1\) and \(M\) prime are completed by the preliminary
division and primality test alone.

## 6. Finite verifier

The checker does not verify the analytic estimate (9). It verifies the
exact algebra around it:

* full signatures over the prime factors of \(E\) are injective on all
  residual primes;
* each differing coordinate produces a prime-conductor base whose
  \(r\)-order is strictly larger at the high-valuation prime;
* the nested chains completely refine thousands of squarefree supports;
* on arbitrary tested multiplicities, every repeated prime divides
  \(E\) and is removed, while the residual part is squarefree;
* every raw split preserves complete prime components.
