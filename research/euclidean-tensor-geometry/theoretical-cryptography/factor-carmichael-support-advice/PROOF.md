# Proof

## 1. Synthesizing a factored exponent multiple

Validate the entries of \(\mathcal S\) as distinct primes and discard
entries larger than \(N\). For each remaining \(r\), compute the largest
power \(r^{a_r}\le N\) by repeated exact multiplication. This gives the
complete factorization
\[
 E=E_{\mathcal S}(N)=\prod_{r\in\mathcal S,\ r\le N}r^{a_r},
 \qquad a_r=\lfloor\log_rN\rfloor. \tag{5}
\]

If \(r^t\parallel\lambda(N)\), then \(r\in\mathcal S\) by the promise and
\[
 r^t\le\lambda(N)\le\varphi(N)\le N.
\]
Consequently \(t\le a_r\). This holds for every prime divisor of
\(\lambda(N)\), so
\[
 \lambda(N)\mid E. \tag{6}
\]
Moreover,
\[
 \log E=\sum_r a_r\log r\le|\mathcal S|\log N, \tag{7}
\]
and \(\sum_r a_r\le|\mathcal S|\log_2N\). Hence (5), its complete
factorization, and all exponent chains below have polynomial input
size. False-positive primes in \(\mathcal S\) only enlarge \(E\); they
do not invalidate (6).

## 2. Remove advised prime divisors

For every \(r\in\mathcal S\), exact division removes the full \(r\)-power
from \(N\). Let \(M\) be the residual integer.

The residual \(M\) is squarefree. Indeed, if \(p^a\mid M\) with
\(a\ge2\), then \(p\mid\lambda(p^a)\mid\lambda(N)\), including the
usual \(2\)-power cases. The promise would imply \(p\in\mathcal S\),
contrary to \(p\mid M\).

For every prime \(p\mid M\), all prime divisors of \(p-1\) belong to
\(\mathcal S\), because \(p-1=\lambda(p)\mid\lambda(N)\).

## 3. Complete signatures are injective

For \(p\mid M\), define the support signature
\[
 \sigma(p)=\bigl(v_r(p-1)\bigr)_{r\in\mathcal S}. \tag{8}
\]
If distinct primes \(p,q\mid M\) had equal signatures, then both
\(p-1\) and \(q-1\) would be \(\mathcal S\)-smooth and their complete
prime factorizations would agree. Thus \(p-1=q-1\), a contradiction.
Therefore every pair of residual primes differs in at least one
coordinate of (8).

## 4. A bounded ordinary base separates every pair

Fix distinct \(p,q\mid M\). Choose \(r\in\mathcal S\) for which, after
possibly interchanging \(p,q\),
\[
 \alpha=v_r(p-1)>\beta=v_r(q-1). \tag{9}
\]
Because \(\mathbb F_p^\times\) is cyclic, it has a multiplicative
character \(\chi\) of exact order \(r^{\alpha-\beta}\). Its modulus is
the prime \(p\), so it is nonprincipal and primitive.

For \(b\not\equiv0\pmod p\), write \(b=g^t\) for a generator \(g\).
Then
\[
 \chi(b)\ne1
 \quad\Longrightarrow\quad
 r^{\alpha-\beta}\nmid t
 \quad\Longrightarrow\quad
 v_r(\operatorname{ord}_p(b))>\beta. \tag{10}
\]
Lau--Wu's cube-free-modulus theorem supplies, for every fixed
\(\varepsilon>0\), a positive integer
\[
 b\ll_\varepsilon p^{1/(4\sqrt e)+\varepsilon} \tag{11}
\]
with \(\chi(b)\notin\{0,1\}\). Since a nonprincipal character
modulo the prime \(p\) has a nontrivial value on some residue in
\(\{1,\ldots,p-1\}\), its least such \(b\) is smaller than \(p\);
hence \(\chi(b)\ne0\). If \(q\mid b\), then the gcd refinement at the start of Section 5
already separates the \(q\)-component from the \(p\)-component,
because \(p\nmid b\). Thus, for the remaining order comparison we may
assume \(q\nmid b\). Equation (10) and Lagrange's theorem then give
\[
 v_r(\operatorname{ord}_p(b))
   >\beta
   \ge v_r(\operatorname{ord}_q(b)). \tag{12}
\]

## 5. Multiradix gcd splitting

For a current block \(D\) and an ordinary base \(b\), first compute
\[
 U=\gcd\!\left(D,b^{\lceil\log_2D\rceil}\right). \tag{13}
\]
Every prime dividing \(b\) occurs in \(U\) with its full exponent in
\(D\), so (13) never tears a prime-power component.

On blocks coprime to \(b\), write \(S_r=v_r(E)\) and compute
\[
 \gcd\!\left(b^{E/r^j}-1,D\right),
 \qquad r\in\mathcal S,\quad 0\le j\le S_r. \tag{14}
\]
For \(p^a\parallel D\), put
\(\rho_{p,r}(b)=v_r(\operatorname{ord}_{p^a}(b))\).
Since \(\operatorname{ord}_{p^a}(b)\mid E\),
\[
 p^a\mid\gcd(b^{E/r^j}-1,D)
 \quad\Longleftrightarrow\quad
 \rho_{p,r}(b)\le S_r-j. \tag{15}
\]
Thus (12) is detected by one cut in (14), and the whole components over
\(p\) and \(q\) separate.

Scan ordinary bases in increasing order, refining all current blocks by
(13)--(14). Equations (8)--(12) imply that by
\[
 O_\varepsilon\!\left(
 P_{\mathcal S}(N)^{1/(4\sqrt e)+\varepsilon}\right)
\]
every pair of distinct residual primes has separated. Each surviving
block is therefore a prime power; deterministic prime-power recognition
recovers its prime and multiplicity.

There are \(O(\log N)\) blocks and
\(\sum_r(S_r+1)=\operatorname{poly}(|\mathcal S|,\log N)\) chain cuts
per base. Modular exponentiation uses an exponent of bit length bounded
by (7). Together with primality validation, gcds, exact division, and
prime-power recognition, this proves (4).

## 6. Finite verifier

The checker does not assume the theorem's conclusion. It independently:

* factors small test inputs only to construct promised advice;
* adds false-positive support primes;
* rebuilds \(E_{\mathcal S}(N)\) and checks
  \(\lambda(N)\mid E_{\mathcal S}(N)\);
* verifies signature injectivity and explicit prime-conductor witnesses;
* replays all gcd-chain refinements;
* checks arbitrary prime multiplicities and that every cut preserves
  complete prime-power components.

The finite computation is validation, not a substitute for the analytic
least-character-nonresidue theorem used in (11).
