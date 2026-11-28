# Proof

## 1. Preprocessing and the chains

Write the supplied factorization as
\[
 E=\prod_{i=1}^{u}r_i^{S_i}.
\]
Validate it by multiplication and deterministic primality testing.
For every listed \(r_i\), divide its exact power out of \(N\) and record
that prime-power factor. Call the remaining integer \(M\).

Every prime \(p\mid M\) satisfies \(p\nmid E\), and \(M\) is squarefree.
The prime \(2\) was removed because \(E\) is even. If an odd
\(p^a\mid N\) has \(a\ge2\), then
\[
 p^{a-1}\mid\lambda(p^a)\mid\lambda(N)\mid E,
\]
so \(p\) was also removed. Finally,
\[
 p-1\mid\lambda(p)\mid E \qquad(p\mid M). \tag{1}
\]

Maintain \(M\) as pairwise coprime blocks. For each ordinary integer
base \(b=2,3,\ldots\) and block \(D\), first saturate the primes dividing
the base:
\[
 U=\gcd(D,b^L),\qquad L=\lceil\log_2D\rceil. \tag{2}
\]
If \(p^a\parallel D\), then \(p^a\mid U\) exactly when \(p\mid b\);
thus (2) preserves complete prime-power components.

On a complementary block coprime to \(b\), for every \(r_i\mid E\)
write \(E=r_i^{S_i}T_i\) and compute
\[
 d_{i,j}=\gcd\left(b^{E/r_i^j}-1,D\right),
 \qquad 0\le j\le S_i. \tag{3}
\]
For \(p\mid D\), put
\[
 \rho_{p,i}(b)=v_{r_i}(\operatorname{ord}_p(b)).
\]
Because the prime-to-\(r_i\) part of the order divides \(T_i\),
\[
 p\mid d_{i,j}
 \quad\Longleftrightarrow\quad
 \rho_{p,i}(b)\le S_i-j. \tag{4}
\]
Hence unequal local \(r_i\)-order components are separated by one of
the nested gcds.

## 2. The GCD-kernel pair lemma

Take distinct residual primes \(p,q\mid M\) and set
\[
 g=\gcd(p-1,q-1). \tag{5}
\]
Since \(p-1\ne q-1\), at least one fails to divide the other. Orient the
pair so that
\[
 q-1\nmid p-1. \tag{6}
\]
Then \(g\) is a proper divisor of \(q-1\), so
\[
 g\le\frac{q-1}{2},\qquad g+1<q. \tag{7}
\]

The cyclic group \(\mathbb F_q^\times\) has exactly \(g\) solutions to
\(x^g=1\). The \(g+1\) distinct nonzero residues represented by
\[
 1,2,\ldots,g+1
\]
cannot all be solutions. Thus there is an integer \(b\) with
\[
 2\le b\le g+1,\qquad b^g\not\equiv1\pmod q. \tag{8}
\]
In particular, \(\operatorname{ord}_q(b)\nmid g\).

Suppose first that \(p\nmid b\). Some prime \(r\) satisfies
\[
 v_r(\operatorname{ord}_q(b))>v_r(g). \tag{9}
\]
Because the left side is at most \(v_r(q-1)\), (9) implies
\[
 v_r(q-1)>v_r(g)=v_r(p-1). \tag{10}
\]
The last equality follows from the definition of the gcd when the
\(q-1\) valuation is larger. Lagrange's theorem at \(p\) gives
\[
 v_r(\operatorname{ord}_p(b))
 \le v_r(p-1)
 <v_r(\operatorname{ord}_q(b)). \tag{11}
\]
By (1), \(r\mid E\), and the corresponding chain (3)--(4) separates
\(p\) and \(q\).

If \(p\mid b\), then \(q\nmid b\) by (7)--(8), and the saturation step
(2) separates the pair directly.

This proves that every pair has a separating scanned base at most
\[
 \gcd(p-1,q-1)+1. \tag{12}
\]

## 3. All pairs and complexity

After every base through \(G_E(N)\) has been processed, no current block
can contain two distinct residual primes: their witness from (12) would
already have separated them. Since \(M\) is squarefree, deterministic
primality testing recognizes every remaining block as prime, and the
recorded preliminary factors complete the factorization of \(N\).

There are at most \(O(\log N)\) blocks. The number of listed primes and
the total number of chain levels are at most \(O(\log E)\). Modular
exponentiation, gcds, saturation, and primality testing therefore cost
a factor polynomial in \(\log N+\log E\) per scanned base. The claimed
bound follows.

For residual primes \(p_1<\cdots<p_k\),
\[
 \gcd(p_i-1,p_j-1)+1\le\min\{p_i,p_j\}.
\]
Taking the maximum over pairs gives
\[
 G_E(N)\le p_{k-1}. \tag{13}
\]

Finally, the same scanning algorithm also satisfies the independent
stopping bound
\[
 P_E(N)^{1/(4\sqrt e)+\varepsilon}
 \operatorname{poly}_{\varepsilon}(\log N+\log E)
\]
from the pinned prime-conductor theorem. It therefore stops by the
minimum of that bound and the present \(G_E(N)\) bound, proving the
hybrid estimate in the README.

## 4. Finite verifier

The checker does not verify the analytic Lau--Wu term in the optional
hybrid bound. It verifies the elementary theorem for exact bounded
families and nontrivial multiples of the exponent:

* the subgroup kernel contains exactly the tested bases satisfying
  \(b^g=1\), and a witness occurs by \(g+1\);
* every witness either saturates one endpoint or creates a strict local
  prime-adic order difference;
* all residual pairs are separated by the claimed maximum;
* the dynamic chains completely refine every tested residual support;
* arbitrary multiplicities are stripped correctly and every raw split
  preserves complete prime components.
