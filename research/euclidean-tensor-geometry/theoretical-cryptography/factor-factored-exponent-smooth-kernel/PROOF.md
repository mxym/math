# Proof

## 1. The standard factored-exponent chains

Validate the supplied factorization
\[
 E=\prod_i r_i^{S_i},
\]
remove from \(N\) the exact powers of every listed \(r_i\), and call the
remaining integer \(M\). The residual integer is squarefree: \(2\) is
listed because \(E\) is even, while an odd repeated factor
\(p^a\mid N\), \(a\ge2\), satisfies
\[
 p^{a-1}\mid\lambda(p^a)\mid E.
\]
Every residual prime also satisfies
\[
 p-1\mid E. \tag{1}
\]

For each scanned ordinary base \(b\), first saturate primes dividing the
base with
\[
 U=\gcd(D,b^{\lceil\log_2D\rceil}) \tag{2}
\]
on every current block \(D\). On complementary blocks coprime to \(b\),
for every \(r_i\mid E\) compute
\[
 \gcd\left(b^{E/r_i^j}-1,D\right),
 \qquad 0\le j\le S_i. \tag{3}
\]
If
\[
 \rho_{p,i}(b)=v_{r_i}(\operatorname{ord}_p(b)),
\]
then
\[
 p\mid\gcd\left(b^{E/r_i^j}-1,D\right)
 \quad\Longleftrightarrow\quad
 \rho_{p,i}(b)\le S_i-j. \tag{4}
\]
Thus unequal local \(r_i\)-order components are separated.

## 2. The smooth-kernel pair lemma

Take distinct residual primes \(p,q\), put
\[
 g=\gcd(p-1,q-1),
\]
and choose an admissible endpoint \(h\in\{p,q\}\). Let \(h'\) be the
other endpoint. Admissibility means \(h-1\nmid h'-1\), so \(g<h-1\).

The subgroup
\[
 H=\{x\in\mathbb F_h^\times:x^g=1\} \tag{5}
\]
has exactly \(g\) elements. If \(B\ge h\), the elementary count among
\(1,\ldots,g+1\) already supplies a base outside \(H\), because
\(g+1\le h-1\). Hence suppose \(B<h\) and
\[
 \Psi(h-1,B)>g. \tag{6}
\]
If every prime \(\ell\le B\) lay in \(H\), then every \(B\)-smooth
integer \(n\le h-1\), being a product of those primes, would also lie in
\(H\). The integers \(1,\ldots,h-1\) represent distinct nonzero residues
modulo \(h\), so (6) would put more than \(g\) distinct elements in
\(H\), a contradiction.

Therefore some prime
\[
 \ell\le B,\qquad \ell^g\not\equiv1\pmod h \tag{7}
\]
exists. If \(h'\mid\ell\), the saturated gcd (2) separates the pair;
notice that \(h\nmid\ell\) because \(\ell\le B<h\).
Assume henceforth that \(h'\nmid\ell\).

Equation (7) says
\[
 \operatorname{ord}_h(\ell)\nmid g.
\]
Hence some prime \(r\) has
\[
 v_r(\operatorname{ord}_h(\ell))>v_r(g). \tag{8}
\]
Since the left side is at most \(v_r(h-1)\), (8) forces
\[
 v_r(h-1)>v_r(g)=v_r(h'-1). \tag{9}
\]
Lagrange's theorem at \(h'\) now gives
\[
 v_r(\operatorname{ord}_{h'}(\ell))
 \le v_r(h'-1)
 <v_r(\operatorname{ord}_h(\ell)). \tag{10}
\]
By (1), \(r\mid E\), so the chain (3)--(4) separates the pair.

Consequently, if (6) holds for an admissible endpoint of every residual
pair, all pairs are separated after bases through \(B\), and the
squarefree residual blocks are prime.

## 3. The fixed-\(\delta\) polynomial class

Assume the condition in the README for a fixed \(\delta>0\). Choose any
fixed \(A>1/\delta\) and set
\[
 B=\left\lceil(\log N)^A\right\rceil. \tag{11}
\]
For a residual pair, select an admissible endpoint \(h\) for which
\[
 \frac{h-1}{g}\ge(h-1)^\delta,
 \qquad\text{so}\qquad
 g\le(h-1)^{1-\delta}. \tag{12}
\]

If \(B\ge h-1\), the elementary kernel count already gives a witness at
most \(g+1\le h-1\le B\). Otherwise put \(x=h-1\). For \(x\ge4\), the
Konyagin--Pomerance bound gives
\[
 \Psi(x,B)>x^{1-\log\log x/\log B}. \tag{13}
\]
Since \(x<N\),
\[
 \frac{\log\log x}{\log B}
 \le\frac1A<\delta. \tag{14}
\]
Combining (12)--(14) yields
\[
 \Psi(h-1,B)>(h-1)^{1-\delta}\ge g. \tag{15}
\]
The finitely many smaller \(x\) are handled directly. Section 2
therefore separates every pair by \(B\).

There are at most \(O(\log N)\) blocks, at most \(O(\log E)\) listed
prime factors and chain levels, and each modular exponentiation, gcd,
saturation, and primality test costs polynomial time in
\(\log N+\log E\). Multiplying by the polylogarithmic base budget (11)
proves the theorem.

## 4. Finite verifier

The checker independently enumerates bounded squarefree and
prime-power families, including nontrivial multiples of the exact
exponent. It verifies:

* exact values of \(\Psi(h-1,B)\);
* existence of a prime base outside the subgroup as soon as
  \(\Psi>g\);
* strict local-order separation or direct saturated separation;
* complete dynamic refinement of every residual support;
* preservation of complete prime components for arbitrary tested
  multiplicities;
* the profile exponent
  \(\log((h-1)/g)/\log(h-1)\) on every orientation.
