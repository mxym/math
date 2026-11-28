# Proof

Put
\[
 \vartheta=\frac1{4\sqrt e}.
\]

## 1. Strip the small primes

Enumerate the primes \(r\le z\) deterministically and remove their exact
powers from \(N\) by trial division. This costs a factor polynomial in
\(z\) and \(\log N\). Let \(M\) be the remaining odd part. Every prime
\(p\mid M\) satisfies \(p>z\), while the original \(E\) remains a
multiple of \(\lambda(M)\).

This preliminary step is important for arbitrary prime multiplicities:
for every enumerated \(r\le z\) and every \(p\mid M\), one has \(r\ne p\).
Thus the kernel of
\[
 (\mathbb Z/p^a\mathbb Z)^\times\longrightarrow
 (\mathbb Z/p\mathbb Z)^\times
\]
is a \(p\)-group and has order coprime to \(r\).

## 2. The multiradix chain

Maintain \(M\) as pairwise coprime blocks, each a product of complete
prime-power components. For an integer base \(b\) and a current block
\(D\), first saturate every shared prime:
\[
 U=\gcd(D,b^L),\qquad L=\lceil\log_2D\rceil.
\]
Then
\[
 U=\prod_{\substack{p^a\parallel D\\p\mid b}}p^a, \tag{2}
\]
so a proper \(U\) preserves the complete-component invariant.

On a complementary block coprime to \(b\), fix a prime \(r\le z\).
Write
\[
 E=r^S T,\qquad r\nmid T,
\]
and compute
\[
 d_{r,j}=\gcd\left(b^{E/r^j}-1,D\right),
 \qquad 0\le j\le S. \tag{3}
\]
For \(p^a\parallel D\), put
\[
 \rho_{p,r}(b)=v_r(\operatorname{ord}_{p^a}(b)).
\]
Since \(r\ne p\), reduction modulo \(p\) preserves the \(r\)-part:
\[
 \rho_{p,r}(b)=v_r(\operatorname{ord}_p(b)). \tag{4}
\]
The odd-to-\(r\) part of the local order divides \(T\), so
\[
 p^a\mid d_{r,j}
 \quad\Longleftrightarrow\quad
 \rho_{p,r}(b)\le S-j. \tag{5}
\]
Thus unequal \(r\)-parts are separated by one of the nested gcds.

For complete robustness, the implementation saturates each gcd in (3)
again as in (2) before refining. This is redundant after the small-prime
stripping, but directly verifies that no partial prime power enters the
partition.

The algorithm applies (3) for every prime \(r\le z\) and every base
\(b=2,3,\ldots\). It stops when deterministic primality and integer-root
tests certify every block as a prime power.

## 3. Different signatures: a prime-conductor character

Take distinct remaining primes \(p,q\). Suppose their signatures differ.
Choose a prime \(r\le z\) for which
\[
 t_p=v_r(p-1)<t_q=v_r(q-1),
\]
and put \(d=t_q-t_p\). Because \(r^d\mid q-1\), there is a Dirichlet
character \(\chi\) modulo \(q\) of exact order \(r^d\). Since \(q\) is
prime and \(\chi\) is nonprincipal, its conductor is \(Q=q\).

To see what a nontrivial character value means, choose a generator \(g\)
of \(\mathbb F_q^\times\), write \(b=g^h\), and normalize
\(\chi(g)\) to a primitive \(r^d\)-th root. Then
\[
 \chi(b)\ne1\quad\Longleftrightarrow\quad r^d\nmid h.
\]
If \(q\nmid b\) and this holds, then \(v_r(h)<d\), whence
\[
 \rho_{q,r}(b)
 =t_q-\min\{t_q,v_r(h)\}
 >t_q-d=t_p\ge\rho_{p,r}(b). \tag{6}
\]
If \(p\mid b\), saturation (2) separates the pair immediately. Otherwise
(5)--(6) separate it in the \(r\)-adic chain.

## 4. Equal signatures: the quadratic pair character

If \(\mathbf s_z(p)=\mathbf s_z(q)\), their \(r=2\) coordinates agree.
Use the primitive quadratic character
\[
 \chi(b)=\left(\frac bp\right)\left(\frac bq\right)
\]
of squarefree conductor \(Q=pq\). A value \(-1\) is a square modulo
exactly one of \(p,q\). Euler's criterion therefore makes the two
\(2\)-parts of the local orders unequal, and the \(r=2\) instance of
(5) separates the pair.

## 5. Lau--Wu and the all-pairs stopping bound

Lau--Wu's Theorem 1 states that, for every fixed \(\eta>0\), a
nonprincipal character of cube-free modulus \(Q\) has an integer
\[
 1\le b\ll_\eta Q^{\vartheta+\eta} \tag{7}
\]
whose character value lies outside \(\{0,1\}\).

In Section 3 the character has prime conductor and its nonzero values
are \(r\)-power roots of unity. Therefore a value outside \(\{0,1\}\)
is precisely a nontrivial value, and (6) applies. In Section 4 the
character is real quadratic, so the value is \(-1\).

For different-signature pairs, \(Q\) is one prime and is at most the
largest remaining prime. For equal-signature pairs, \(Q=pq\) is at most
the product of the two largest primes in that signature class. Hence
every pairwise conductor satisfies
\[
 Q\le H_z(N). \tag{8}
\]
Equations (7)--(8) give a separating base at most
\(C_\eta H_z(N)^{\vartheta+\eta}\) for every unordered pair.

After all bases through this bound have been processed, a current block
cannot contain two distinct primes: their pairwise witness would have
separated them. The complete-component invariant then says that all
blocks are prime powers. The algorithm recognizes this condition and
stops, without knowing \(H_z(N)\).

There are \(O(\log N)\) blocks. For each base and each prime \(r\le z\),
valuation extraction from \(E\), modular exponentiation, gcds,
saturation, and certification cost
\(\operatorname{poly}(z,\log N+\log E)\). Choose \(\eta\) below the
requested \(\varepsilon\) and absorb the fixed constant to obtain
\[
 H_z(N)^{1/(4\sqrt e)+\varepsilon}
 \operatorname{poly}_\varepsilon(z,\log N+\log E).
\]

## 6. Elementary corollaries

If the remaining primes are \(p_1<\cdots<p_k\), \(k\ge2\), then
\[
 H_z(N)\le p_{k-1}p_k\le\operatorname{rad}(N). \tag{9}
\]
Also \(p-1\mid\lambda(N)\mid E\), so
\[
 H_z(N)\le(E+1)^2. \tag{10}
\]
If all signatures are distinct, every class has size one and
\[
 H_z(N)=p_k\le E+1. \tag{11}
\]
Inputs with fewer than two remaining primes are already completely
handled by the small-prime step and deterministic prime-power
recognition.

## 7. Finite verifier

The checker does not verify the analytic estimate (7). It verifies the
surrounding exact claims for \(z=7\):

* prime-power-order inequalities for different-signature pairs;
* quadratic separation inside equal-signature classes;
* the conductor bound \(Q\le H_z(N)\);
* complete all-pairs refinement of thousands of squarefree supports;
* complete-prime-power preservation for arbitrary tested
  multiplicities;
* strict improvements over the \(r=2\)-only bottleneck.
