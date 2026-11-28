# Proof

## 1. Advice preprocessing and squarefree residual

Construct the completely factored multiple
\[
 E=\prod_{\substack{r\in\mathcal S\\r\le N}}
 r^{\lfloor\log_rN\rfloor}. \tag{4}
\]
The support promise implies
\[
 \lambda(N)\mid E,\qquad \log E\le|\mathcal S|\log N. \tag{5}
\]
Validate the prime list and divide every listed prime out of \(N\) with
its full multiplicity. Let \(M\) be the residual.

The residual is squarefree. If \(p^a\mid M\) with \(a\ge2\), then
\(p\mid\lambda(p^a)\mid\lambda(N)\), so (1) would put \(p\) in
\(\mathcal S\), contrary to the construction of \(M\). Thus all repeated
prime powers have already been completely factored, and \(M\) is a
product of at most \(K\) distinct primes.

For an ordinary base \(u\), first saturate prime divisors of \(u\) by
\[
 \gcd(D,u^{\lceil\log_2D\rceil}) \tag{6}
\]
inside every current block \(D\). On coprime blocks, process all chains
\[
 \gcd(u^{E/r^j}-1,D),
 \qquad r\in\mathcal S,\quad0\le j\le v_r(E). \tag{7}
\]
Unequal \(r\)-adic components of local multiplicative orders are
detected by (7).

## 2. Pairwise large-coordinate exit

Choose a base budget \(y>e\), and put
\[
 L=\log N,\qquad s=\log y,\qquad
 T=\exp\!\left(\frac{L\log L}{s}\right). \tag{8}
\]
For distinct residual primes \(p,q\), write
\[
 g_{pq}=\gcd(p-1,q-1),\qquad
 A_{pq}=\frac{p-1}{g_{pq}},\qquad
 B_{pq}=\frac{q-1}{g_{pq}}. \tag{9}
\]
The two coordinates in (9) are coprime.

Suppose \(A_{pq}>T\); the other case is symmetric. In
\(\mathbb F_p^\times\), the subgroup
\[
 H=\{z:z^{g_{pq}}=1\}
\]
has \(g_{pq}\) elements. If \(y<p-1\), the
Konyagin--Pomerance estimate and (8) give
\[
 \Psi(p-1,y)>
 (p-1)^{1-\log\log(p-1)/\log y}
 >
 \frac{p-1}{A_{pq}}=g_{pq}. \tag{10}
\]
If \(y\ge p-1\), the same escape follows by scanning all residues.
Hence some prime \(\ell\le y\) lies outside \(H\).

If \(\ell=q\), saturation (6) separates the pair. Otherwise
\(\operatorname{ord}_p(\ell)\nmid g_{pq}\), so for some
\(r\mid A_{pq}\),
\[
 v_r(\operatorname{ord}_p(\ell))>v_r(g_{pq}). \tag{11}
\]
Coprimality in (9) gives
\[
 v_r(q-1)=v_r(g_{pq}),
\]
and therefore
\[
 v_r(\operatorname{ord}_q(\ell))\le v_r(g_{pq}). \tag{12}
\]
The prime \(r\) divides \(\lambda(N)\), hence belongs to
\(\mathcal S\), and (7) detects (11)--(12).

After scanning every base through \(y\), two primes can remain in the
same current block only if
\[
 A_{pq}\le T\quad\text{and}\quad B_{pq}\le T. \tag{13}
\]

## 3. Reconstructing a remaining block

Let a remaining squarefree block be
\[
 D=p_1p_2\cdots p_t,\qquad 2\le t\le K.
\]
For each \(i\ge2\), reduce the ratio
\[
 \frac{p_i-1}{p_1-1}=\frac{a_i}{b_i},
 \qquad \gcd(a_i,b_i)=1. \tag{14}
\]
By (13),
\[
 1\le a_i,b_i\le T. \tag{15}
\]

The algorithm does not know the ordering in (14). It tries every
\(t\in\{2,\ldots,K\}\) and every ordered tuple of coprime pairs
\[
 (a_i,b_i)\in[1,\lceil T\rceil]^2,\qquad 2\le i\le t. \tag{16}
\]
For one tuple, consider
\[
 F(X)=(X+1)\prod_{i=2}^t(a_iX+b_i),\qquad
 C=D\prod_{i=2}^tb_i. \tag{17}
\]
All coefficients of \(F\) are positive, so \(F(X)\) is strictly
increasing for integers \(X\ge0\). Binary search therefore decides in
polynomial time whether
\[
 F(X)=C \tag{18}
\]
has a positive integer solution.

For the true tuple (14), \(X=p_1-1\) satisfies (18). The candidates
\[
 p_1=X+1,\qquad
 p_i=\frac{a_iX}{b_i}+1 \quad(i\ge2) \tag{19}
\]
are checked for integrality, distinct primality, and product \(D\).
Thus the correct tuple completely factors the block.

The number of tuples for a \(t\)-prime block is at most
\[
 T^{2(t-1)}\le T^{2(K-1)}, \tag{20}
\]
with polynomial work per tuple. No divisor enumeration of \(E\) or
\(\lambda(N)\) is used.

## 4. Complexity balance

Choose
\[
 s=\sqrt{2(K-1)L\log L},\qquad y=\lceil e^s\rceil. \tag{21}
\]
The base-scan branch has logarithmic cost exponent
\[
 \log y=(1+o(1))\sqrt{2(K-1)L\log L}. \tag{22}
\]
By (8) and (20), the reconstruction branch has exponent
\[
 2(K-1)\log T
 =\frac{2(K-1)L\log L}{s}
 =\sqrt{2(K-1)L\log L}. \tag{23}
\]
All exponent-chain, gcd, primality, perfect-power, binary-search, and
advice-validation costs are polynomial in \(B\) for fixed \(K\).
Safe integer ceilings for (8) and (21) are computable with standard
high-precision arithmetic; finitely many small inputs are handled by
trial division. Equations (22)--(23) prove (2).

## 5. Finite verifier

The checker independently verifies:

* exact support synthesis and \(\lambda(N)\mid E\);
* multiradix refinement over a finite base budget;
* explicit blocks not separated by base \(2\);
* the pairwise subgroup-obstruction condition in those blocks;
* monotone-polynomial recovery for all tested two- and three-prime
  inputs and curated four-prime inputs;
* complete stripping of repeated prime powers.

The finite computation checks the algebra and both exits. It is not a
substitute for the smooth-number estimate used in (10).
