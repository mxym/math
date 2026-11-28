# Proof

## 1. Support preprocessing

Construct the fully factored exponent multiple
\[
 E=\prod_{\substack{r\in\mathcal S\\r\le N}}
 r^{\lfloor\log_rN\rfloor}. \tag{4}
\]
The support promise implies
\[
 \lambda(N)\mid E,\qquad \log E\le|\mathcal S|\log N. \tag{5}
\]
Validate every entry of \(\mathcal S\) as prime and divide its full
power out of \(N\).

The remaining integer is squarefree. Indeed, if \(p^a\) survived with
\(a\ge2\), then \(p\mid\lambda(p^a)\mid\lambda(N)\), so (1) would have
listed \(p\) and its full power would already have been removed.

For an ordinary base \(u\), current blocks are refined by saturation
\[
 \gcd(D,u^{\lceil\log_2D\rceil}) \tag{6}
\]
and, on coprime blocks, by every known exponent chain
\[
 \gcd(u^{E/r^j}-1,D),
 \qquad r\in\mathcal S,\quad0\le j\le v_r(E). \tag{7}
\]

## 2. Fast removal of small factors

Put
\[
 L=\log N,\qquad \ell=\log L,
\]
and choose a small-factor cutoff \(Z=e^z\), with \(z\) fixed in
Section 5. The deterministic Pollard--Strassen product-tree method finds
a prime divisor at most \(Z\), or proves that none exists, in
\[
 Z^{1/2+o(1)}\operatorname{poly}(\log N) \tag{8}
\]
bit operations. Repeating after exact division costs only an additional
polynomial factor, because at most \(O(\log N)\) prime factors can be
removed.

Let \(M\) be the residual. It is squarefree and every prime divisor of
\(M\) exceeds \(Z\). If \(t=\omega(M)\), then
\[
 Z^t<M\le N,\qquad t<\frac{L}{z}. \tag{9}
\]

## 3. Smooth-subgroup base scan

Choose a base budget \(y=e^s\) and put
\[
 T=\exp\!\left(\frac{L\ell}{s}\right). \tag{10}
\]
Scan all ordinary bases through \(y\), refining blocks by (6)--(7).

For distinct residual primes \(p,q\), write
\[
 g=\gcd(p-1,q-1),\qquad
 A=\frac{p-1}{g},\qquad B=\frac{q-1}{g}. \tag{11}
\]
Then \(\gcd(A,B)=1\). Suppose \(A>T\). In
\(\mathbb F_p^\times\), the subgroup
\[
 H=\{x:x^g=1\}
\]
has \(g=(p-1)/A\) elements. The Konyagin--Pomerance estimate gives
\[
 \Psi(p-1,y)>
 (p-1)^{1-\log\log(p-1)/\log y}>g, \tag{12}
\]
with the elementary full-residue scan covering the case \(y\ge p-1\).
Consequently some prime base \(u\le y\) lies outside \(H\).

If \(u=q\), saturation separates the pair. Otherwise
\(\operatorname{ord}_p(u)\nmid g\), so for some prime \(r\mid A\),
\[
 v_r(\operatorname{ord}_p(u))>v_r(g). \tag{13}
\]
Coprimality in (11) gives
\[
 v_r(\operatorname{ord}_q(u))\le v_r(q-1)=v_r(g). \tag{14}
\]
The prime \(r\) divides \(\lambda(N)\), hence belongs to
\(\mathcal S\), and one of the chains (7) detects the difference.
The same argument applies when \(B>T\).

Therefore every pair of primes left in one block after the base scan
satisfies
\[
 A\le T,\qquad B\le T. \tag{15}
\]

## 4. Reconstructing unresolved blocks

Let
\[
 D=p_1p_2\cdots p_m
\]
be one unresolved block. By (9), \(m<L/z\). For \(i\ge2\), reduce
\[
 \frac{p_i-1}{p_1-1}=\frac{a_i}{b_i},
 \qquad \gcd(a_i,b_i)=1. \tag{16}
\]
Equation (15) gives
\[
 1\le a_i,b_i\le T. \tag{17}
\]

The algorithm tries every \(m\le\lceil L/z\rceil\) and every ordered
tuple of coprime pairs in (17). For one tuple define
\[
 F(X)=(X+1)\prod_{i=2}^m(a_iX+b_i),\qquad
 C=D\prod_{i=2}^mb_i. \tag{18}
\]
The polynomial \(F\) is strictly increasing for integers \(X\ge0\), so
binary search decides in polynomial time whether \(F(X)=C\) has a
positive integer solution. For the true tuple, \(X=p_1-1\), and
\[
 p_i=\frac{a_iX}{b_i}+1 \tag{19}
\]
recovers the complete block after integrality, primality, distinctness,
and product checks.

The number of tuples is bounded by
\[
 T^{2(m-1)}
 \le
 \exp\!\left(\frac{2L^2\ell}{zs}\right). \tag{20}
\]
The sum over all possible block sizes and blocks changes this by only a
polynomial factor.

## 5. Three-way balance

For fixed \(z\), balance the base scan and (20) by taking
\[
 s=L\sqrt{\frac{2\ell}{z}}. \tag{21}
\]
Both then have logarithmic cost exponent \(s\). The small-factor stage
(8) has exponent \(z/2+o(z)\). Balance these by choosing
\[
 z=2L^{2/3}\ell^{1/3},\qquad
 s=L^{2/3}\ell^{1/3}. \tag{22}
\]
Indeed,
\[
 \frac z2=s,\qquad
 \frac{2L^2\ell}{zs}=s. \tag{23}
\]
Thus small-factor removal, the base scan, and ratio reconstruction each
cost
\[
 \exp\!\left((1+o(1))
 L^{2/3}\ell^{1/3}\right). \tag{24}
\]
All exponent construction, gcd, modular powering, primality validation,
binary search, and bookkeeping costs are polynomial in \(B\). Safe
integer approximations to \(Z,y,T\) are computable in polynomial time,
and finitely many small cases are handled directly. This proves (2).

## 6. Finite verifier

The checker independently validates:

* support synthesis and \(\lambda(N)\mid E\);
* exact stripping at a finite cutoff and the residual-prime count;
* exponent-chain refinement for a finite base budget;
* rational-ratio reconstruction of all tested residual blocks;
* false-positive advice;
* complete removal of repeated prime powers.

The finite checker validates the structural reductions. It does not
replace either the analytic smooth-number bound (12) or the established
Pollard--Strassen complexity (8).
