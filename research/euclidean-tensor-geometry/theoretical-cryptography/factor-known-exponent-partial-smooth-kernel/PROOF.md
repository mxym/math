# Proof

## 1. Extract only the small coordinates

Enumerate every prime \(r\le Y\) and compute
\[
 S_r=v_r(E)
\]
by repeated exact division. This costs
\(\operatorname{poly}(Y,\log E)\). For each such \(r\), divide its exact
power out of \(N\) and record the resulting prime-power factor. Call the
remaining integer \(M\). Every prime divisor of \(M\) is larger than
\(Y\), although \(M\) need not be squarefree.

For a current block \(D\) and ordinary base \(b\), first saturate the
primes dividing \(b\):
\[
 U=\gcd(D,b^{\lceil\log_2D\rceil}). \tag{1}
\]
This preserves complete prime-power components. On complementary
blocks coprime to \(b\), for every prime \(r\le Y\) compute
\[
 \gcd\left(b^{E/r^j}-1,D\right),
 \qquad 0\le j\le S_r. \tag{2}
\]

If \(p^a\parallel D\), put
\[
 \rho_{p,r}(b)=v_r(\operatorname{ord}_{p^a}(b)).
\]
Because \(p>Y\ge r\), the kernel of reduction
\[
 (\mathbb Z/p^a\mathbb Z)^\times
 \longrightarrow
 (\mathbb Z/p\mathbb Z)^\times
\]
is a \(p\)-group, so
\[
 \rho_{p,r}(b)=v_r(\operatorname{ord}_p(b)). \tag{3}
\]
Writing \(E=r^{S_r}T\), the prime-to-\(r\) part of the local order
divides \(T\), and hence
\[
 p^a\mid\gcd\left(b^{E/r^j}-1,D\right)
 \quad\Longleftrightarrow\quad
 \rho_{p,r}(b)\le S_r-j. \tag{4}
\]
Thus unequal known local order components split complete prime powers.

## 2. A partial-signature kernel

Take distinct prime divisors \(p,q\mid M\) and an admissible orientation
\(h\mid h'\). Put
\[
 m=M_Y(h\mid h')>1,\qquad x=h-1,\qquad k=x/m. \tag{5}
\]
The integer \(m\) divides \(x\). Indeed, its exponent at every small
prime \(r\le Y\) is at most \(v_r(h-1)\).

Consider the subgroup
\[
 H=\{z\in\mathbb F_h^\times:z^k=1\}. \tag{6}
\]
It has exactly \(k\) elements. If
\[
 \Psi(x,B)>k, \tag{7}
\]
then, exactly as in the full smooth-kernel argument, some prime
\(\ell\le B\) lies outside \(H\): otherwise every \(B\)-smooth integer
at most \(x\) would give a distinct element of the size-\(k\) subgroup.
When \(B\ge h\), the elementary count among \(1,\ldots,k+1<h\) gives an
ordinary base outside \(H\) instead.

Choose a witness base \(b<h\). If \(h'\mid b\), saturation (1) separates
the pair. Otherwise
\[
 \operatorname{ord}_h(b)\nmid k. \tag{8}
\]
Hence some prime \(r\) satisfies
\[
 v_r(\operatorname{ord}_h(b))>v_r(k). \tag{9}
\]
For primes \(r>Y\), the definition (5) gives
\(v_r(k)=v_r(h-1)\), so (9) is impossible. Therefore \(r\le Y\).
Moreover, (9) can hold only when
\[
 v_r(h-1)>v_r(h'-1),
\]
in which case the definition of \(m\) gives
\[
 v_r(k)=v_r(h'-1). \tag{10}
\]
Lagrange's theorem and the lift identity (3) yield
\[
 \rho_{h',r}(b)
 \le v_r(h'-1)
 =v_r(k)
 <\rho_{h,r}(b). \tag{11}
\]
The known chain (2)--(4) separates the complete prime-power components
over \(h\) and \(h'\).

## 3. The fixed-\(\delta\) bound

Assume every pair has an admissible orientation satisfying
\[
 m=M_Y(h\mid h')\ge(h-1)^\delta. \tag{12}
\]
Then
\[
 k=\frac{h-1}{m}\le(h-1)^{1-\delta}. \tag{13}
\]

Choose any fixed \(A>1/\delta\) and let
\[
 B=\left\lceil(\log N)^A\right\rceil. \tag{14}
\]
If \(B\ge h-1\), the elementary subgroup count gives a witness by \(B\).
Otherwise, with \(x=h-1\ge4\), the Konyagin--Pomerance estimate gives
\[
 \Psi(x,B)>x^{1-\log\log x/\log B}. \tag{15}
\]
Since \(x<N\),
\[
 \frac{\log\log x}{\log B}\le\frac1A<\delta. \tag{16}
\]
Equations (13)--(16) imply \(\Psi(x,B)>k\). Section 2 therefore supplies
a separating base by \(B\) for every pair.

After all these bases are processed, every current block contains only
one distinct prime. Deterministic prime-power recognition returns that
prime and its multiplicity. There are \(O(\log N)\) blocks, \(O(Y)\) enumerated primes, and
\(O(Y+\log E)\) total chain levels. Every modular
exponentiation, gcd, saturation, and certification has cost polynomial
in \(Y,\log N+\log E\). Multiplication by the base budget (14) proves the
claim.

## 4. Finite verifier

The checker uses only the small coordinates \(2,3,5,7\), without a
factorization of the rest of \(E\). It independently verifies:

* exact oriented indices \(M_Y(h\mid h')\) and subgroup sizes;
* exact smooth-number counts and small prime witnesses outside each
  subgroup;
* the fixed profile threshold \(\delta=1/4\);
* complete refinement for all qualifying squarefree supports and
  nontrivial exponent multiples;
* prime-power lift invariance and preservation of complete components
  for qualifying arbitrary-multiplicity inputs.
