# Proof

Put
\[
 \vartheta=\frac{1}{4\sqrt e}.
\]
All occurrences of \(\varepsilon\) may be decreased by a fixed factor
when passing from a character conductor to \(N\).

## 1. The deterministic square-chain splitter

Let \(D\) be an odd divisor of the original input, and suppose that
\(E\) is a positive multiple of \(\lambda(D)\). Write
\[
 E=2^S T,\qquad T\ \text{odd}.
\]
For each integer \(a\), first compute \(\gcd(a,D)\). A proper gcd splits
\(D\). Otherwise, when the gcd is one, compute
\[
 d_j=\gcd\!\left(a^{E/2^j}-1,D\right),\qquad 0\le j\le S. \tag{1}
\]
The powers can be obtained by modular exponentiation and repeated
squaring; the cost per base is polynomial in \(\log D+\log E\).

For a prime power \(p^k\parallel D\), put
\[
 \rho_p(a)=v_2(\operatorname{ord}_{p^k}(a)).
\]
The kernel of
\[
 (\mathbb Z/p^k\mathbb Z)^\times\longrightarrow
 (\mathbb Z/p\mathbb Z)^\times
\]
is an odd \(p\)-group, so
\[
 \rho_p(a)=v_2(\operatorname{ord}_p(a)). \tag{2}
\]
The odd part of every local order divides \(T\). Hence
\[
 p^k\mid d_j\quad\Longleftrightarrow\quad
 \rho_p(a)\le S-j. \tag{3}
\]
Therefore, if the values \(\rho_p(a)\) are not all equal over the
distinct primes dividing \(D\), one of the gcds in (1) is proper. It
splits \(D\) into products of complete prime-power components.

## 2. A quadratic character that forces a split

For each prime \(p\mid D\), set
\[
 s_p=v_2(p-1).
\]
Euler's criterion gives
\[
 \left(\frac ap\right)=-1
 \quad\Longrightarrow\quad
 \rho_p(a)=s_p. \tag{4}
\]
Conversely, a quadratic residue has \(\rho_p(a)\le s_p-1\).

If the \(s_p\)'s are not all equal, choose a prime \(q\mid D\) in a
maximal layer and a prime \(p\mid D\) in a lower layer. The Legendre
symbol modulo \(q\) is a primitive nonprincipal character of conductor
\(Q=q\). Whenever its value at \(a\) is \(-1\), (4) gives
\(\rho_q(a)=s_q\), while \(\rho_p(a)\le s_p<s_q\). Thus (1) splits.

If all \(s_p\)'s are equal, choose distinct primes \(p,q\mid D\). The
product
\[
 \chi(a)=\left(\frac ap\right)\left(\frac aq\right)
\]
is a primitive nonprincipal character of conductor
\[
 Q=pq. \tag{5}
\]
A value \(-1\) means exactly one of the two Legendre symbols is
\(-1\). The corresponding two \(\rho\)-values are the common maximum
and at most one less, so (1) again splits.

Lau--Wu's Theorem 1 says that for every fixed \(\eta>0\), a
nonprincipal character of cube-free modulus \(Q\) has an integer
\[
 1\le a\ll_\eta Q^{\vartheta+\eta}
\]
at which its value is neither \(0\) nor \(1\). The moduli \(q\) and
\(pq\) above are odd and squarefree. If the witness value is \(-1\),
the square chain splits. If it is \(0\), then \(p\mid a\) or \(q\mid a\),
so \(\gcd(a,D)>1\). For sufficiently large \(D\), the witness bound is
less than \(D\), hence that gcd is proper. Finitely many smaller inputs
are absorbed into the constant.

The algorithm does not know \(p,q,Q\), or \(\chi\). Choose
\(\eta<\varepsilon\), absorb the implied constant into the remaining
power of \(D^\varepsilon\), and try every integer \(a\) up to
\(D^{\vartheta+\varepsilon}\). The theorem guarantees that one trial
succeeds.

## 3. Complete factorization from a known multiple of \(\lambda\)

For every odd prime \(p\mid N\), one has
\(p-1\mid\lambda(N)\mid E\), hence \(p\le E+1\). For every composite
divisor \(D\) with at least two distinct prime divisors, Section 2
therefore has
\[
 Q\le
 \min\!\left\{\operatorname{rad}(D),(E+1)^2\right\}.
\]
Indeed, in the unequal-layer case \(Q\) is one prime divisor, and in
the equal-layer case it is the product of two distinct prime divisors.
Scanning bases in increasing order therefore produces a proper factor
by the time the right-hand side of this bound, raised to
\(\vartheta+\varepsilon\), is reached. The algorithm does not need to
know the radical; it stops when a proper gcd is found. Repeat on the
two factors. The same original \(E\) remains a multiple
of the Carmichael value of every divisor. Prime powers are recognized
deterministically in polynomial time, and their prime bases are
certified by deterministic primality testing.

There are \(O(\log N)\) nodes in the recursion, and at every
node this bound is at most
\[
 C(N,E)=\min\!\left\{\operatorname{rad}(N),(E+1)^2\right\}.
\]
Modular exponentiation and gcd computation add only factors polynomial
in \(\log E+\log N\). Thus complete factorization costs
\[
 C(N,E)^{1/(4\sqrt e)+\varepsilon}
 (\log N+\log E)^{O_\varepsilon(1)}.
\]
If \(E=N^\tau<N^{1/2}\), then \(C(N,E)\ll N^{2\tau}\), giving
\(N^{\tau/(2\sqrt e)+\varepsilon}\).
For an even input, strip its exact power of two first.

## 4. A structural first-split profile for a short multiple

Suppose that \(N\) is odd, \(k=\omega(N)\ge3\), and the supplied
integer \(E\) satisfies
\[
 \lambda(N)\mid E,\qquad E<N.
\]
Put
\[
 \tau=\frac{\log E}{\log N},\qquad
 a(\tau)=\min\!\left\{\tau,\frac{1+\tau}{4}\right\}.
\]
Every prime \(p\mid N\) satisfies \(p-1\mid E\), so
\[
 p\le E+1\ll N^{\tau+\varepsilon}. \tag{6}
\]
Run the deterministic routine of Morain--Renault--Smith Theorem 4.3
with \(u=1\) and \(M=E\), and validate any output. If the largest prime
divisor is \(p_1=N^{\alpha_1}\), then \(p_1-1\mid E\), so their theorem
recovers \(p_1\) in polynomial time whenever
\[
 \alpha_1>\frac{1+\tau}{4}. \tag{7}
\]
This use of Theorem 4.3 does not require \(N\) to be squarefree or
\(E\) to be the exact Carmichael value.

If that polynomial routine has not already split \(N\), every distinct
prime factor is at most \(N^{(1+\tau)/4}\). Together with (6), and
absorbing fixed constants into \(N^\varepsilon\), every prime factor is
at most
\[
 N^{a(\tau)+\varepsilon}. \tag{8}
\]

* If the layers \(s_p=v_2(p-1)\) are not all equal, choose \(q\) in a
  maximal layer and \(p\) in a lower layer. By (8), the character in
  Section 2 has conductor
  \[
   Q=q\ll N^{a(\tau)+\varepsilon}.
  \]

* If all layers are equal, choose the two smallest distinct prime
  factors \(p_1',p_2'\). Since there are \(k\) distinct factors,
  \[
   (p_1'p_2')^k
   \le \operatorname{rad}(N)^2
   \le N^2,
  \]
  and hence
  \[
   p_1'p_2'\le N^{2/k}. \tag{9}
  \]
  By (8), the same product is also
  \(O(N^{2a(\tau)+\varepsilon})\). Thus the product character has
  conductor
  \[
   Q\ll N^{\min\{2a(\tau),\,2/k\}+\varepsilon}.
  \]

The worst of the unequal- and equal-layer cases is
\[
 c(\tau,k)=
 \max\!\left\{a(\tau),\min\!\left\{2a(\tau),\frac2k\right\}\right\}
 =\min\!\left\{2a(\tau),\max\!\left\{a(\tau),\frac2k\right\}\right\}.
\]
Consequently a square-chain witness occurs by
\[
 N^{\vartheta c(\tau,k)+\varepsilon}. \tag{10}
\]
The algorithm need not know the hidden character, the prime sizes, or
\(k\): it runs the bounded polynomial routine and scans ordinary bases
in increasing order until a proper gcd appears. The actual \(k\) only
sharpens the stopping-time analysis.

For exact \(E=\lambda(N)\), one has \(E<N\), so \(\tau<1\). Prime
powers are recognized in polynomial time; inputs with two distinct odd
prime factors are handled by the pinned deterministic polynomial
exact-\(\lambda\) algorithm. For every remaining input, \(k\ge3\). If \(\tau\ge1/3\), then
\(a(\tau)=(1+\tau)/4<1/2\); if \(\tau<1/3\), then
\(a(\tau)=\tau\), which can only improve the following coarse bounds.
At \(k=3\), (10) is at most
\[
 N^{(2/3)\vartheta+\varepsilon}
 =N^{1/(6\sqrt e)+\varepsilon}.
\]
For every \(k\ge4\), \(c(\tau,k)\le1/2\), giving
\[
 N^{\vartheta/2+\varepsilon}
 =N^{1/(8\sqrt e)+\varepsilon}. \tag{11}
\]
When \(\tau<1/3\), the sharper bound
\(c(\tau,k)\le2\tau\) also records the direct restriction
\(p\le E+1\).

These smaller exponents are not asserted for recursive complete
factorization. After a split, the original \(E\) may be at least as
large as the child, and an original exact \(\lambda(N)\) need only be a
multiple, not the exact Carmichael value of the child. Section 3
supplies the complete-factor bound.
