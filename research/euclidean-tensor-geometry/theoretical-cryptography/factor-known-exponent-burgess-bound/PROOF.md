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

For every composite \(D\) with at least two distinct prime divisors,
Section 2 has \(Q\le D\). Scanning all bases through
\(D^{\vartheta+\varepsilon}\) therefore produces a proper factor.
Repeat on the two factors. The same original \(E\) remains a multiple
of the Carmichael value of every divisor. Prime powers are recognized
deterministically in polynomial time, and their prime bases are
certified by deterministic primality testing.

There are \(O(\log N)\) nodes in the recursion, and every scanned range
is at most \(N^{\vartheta+\varepsilon}\). Modular exponentiation and
gcd computation add only factors polynomial in \(\log E+\log N\).
Thus complete factorization costs
\[
 N^{1/(4\sqrt e)+\varepsilon}
 (\log E)^{O_\varepsilon(1)}.
\]
For an even input, strip its exact power of two first.

## 4. A smaller first-split exponent from exact \(\lambda\)

Now suppose that \(N\) is odd, composite, squarefree, and the supplied
value is the exact \(\lambda(N)\).

First run the deterministic polynomial exact-\(\lambda\) candidate
search for a product of two primes and validate any returned
factorization. Also run the Morain--Renault--Smith large-factor
procedure and validate its output. Their Theorem 1.1 guarantees that,
when \(N\) has at least three prime factors and its largest prime
exceeds \(\sqrt N\), this procedure recovers that prime in deterministic
polynomial time from one exact \(\lambda\) value.

It remains to consider at least three primes, all at most \(\sqrt N\).

* If the layers \(s_p\) are not all equal, choose \(q\) in a maximal
  layer and \(p\) in a lower layer. Since \(q\le\sqrt N\), the character
  in Section 2 has \(Q=q\le N^{1/2}\). Its witness occurs below
  \(N^{\vartheta/2+\varepsilon}\).

* If all layers are equal, choose the two smallest prime factors
  \(p_1,p_2\). With at least three factors,
  \[
   p_1p_2\le N^{2/3}.
  \]
  The product character has \(Q=p_1p_2\le N^{2/3}\), so its witness
  occurs below
  \[
   N^{(2/3)\vartheta+\varepsilon}
   =N^{1/(6\sqrt e)+\varepsilon}. \tag{6}
  \]

Scanning all bases through the larger bound (6), alongside the two
polynomial candidate procedures, therefore finds a nontrivial factor
without knowing which case holds.

The smaller exponent is not asserted for recursive complete
factorization: after a split, the original exact \(\lambda(N)\) need
only be a multiple, not the exact Carmichael value of a child factor.
Section 3 supplies the unconditional complete-factor bound.
