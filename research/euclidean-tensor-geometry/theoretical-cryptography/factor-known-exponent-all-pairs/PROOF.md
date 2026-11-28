# Proof

Put
\[
 \vartheta=\frac1{4\sqrt e}.
\]

## 1. A deterministic refinement algorithm

Remove the exact power of two from \(N\). The odd part is maintained as
a product of pairwise coprime blocks, each block being a product of
complete prime-power components of the original input.

Fix an integer base \(a\) and a current block \(D\). Put
\(L=\lceil\log_2D\rceil\) and
\[
 U=\gcd(D,a^L).
\]
If \(p^r\parallel D\), then \(r\le L\). Consequently
\[
 U=\prod_{\substack{p^r\parallel D\\p\mid a}}p^r. \tag{1}
\]
Thus a proper \(U\) splits complete prime-power components, not partial
powers. On the complementary block \(D/U\), the base \(a\) is a unit.

Write
\[
 E=2^S T,\qquad T\ \text{odd}.
\]
On every block coprime to \(a\), compute
\[
 d_j=\gcd\left(a^{E/2^j}-1,D\right),
 \qquad 0\le j\le S, \tag{2}
\]
and refine the current partition by these divisors. Formula (1) and the
lemma below show that the complete-component invariant is preserved.

Process \(a=2,3,\ldots\) in order. Stop when every block is certified to
be a prime power. Deterministic primality testing together with exact
integer-root tests supplies this certification in time polynomial in
\(\log N\). The algorithm is fully specified without knowing any hidden
prime or stopping parameter.

## 2. The square-chain signature

For \(p^r\parallel D\) and \(\gcd(a,p)=1\), define
\[
 \rho_p(a)=v_2(\operatorname{ord}_{p^r}(a)).
\]
The kernel of reduction from
\((\mathbb Z/p^r\mathbb Z)^\times\) to
\((\mathbb Z/p\mathbb Z)^\times\) is an odd \(p\)-group, so
\[
 \rho_p(a)=v_2(\operatorname{ord}_p(a)). \tag{3}
\]
Because \(E\) is a multiple of every local order, its odd part \(T\)
contains the odd part of that order. Therefore
\[
 p^r\mid d_j
 \quad\Longleftrightarrow\quad
 \rho_p(a)\le S-j. \tag{4}
\]
In particular, if two distinct prime components have different
\(\rho\)-values, one of the nested gcds in (2) separates them.

For later use put \(s_p=v_2(p-1)\). Euler's criterion gives
\[
 \left(\frac ap\right)=-1
 \Longrightarrow \rho_p(a)=s_p,\qquad
 \left(\frac ap\right)=1
 \Longrightarrow \rho_p(a)\le s_p-1. \tag{5}
\]

## 3. A small witness for every pair

Fix two distinct odd prime divisors \(p,q\) that have not yet been
separated.

If \(s_p\ne s_q\), suppose without loss of generality that \(s_q>s_p\).
Use the Legendre symbol
\[
 \chi(a)=\left(\frac aq\right),
\]
a primitive nonprincipal quadratic character of conductor \(Q=q\).
A value \(\chi(a)=-1\) is coprime to \(q\). If \(p\mid a\), the
saturation step (1) already separates the pair. Otherwise
\[
 \rho_q(a)=s_q>s_p\ge\rho_p(a),
\]
so (4) separates the two components.

If \(s_p=s_q\), use
\[
 \chi(a)=\left(\frac ap\right)\left(\frac aq\right).
\]
This is a primitive nonprincipal quadratic character of squarefree
conductor \(Q=pq\). A value \(-1\) means that exactly one of the two
Legendre symbols is \(-1\). By (5), the two \(\rho\)-values differ, and
again (4) separates the pair.

Lau--Wu's Theorem 1 states that, for every fixed \(\eta>0\), a
nonprincipal character of cube-free modulus \(Q\) has an integer
\[
 1\le a\ll_\eta Q^{\vartheta+\eta} \tag{6}
\]
at which its value lies outside \(\{0,1\}\). Both characters above are
real quadratic, so this value is \(-1\). It is therefore coprime to its
conductor.

The base \(a\) can be divisible by prime factors of the current block
that are not in its conductor. Formula (1) first removes all of those
complete components. In the unequal-layer case, divisibility by the
lower-layer prime separates the chosen pair immediately; otherwise the
complementary block still contains both primes and (2)--(5) separate
them. In the equal-layer case both chosen primes lie in the conductor,
so both remain in the complementary block and the square chain separates
them. If the pair had already been separated by an earlier base, nothing
remains to prove.

## 4. Simultaneous all-pairs refinement

For each \(2\)-adic layer, the conductor of every same-layer pair is at
most the product of the two largest primes in that layer. For a
different-layer pair, the conductor used in Section 3 is one of the two
primes and is at most the largest prime divisor. Hence every pairwise
character conductor satisfies
\[
 Q\le H(N). \tag{7}
\]

Choose \(\eta>0\) smaller than the requested final
\(\varepsilon\), allowing for the fixed conversion of exponents and
constants. By (6)--(7), for every unordered pair of distinct prime
divisors there is a separating base
\[
 a\le C_\eta H(N)^{\vartheta+\eta}. \tag{8}
\]
After all bases through the right-hand side of (8) have been processed,
no block can contain two distinct prime divisors: any such pair would
have been separated by its witness. Since the invariant says that every
block is a product of complete prime-power components, every remaining
block is a prime power. The algorithm has therefore stopped with the
complete factorization.

At all times there are \(O(\log N)\) blocks. Per base, saturation,
modular exponentiation, the \(O(\log E)\) square-chain operations, gcds,
integer-root tests, and primality tests cost a factor polynomial in
\(\log N+\log E\). Absorbing \(C_\eta\) and the difference between
\(\eta\) and \(\varepsilon\) gives
\[
 H(N)^{1/(4\sqrt e)+\varepsilon}
 (\log N+\log E)^{O_\varepsilon(1)}.
\]
The algorithm need not know \(H(N)\): it simply stops when every block
is a certified prime power.

## 5. Corollaries

Let \(p_1<\cdots<p_k\) be the distinct odd prime divisors, \(k\ge2\).
Every same-layer pair product is at most \(p_{k-1}p_k\), and the largest
prime is smaller than that product. Thus
\[
 H(N)\le p_{k-1}p_k\le\operatorname{rad}(N). \tag{9}
\]
Moreover, for every \(p\mid N\),
\[
 p-1\mid\lambda(N)\mid E,
\]
so \(p\le E+1\) and
\[
 H(N)\le(E+1)^2. \tag{10}
\]
If every layer has size at most one, the pair-product part of the
definition is empty and \(H(N)=p_k\le E+1\).

Prime powers, and inputs with no odd prime factor, are handled in
deterministic polynomial time before the pairwise argument is needed.

## 6. What the finite verifier checks

The checker is not a proof of the analytic estimate (6). It independently
checks the exact algebra used around it:

* the prime- and two-prime character choices force unequal
  square-chain signatures;
* the displayed \(H(N)\) dominates every pair conductor;
* scanning through the actual least pair witnesses refines thousands of
  squarefree supports to singleton primes;
* saturation and square-chain refinement preserve complete prime-power
  components for arbitrary tested multiplicities.
