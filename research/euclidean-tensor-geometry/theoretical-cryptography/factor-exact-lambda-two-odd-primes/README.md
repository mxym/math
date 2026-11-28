# Factoring arbitrary powers of two odd primes from one exact Carmichael value

**Theorem.** There is an unconditional deterministic bit-polynomial algorithm which, given an integer \(N\ge1\) and its exact Carmichael value \(\lambda(N)\), returns the complete prime factorization of \(N\), provided \(N\) has at most two distinct **odd** prime factors. The multiplicities of all primes, including 2, are unrestricted and not supplied. No oracle call at a proper divisor is needed. This extends the known squarefree two-prime case; it is not an algorithm for unrestricted integer factorization or for arbitrary multiples of \(\lambda(N)\).

Here \(\lambda\) is the exponent of the unit group, with \(\lambda(1)=1\). For a prime power \(r^b\), its value is \(r^{b-1}(r-1)\) except for \(r=2,b\ge3\), when it is \(2^{b-2}\); on coprime products it is the least common multiple. Write \(v_r(x)\) for the exponent of prime \(r\) in a positive integer \(x\).

## 1. Odd input: locate the surviving radical

An odd input \(n=1\) is trivial. With one odd prime factor, an exact prime-power test gives the decomposition using integer roots and deterministic primality testing. Assume now \(n=p^a q^b\) with distinct odd primes \(p<q\). Write \(\Lambda=\lambda(n)\), put \(s=v_p(q-1)\), and set \(u=n/\gcd(n,\Lambda)\). From the local exponents,
\[
v_q(\Lambda)=b-1,\qquad v_p(\Lambda)=\max(a-1,s).
\]
Indeed \(q\) divides neither \(p\) nor \(p-1\), whereas its own local exponent contributes \(q^{b-1}\); the two contributions to the \(p\)-valuation are \(a-1\) and \(s\). Thus \(u=q\) if \(s\ge a\), and \(u=pq\) otherwise. If \(u\) is prime, divide out its full power and take the prime-power root of the remaining integer, if nontrivial. A promised prime-power input also falls into this prime-\(u\) branch.

## 2. Odd input: the normalized gcd recovers a shifted product

In the composite-\(u\) branch, \(s\le a-1\). Set \(t=(q-1)/p^s\) and \(m=\Lambda/(n/u)\), where the division is exact because \(n/u=\gcd(n,\Lambda)\). Then
\[
m=\operatorname{lcm}(p-1,t).
\]
To see this, the two local exponents are \(p^{a-1}(p-1)\) and \(q^{b-1}p^s t\). Their gcd is \(p^s\gcd(p-1,t)\): \(p\nmid(p-1)t\) and \(q>p\) implies \(q\nmid p^{a-1}(p-1)\). Divide their product by this gcd and by \(p^{a-1}q^{b-1}=n/u\).

Let \(d=\gcd(p-1,t)\). Since \(u-1=p^{s+1}t+(p-1)\), reduction modulo \(t\) and modulo \(p-1\) gives
\[
\gcd(u-1,t)=\gcd(u-1,p-1)=d.
\]
For positive integers, gcd with a fixed integer distributes over lcm, as is seen on each prime valuation. Consequently \(d=\gcd(u-1,m)\) is known and \(W=m\gcd(u-1,m)=(p-1)t\). Combining with \(u=p^{s+1}t+p\) shows that \(p\) is a root of the integer polynomial
\[
F_s(X)=WX^{s+1}+X^2-(u+1)X+u.\tag{1}
\]
Only \(0\le s\le\lfloor\log_2 n\rfloor+1\) need be tried. For each integer root in \([3,\lfloor\sqrt u\rfloor]\), test whether it divides \(u\), whether both it and its complementary divisor are distinct primes, and whether their full powers give \(n\). Recompute the Carmichael value of that factorization and accept only on equality. The true root passes. With \(s=0\), the normalized gcd gives the known squarefree quadratic on \(u\). The same argument applies to arbitrary multiplicities, including \(1\le s<a\), which is the cross-divisibility case not eliminated by the first gcd.

For comparison, the same identity also yields a bounded rounding decoder. Write \(Z=d(1+p+\cdots+p^s)\). Since \(m=t(p-1)/d\) and \(d\mid t\), \(m\ge p-1\), and
\[
0<\frac{u}{m}-Z=\frac{d}{p-1}+\frac{p}{m}\le\frac52.
\]
Thus \(Z=\lfloor u/m\rfloor-j\) for some \(j\in\{0,1,2\}\) and \(u-mZ=t+p\); one can also solve \(X^{s+1}(u-mZ-X)+X-u=0\). Equation (1) is preferable because the gcd removes these three guesses.

## 3. Exact integer roots and bit complexity

Each polynomial in (1) is strictly convex on the positive reals: the quadratic contributes 2 to the second derivative and the power term contributes a nonnegative quantity. Therefore the discrete differences \(F_s(x+1)-F_s(x)\) are strictly increasing for integer \(x\ge1\). A binary search finds the first nonnegative difference in the search interval, or its right endpoint if none occurs. The integer values decrease to a minimum and then increase, possibly with two adjacent equal minima. A binary search on each monotone segment finds the integer zeros by exact sign comparisons; check the adjacent minimum as well in case it is also zero. Alternatively, deterministic factorization of integer polynomials and reading off the linear factors gives the same candidate set; neither method factors a general integer as a subroutine. The included verifier uses the binary-search method.

Let \(H\) be the input bit length of \(N\). The number of \(s\) guesses is \(O(H)\); the coefficients of (1) have \(O(H)\) bits because \(m,u\le N\) on a valid branch and \(W\le mu\). An evaluation at any searched integer has \(O(H^2)\) bits and can be performed by repeated squaring and integer arithmetic. Each binary search uses \(O(H)\) evaluations. Integer roots used in the prime-power branch can be found by the same standard binary search, enumerating exponents at most \(H\), and primality is deterministic polynomial time by AKS. The whole odd-input algorithm runs in deterministic polynomial time.

## 4. Restore an even input

Write \(N=2^e n\) with \(n\) odd, computed by division. If \(e=0\), use the odd algorithm directly. If \(n=1\), output the power of two. Otherwise write the supplied \(\lambda(N)=2^z A\) with \(A\) odd. Because \(\lambda(2^e)\) is a power of two and \(\lambda(N)=\operatorname{lcm}(\lambda(2^e),\lambda(n))\), the odd part of \(\lambda(n)\) is exactly \(A\) and its two-adic exponent is some \(0\le j\le z\). Run the odd algorithm on the \(O(H)\) candidates \(2^j A\). For a guessed value the odd routine is merely a bounded search, followed by exact verification, and may reject. Adjoin the known power of two to an accepted decomposition and validate the full product, primality, multiplicities and supplied \(\lambda(N)\). The true guess succeeds; every accepted factorization is correct by unique factorization.

The only input beyond \(N\) is its **exact** Carmichael value. Neither a general factorization of \(\lambda(N)\), nor an order oracle, nor a size separation or smoothness assumption is used. `sh replay.sh` runs finite, synthetic exact checks; see [UPSTREAM.md](UPSTREAM.md) for prior scope.
