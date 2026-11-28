# One high-power divisor sum for all integers with at most three prime factors

## Result

> **Theorem.** Let \(n\ge2\) satisfy \(\omega(n)\le3\), with arbitrary
> prime multiplicities. Put \(M=\lceil\log_2 n\rceil\) and
> \(J=\max(2,M)\). Given the single exact value
> \[
> S=\sigma(n^J),
> \]
> the complete prime-power factorization of \(n\) can be recovered
> deterministically in \(\operatorname{poly}(\log n)\) bit operations.

The query exponent is fixed before the answer is known. The theorem covers
prime powers, arbitrary two-prime-power integers, nonuniform triprimes, and
uniform triprimes. It is not a general integer-factorization algorithm and
does not claim that one high-power divisor sum suffices when
\(\omega(n)\ge4\).

This result strictly extends the squarefree triprime theorem in the
neighboring *factor-one-sum-squarefree-triprime* directory.

## 1. The one sum recovers the totient even with multiplicities

Write
\[
 n=\prod_{i=1}^k p_i^{a_i},\qquad q_i=p_i^{a_i}.
\]
The exact Euler-product identity is
\[
 \frac{\varphi(n)\sigma(n^J)}{n^{J+1}}
 =\prod_{i=1}^k\left(1-p_i^{-1}q_i^{-J}\right)
 =:P_J.
\]
Therefore
\[
 \frac{n^{J+1}}{\sigma(n^J)}=\frac{\varphi(n)}{P_J}.
\]
Because \(a_iJ+1\ge J+1\),
\[
 1-P_J
 \le\sum_i p_i^{-(a_iJ+1)}
 \le\sum_{m=2}^{\infty}m^{-(J+1)}
 <2^{-J}\qquad(J\ge2).
\]
If \(J\ge M\), then
\[
 (\varphi(n)+1)(1-P_J)<n\,2^{-J}\le1.
\]
It follows that
\[
 \boxed{\displaystyle
 \varphi(n)=\left\lfloor\frac{n^{J+1}}{S}\right\rfloor.}
\]

No squarefreeness assumption entered this step.

## 2. The known totient-only part

Żrałek's deterministic totient-factorization analysis gives two facts used
here.

1. Every integer with at most two distinct prime factors can be factored
   deterministically from \(n\) and the single value \(\varphi(n)\).
2. If
   \[
     n=p^\alpha q^\beta r^\gamma
   \]
   with distinct primes and the three exponents are not all equal, then
   \(n\) can be factored deterministically from \(n,\varphi(n)\) in
   \(O((\log n)^3)\) operations.

A direct implementation of the two-prime step is also elementary. If
\(w=x^a y^b\), \(\psi=\varphi(w)\), and \(d=w-\psi\), then
\[
 dxy=w(x+y-1),\qquad (dx-w)y=w(x-1).
\]
For each \(1\le a,b\le\lceil\log_2w\rceil\), factor
\[
 H_{a,b}(X)=w^{b-1}X^a(X-1)^b-(dX-w)^b
\]
over \(\mathbb Q\). The true \(x\) is an integer root; recover
\(y=w(x-1)/(dx-w)\) and verify primality, exponents, product, and totient.
The degrees and coefficient heights are polynomial in \(\log w\).

A short self-contained form of the equal-order split is useful. Put
\[
 r_0=\frac{n}{\gcd(n,\varphi(n))},\qquad
 U=\gcd(n,r_0^M),\qquad V=n/U.
\]
The integer \(r_0\) is a nonempty squarefree product of prime divisors of
\(n\), and it contains the largest prime divisor. If \(V>1\), then
\((U,V)\) is a nontrivial coprime partition into complete prime powers.
Since \(\omega(n)\le3\), at least one side is a prime power; exact-root
testing and AKS identify it. Divide its known totient contribution out of
\(\varphi(n)\), leaving an integer with at most two distinct primes.

If \(V=1\), then \(r_0=\operatorname{rad}(n)\). The quotients
\[
 \frac{\gcd(n,r_0^j)}{\gcd(n,r_0^{j-1})}
 =\prod_{a_p\ge j}p
\]
recover the equal-exponent groups. If there is more than one nonempty
group, at most one group is composite. The singleton prime groups are
known, their totient contributions can be divided out, and a remaining
double group \(u=pq\) is split using
\[
 X^2-(u-\varphi(u)+1)X+u.
\]

Thus the only three-prime case not closed by the totient-only split is the
**uniform-multiplicity case**.

## 3. The uniform-multiplicity branch

Suppose
\[
 n=m^a,\qquad m=pqr
\]
for three distinct primes. The single-group equal-order branch gives \(m=r_0=\operatorname{rad}(n)\)
and the common exponent \(a\); exact integer-root testing independently
verifies \(n=m^a\). The base \(m\) is squarefree.
Also
\[
 \varphi(m)=\frac{\varphi(n)}{m^{a-1}}.
\]

Set
\[
 t=aJ+1,\qquad
 G_t(X)=1+X+\cdots+X^{t-1}.
\]
Then the same single supplied value is
\[
 S=\sigma(n^J)
  =G_t(p)G_t(q)G_t(r).
\]

Let
\[
 s=p+q+r,\qquad C=m-\varphi(m)-1.
\]
Since
\[
 \varphi(m)=m-(pq+pr+qr)+s-1,
\]
we have \(pq+pr+qr=s+C\). Define
\[
 P_T(X)=X^3-TX^2+(T+C)X-m
\]
and the univariate integer polynomial
\[
 R(T)=\operatorname{Res}_X(P_T,G_t)-S.
\]
The true sum \(s\) is an integer root of \(R\).

### Exact degree and leading coefficient

For \(\zeta^t=1\), \(\zeta\ne1\),
\[
 P_T(\zeta)
 =\zeta^3+C\zeta-m+T\zeta(1-\zeta).
\]
Since
\[
 \operatorname{Res}(P_T,G_t)
 =(-1)^{3(t-1)}
   \prod_{\substack{\zeta^t=1\\\zeta\ne1}}P_T(\zeta),
\]
its leading coefficient in \(T\) is
\[
 (-1)^{3(t-1)}
 \left(\prod_{\zeta\ne1}\zeta\right)
 \left(\prod_{\zeta\ne1}(1-\zeta)\right)
 =(-1)^{3(t-1)}(-1)^{t-1}G_t(1)
 =t.
\]
Hence
\[
 \deg R=t-1=aJ
\]
and \(R\) is never the zero polynomial.

Factor \(R\) deterministically over \(\mathbb Q\), retain its integer roots
\(T\), factor the corresponding cubic \(P_T\), and accept only three
distinct positive primes that reproduce \(m,\varphi(m)\), and the supplied
\(S\). The true factorization is retained.

## 4. A verified total algorithm

Run the following deterministic branches and verify every output.

1. Recover \(\varphi(n)\) by the floor formula.
2. Apply the gcd/equal-order split above. It completely handles
   \(\omega(n)\le2\) and three-prime inputs with nonuniform exponents.
3. If the split has one equal-exponent group, use its base
   \(m=r_0\) and common exponent \(a\), build the uniform resultant
   \(R(T)\), and test every integer root as above.

Under the promise \(\omega(n)\le3\), at least one branch succeeds. A false
branch cannot be accepted because primality, multiplicities, the product,
the totient, and the original divisor sum are all checked exactly.

## 5. Bit complexity

Let \(M=\lceil\log_2 n\rceil\), and take
\(J=\max(2,M)\).

- The supplied \(S\) and \(n^{J+1}\) have \(O(M^2)\) bits.
- The gcd/equal-order operations and their exact-power checks are
  deterministic polynomial time.
- In the uniform branch, \(\log m=M/a+O(1)\) and
  \(t=aJ+1=O(M^2)\).
- The dense resultant polynomial \(R\) has degree \(O(M^2)\) and
  polynomially bounded coefficient height, for example
  \(O(t(\log m+\log t))\) bits by a Sylvester/Hadamard bound.
- Fraction-free resultant computation and deterministic factorization over
  \(\mathbb Q\) are polynomial in these bounds.

The total bit complexity is therefore polynomial in \(M\).

## 6. Abundance-decision corollary

Shunia's comparison construction computes this one exact
\(\sigma(n^J)\) using \(O(\log(n^J))=O(M^2)\) adaptive abundance decisions.
Each abundance query is at an integer of
\(O((\log(n^J))^2)=O(M^4)\) bits.

Thus every integer with at most three distinct prime factors, with arbitrary
multiplicities, is deterministically factored from \(O(M^2)\) abundance
decisions of \(O(M^4)\)-bit size.

## 7. Independent checks

An author-external reviewer checked the exact Żrałek scope against the fixed
PDF, rederived the gcd split and the uniform resultant sign, degree, and bit
bounds, and ran 4,462 exact triprime cases with \(n\le12000\). Four
independent full resultant reconstructions used
\[
 \begin{aligned}
 (n,a,J,t)&=(455,1,9,10),\\
           &\quad(207025,2,18,37),\\
           &\quad(1003003001,3,30,91),\\
           &\quad(146918641,2,28,57).
 \end{aligned}
\]
In every case the leading coefficient was \(t\), and the unique verified
prime-sum root was recovered.

The bundled dependency-free verifier checks:

- 375 arbitrary-multiplicity totient-floor cases;
- 90 exact two-prime eliminant cases;
- 540 gcd/equal-order split cases, equally divided between its two branches;
- 60 nonuniform \(2+1\) equal-order completion cases;
- 8 exact uniform Sylvester-resultant cases;
- 39 exact leading-coefficient identities; and
- one 210-bit uniform input with \(t=1471\) and a 44,036-bit divisor sum.

## 8. Scope and prior work

The exact source comparison is in *UPSTREAM.md*.

The totient-only subcases are not claimed as new. The precise increment is
their composition with one high-power divisor sum and the uniform
cyclic-resultant branch, which closes **all** multiplicity patterns for
\(\omega(n)\le3\) using one ordinary divisor-sum value.

More generally, a larger \(J\ge\max(2,M)\) also works, with runtime
polynomial in \(M,J\) and the explicit input length. No absolute priority
or one-query optimality claim is made.
