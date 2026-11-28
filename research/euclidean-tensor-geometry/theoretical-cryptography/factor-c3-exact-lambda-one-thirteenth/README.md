# Deterministic factoring of three-prime Carmichael radicals from one exact exponent

**Theorem.** Given a Carmichael number \(R\) with exactly three prime factors and its **exact** Carmichael value \(\lambda(R)\), unconditional deterministic complete factorization uses \(R^{1/13}(\log(2R))^{O(1)}\) bit operations.

**Corollary.** Let \(N=2^e n\), \(n\) odd, and suppose its odd radical \(R=\operatorname{rad}(n)\) satisfies the theorem's promise. Given \(N\) and \(\lambda(N)\), complete factorization uses
\[
 R^{1/13}(\log(2N))^{O(1)}
\]
bit operations. All prime multiplicities are arbitrary and unknown. There is no query at a proper divisor in either result.

The assertion is a numerical time bound on a promised class with arithmetic advice, not a bit-polynomial algorithm for all three-prime Carmichael numbers. It does not cover arbitrary three-prime radicals, known multiples of \(\lambda(N)\), or ordinary factoring without the advice. The square-decoding identity below is known. The exponent comes from combining two searches using different information recovered by that identity.

## 1. Arithmetic data recovered from a squarefree input

Write \(R=pqr\) with odd primes \(p<q<r\), and let \(\Lambda=\lambda(R)\). Korselt's criterion gives \(\Lambda\mid R-1\). Put
\[
 g=\gcd(p-1,q-1,r-1), \quad p=1+ga,\quad q=1+gb,\quad r=1+gc.
\]
Here \(g\ge2\), \(1\le a<b<c\), and \(a,b,c\) are pairwise coprime. Indeed, if a prime divides two of them, it does not divide the third because their common gcd is 1. That prime would divide \(\Lambda/g=\operatorname{lcm}(a,b,c)\), but would not divide \((R-1)/g\), whose reduction is the third coefficient. This contradicts Korselt. In particular \(\Lambda=gabc\).

Let \(S=(R-1)/\Lambda\). The square bound used in Gupta--Sikarov--Volkovich, Lemma 2.11, recovers \(g=\lfloor\sqrt{S-1}\rfloor\). For completeness, expanding shows \(S>g^2\), and
\[
 S<\frac{(g+1)(g+1/2)(g+1/3)}{g}
   =g^2+\tfrac{11}{6}g+1+\tfrac{1}{6g}<(g+1)^2.
\]
The first strict upper bound drops the \(-1\) in the numerator and uses \(a\ge1,b\ge2,c\ge3\); the last uses \(g>1\). Define the known quantities
\[
 J=S-g^2,\quad L=\Lambda/g=abc,\quad E=LJ,\quad x=g/J.
\]
Then \(1\le J\le2g\), \(x\ge1/2\), and \(\varphi(R)=g^2\Lambda\). Expanding \(R\) also gives the two forms of the key identity:
\[
 \begin{split}
 E&=(a+b+c)+g(ab+ac+bc),\\
 J&=g/a+g/b+g/c+1/(ab)+1/(ac)+1/(bc).
 \end{split} \tag{1}
\]
In particular
\[
 x<a<\tfrac92 x,\qquad a+b+c<\frac{3L}{x^2},\qquad L<\frac{R}{g^3}.
 \tag{2}
\]
For the first bound use \(g/a<J<3g/a+3/a^2\le 9g/(2a)\), since \(a\ge1,g\ge2\). For the second use \(abc=L\), \(b>a>x\), and \(a+b+c<3c\). The last is immediate from \(R=(1+ga)(1+gb)(1+gc)>g^3L\).

## 2. Search the progression for one factor

Use the integer interval
\[
 A_0=\lfloor g/J\rfloor+1,\qquad
 A_1=\min\left\{\left\lfloor\frac{9g-1}{2J}\right\rfloor,\
                 \left\lfloor\frac{\lfloor\sqrt[3]R\rfloor-1}{g}\right\rfloor\right\}.
\]
This contains \(a\) by (2) and \(p^3<R\). Put \(T=A_1-A_0+1\); it is positive on the promised branch, and \(T=O(1+x)\). For every \(i\) in the interval the candidate is \(1+gi<R\). Set \(B=\lceil\sqrt T\rceil\), \(K=\lfloor T/B\rfloor\), and over \(\mathbb Z/R\mathbb Z\) form
\[
 F(Y)=\prod_{j=0}^{B-1}\bigl(1+g(A_0+BY+j)\bigr).
\]
A balanced product tree forms \(F\). A monic subproduct tree on \(Y,Y-1,\ldots,Y-(K-1)\), followed by recursive remainders, evaluates \(F(0),\ldots,F(K-1)\). Their gcds with \(R\) are the block gcds. Test the at most \(B-1\) final candidates directly. If a full-block gcd is \(R\), test that block's at most \(B\) candidates individually and take a nontrivial gcd. In such a block some leaf gcd exceeds 1, and it is proper because each candidate is positive and smaller than \(R\). In fact a promised input has \(r>R^{1/3}\), so no clipped candidate is a multiple of \(r\); the full-gcd fallback is only needed for a generic progression helper. At least one nontrivial gcd occurs since the interval contains \(p\). A proper gcd of \(R\) yields a prime factor by testing that gcd and its complementary divisor. Divide \(\varphi(R)\) by this prime minus one to get the totient of the complementary semiprime, then recover its two factors by the quadratic discriminant. Validate primality with deterministic AKS and check the exact Carmichael value on the output.

The modular polynomial work costs \(\widetilde O(B\log R)\) bit operations, where the soft bound suppresses powers of \(\log(2R)\). To see this without assuming that the modulus is prime, multiply polynomials of length \(d\) by packing their standard residue coefficients as nonnegative digits of bit width \(2\lceil\log_2 R\rceil+\lceil\log_2(2d)\rceil+1\). Integer multiplication produces the coefficient convolution with no carries between digits; extract and reduce modulo \(R\). Quasi-linear integer multiplication gives the bound \(\widetilde O(d\log R)\) here. Remaindering by a monic divisor uses polynomial reversal and truncated inverse of a series with constant term 1, via \(v\leftarrow v(2-av)\), doubling precision at each step for the inverse of \(a\). Thus each remainder has the same soft degree-linear bound and needs no nonunit inversion. At any level of either tree the sum of degrees is \(O(B+K)\), including the initial reduction of the degree-at-most-\(B\) polynomial. The number of levels is logarithmic, and \(K\le B\). Including gcds, branch time is \(O((1+\sqrt x)(\log(2R))^{O(1)})\).

## 3. Search the residue class of one cubic coefficient

Equation (1) fixes \(s=a+b+c\equiv E\pmod g\). Enumerate the integers in this residue class with
\[
 1\le s\le \left\lfloor\frac{3LJ^2-1}{g^2}\right\rfloor .
\]
For each set \(w=(E-s)/g\), skip if \(w\le0\), and seek three positive integer roots of
\[
 P_s(X)=X^3-sX^2+wX-L. \tag{3}
\]
For the correct \(s\), the roots are \(a,b,c\). Verify product, distinctness, primality of the reconstructed \(1+g a,1+g b,1+g c\), and the supplied exponent. Thus a spurious candidate cannot certify a wrong output.

A self-contained bit-polynomial test for (3) is as follows. Any positive root of a split candidate is at most \(L\). The discrete difference is
\[
 P_s(t+1)-P_s(t)=3t^2+(3-2s)t+(1-s+w).
\]
Its own differences are \(6t+6-2s\); their signs locate a minimum of the quadratic on \(1,\ldots,L-1\), and binary searches on its two monotone sides give the interval of negative differences, if any. Therefore the values of \(P_s\) on \(1,\ldots,L\) consist of at most three monotone segments: nondecreasing, decreasing, and nondecreasing. On each signed monotone segment, multiply by sign \(+1\) on a nondecreasing segment and by sign \(-1\) on the decreasing segment. Binary search for the first nonnegative signed value and the first positive signed value gives the entire interval of zeros. In other words, test \(P_s\ge0\) and \(P_s>0\) on nondecreasing segments, and \(P_s\le0\) and \(P_s<0\) on the decreasing segment. Take the union of the zero intervals to include shared endpoints and repeated roots correctly (the nonzero cubic has at most three distinct zeros). For \(L=1\) test the single point. Given any one integer root, divide out its linear factor and solve the remaining quadratic by its exact discriminant. If the cubic splits into positive distinct integer roots, this succeeds regardless of the first root found. All values have \(O(\log R)\) bits, including at the interval endpoints. Each candidate therefore costs polynomial time in \(\log R\).

The candidate count is at most \(1+3L/(g x^2)\), hence \(O(1+R/(g^4 x^2))=O(1+R/x^6)\) since \(x\le g\). If \(x\le R^{2/13}\), use Section 2. Otherwise Section 3 costs at most \(O((1+R^{1/13})(\log(2R))^{O(1)})\). The comparison can use the integers \(g^{13}\) and \(J^{13}R^2\). Alternatively choose the smaller of the two computable search sizes \(B\) and the number of residues; this keeps the same bound. This proves the squarefree case.

## 4. Odd prime multiplicities and the even part

If \(n=\prod_{p\mid R}p^{a_p}\), Korselt gives \(\gcd(R,\lambda(R))=1\), so no prime divisor of \(R\) divides any other prime divisor minus one. The local Carmichael exponents for \(n\) therefore give
\[
 \gcd(n,\lambda(n))=n/R,\qquad \lambda(n)/(n/R)=\lambda(R).
\]
Indeed each CRT component has exponent \(p^{a_p-1}(p-1)\), the \(p^{a_p-1}\) part is absent from all other local exponents, and all the \(p-1\) parts are coprime to \(R\). Hence the exact odd exponent gives \(R\) and \(\Lambda\), and each \(a_p\) is recovered by division after factoring \(R\).

To obtain the odd exponent from the exact even input, strip \(2^e\) and write \(\lambda(N)=2^z A\) with \(A\) odd. The order formula \(\lambda(N)=\operatorname{lcm}(\lambda(2^e),\lambda(n))\) and the fact that \(\lambda(2^e)\) is a two-power give at most \(1+z=O(\log(2N))\) candidates \(\lambda(n)=2^j A\), \(0\le j\le z\); if \(e=0\) use the exact value directly. For a candidate set \(D=\gcd(n,2^j A)\), \(R=n/D\) and \(\Lambda=2^j A/D\). The odd gcd and hence \(R\) are independent of \(j\). Reject if \(\Lambda\nmid R-1\), \(S\le1\), \(g<2\), \(g\nmid\Lambda\), or \(J\notin[1,2g]\). At this point even a false candidate obeys \(x\ge1/2\), \(x\le g\), \(L<R/g^3\), so all branch time bounds remain valid. Reject an empty interval or unsuccessful search. Require the complete output to consist of prime powers with the correct product and exact \(\lambda(N)\). The true candidate always succeeds, and any accepted factorization is correct. The number of guesses changes only the polylogarithmic factor.

## 5. Two elementary bit-polynomial windows

If \(r\le g^2(\log(2N))^C\) for a fixed \(C\), then \(s=a+b+c<3g(\log(2N))^C\). Scan Section 3 in increasing order with this smaller cutoff (or try the first \(O((\log(2N))^C)\) candidates before the general algorithm). No primality or factorization advice beyond \(\lambda(N)\) is needed. This is not limited to the previously known simple case \(a=1\). For instance \(252601=41\cdot61\cdot101\) has \(g=20\) and \((a,b,c)=(2,3,5)\).

Alternatively if \(a=1\) or \(b\ge2a^2\), there is a direct recovery \(a=\lceil x\rceil\). For \(a=1\) use \(0<x<1\). For \(a\ge2\), put \(U=J-g/a\). The exact condition for \(a=\lceil x\rceil\) is
\[
 U<\frac{g}{a(a-1)}.
\]
When \(b\ge 2a^2\), (1) and \(c>b\) give
\[
 U<2g/b+2/(ab)+1/b^2
 \le g/a^2+1/a^3+1/(4a^4)<g/[a(a-1)].
\]
The final difference \(g/[a(a-1)]-g/a^2=g/[a^2(a-1)]\) exceeds \(2/a^3\). Once \(a\) is recovered, use the known totient as in Section 2. The \(a=1\) case is already covered by Gupta--Sikarov--Volkovich.

See [UPSTREAM.md](UPSTREAM.md) for the source comparisons. The finite checkers reproduce the arithmetic and exact recovery paths, not the asymptotic cost of a fast polynomial-arithmetic implementation.
