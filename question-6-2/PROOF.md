# Classification of the polynomial in Question 6.2

Throughout \(e>2\), \(K=\mathbb F_{4^e}\), and \(n=1+4^{e-2}+4^{e-1}+2\cdot4^e\). Write \(S_j(X)=\sum_{i=0}^{j-1}X^{4^i}\) and \(\tau=\operatorname{Tr}_{K/\mathbb F_4}=S_e|_K\).

## 1. The exact polynomial from the translation sum

The definition is \(g_{n,4}(Z^4-Z)=\sum_{u\in\mathbb F_4}(Z+u)^n\). Let \(X=Z^4+Z\), and for each summand put \(T=Z+u\). Then \(T^{4^j}=T+S_j(X)\). With \(A=S_{e-2}(X), B=S_{e-1}(X), t=S_e(X)\), the summand factors as
\[
 T(T+A)(T+B)(T+t)^2
 =T^5+(A+B)T^4+(AB+t^2)T^3+(A+B)t^2T^2+ABt^2T.
\]
Of the power sums \(\sum_{u\in\mathbb F_4}(Z+u)^j\), \(1\le j\le5\), all are zero except at \(j=3\), where the sum is 1. Indeed \(\sum_u u^i\) vanishes for \(i=0\) and for \(i>0\) not divisible by 3, and equals 1 for positive multiples of 3; the candidate binomial coefficients at \(i=3,j=4,5\) are even. Therefore \(g_{n,4}=AB+t^2\) as a polynomial: the equality holds at all \(X\) in an algebraic closure, since there is a \(Z\) with \(Z^4+Z=X\) for each \(X\). The formal identity \(t+S_2^{4^{e-2}}=A\) reconciles this with the displayed expression in the question.

On \(K\) set \(y=x^{4^{e-2}}\). This is a bijective change of input with inverse \(x=y^{16}\), and \(\tau(y)=\tau(x)=t\). Then \(B(x)=t+y^4,\ A(x)=t+y+y^4\), so
\[
 g_{n,4}(x)=(t+y^4)(t+y+y^4)+t^2
            =h(y):=y^8+y^5+y\tau(y).                          \tag{1}
\]

## 2. Even extensions

If \(y\in\mathbb F_4\) and \(e\) is even, then \(\tau(y)=ey=0\), and \(y^8=y^5=y^2\). Thus every point of \(\mathbb F_4\) maps to zero. This excludes every even extension in the question.

## 3. A collision criterion on the zero-trace layer

Suppose \(e\) is odd. We will find \(b\in K\) such that
\[
 \tau(b^9+b^6)=1,\qquad
 \tau(b^{13}+b^{10}+b^7)=0.                                   \tag{2}
\]
With \(a=b^4+b\) one has \(\tau(a)=0\) and \(a\ne0\): otherwise \(b\in\mathbb F_4\), and \(b^9+b^6=0\) contradicts (2). Expanding \(a^3=b^{12}+b^9+b^6+b^3\) and using \(\tau(b^{12})=\tau(b^3)\) yields \(\tau(a^3)=1\). Since \(\tau(1)=1\) for odd \(e\), the equation
\[
 z^4+z=a^3+1
\]
is soluble. Indeed, the \(\mathbb F_4\)-linear map \(z\mapsto z^4+z\) has kernel \(\mathbb F_4\) and image contained in \(\ker\tau\); both image and \(\ker\tau\) have cardinality \(4^{e-1}\) (the trace is a nonzero linear map, already since \(\tau(1)=1\)). Also
\[
 \begin{aligned}
 \tau(az)
 &=\tau((b^4+b)z)=\tau(b^4(z^4+z))=\tau(b^4(a^3+1))\\
 &=\tau(b^{16}+b^{13}+b^{10}+b^7+b^4)
   =\tau(b^{13}+b^{10}+b^7)=0,
 \end{aligned}
\]
as the trace is invariant under fourth powers. Thus \(y=az\) and \(y+a\) have trace zero. On this layer (1) gives
\[
 h(y+a)+h(y)=a^8+a^5+a^4y+a y^4
             =a^5(a^3+1+z+z^4)=0.
\]
As \(a\ne0\), this is a collision.

## 4. Existence of the trace witness for every odd e at least nine

Write \(Q=4^e\), \(P_1(X)=X^9+X^6\), \(P_2(X)=X^{13}+X^{10}+X^7\). Let \(\chi(t)=(-1)^{\operatorname{Tr}_{\mathbb F_4/\mathbb F_2}(t)}\) on \(\mathbb F_4\) and \(\psi(x)=\chi(\tau(x))\) on \(K\). For \(c\in\mathbb F_4\), character orthogonality gives \(\sum_{u\in\mathbb F_4}\chi(uc)=4\) when \(c=0\) and 0 otherwise; for \(c\ne0\) multiplication by \(c\) permutes the field and the character is nontrivial. Applying this separately to the two conditions in (2), their number of solutions \(N\) satisfies
\[
 16N
 =\sum_{u,v\in\mathbb F_4}\chi(u)
       \sum_{b\in K}\psi\big(uP_1(b)+vP_2(b)\big).              \tag{3}
\]
Here the twist \(\chi(u)\) corresponds to target trace 1 in the first condition. The two conditions use independent summation indices, so no independence assumption about the values of the polynomials is needed. The equality \(\psi(x)=(-1)^{\operatorname{Tr}_{K/\mathbb F_2}(x)}\) follows by transitivity of the trace, and \(\psi\) is nontrivial.

The \((u,v)=(0,0)\) term in (3) is \(Q\). When \(u\ne0,v=0\), the polynomial has odd leading degree 9; when \(v\ne0\) its odd leading degree is 13. The complete additive Weil bound on \(K\) for a polynomial of degree \(D\) prime to the characteristic is \((D-1)\sqrt Q\) for each nontrivial character. One can reduce the even-power terms without changing the character by replacing \(cX^{2j}\) with \(\sqrt c\, X^j\), since the absolute trace is invariant under squaring. This leaves the same nonzero odd leading term. In particular none of the nonzero masks is Artin–Schreier-degenerate: its polynomial has a pole of odd positive order at infinity, whereas a nonconstant rational square-plus-itself with a pole there has even pole order. There are three masks of the first kind and twelve of the second. It follows that
\[
 16N\ge Q-(3\cdot8+12\cdot12)\sqrt Q
       = Q-168\sqrt Q>0,
\]
since \(\sqrt Q=2^e\ge512\) for \(e\ge9\). This proves a collision for all odd \(e\ge9\), without an upper limit.

## 5. Exact finite certificates for e = 3, 5, 7

Use a binary polynomial basis in \(K=\mathbb F_2[\alpha]\), with \(\alpha\) the residue of \(X\) modulo the indicated binary polynomial. A nonnegative integer encodes its binary digits as the coefficients of successive powers of \(\alpha\); addition is XOR. The reproducible checker verifies for each listed modulus that successive powers of \(\alpha\) exhaust the nonzero vectors exactly once and return to 1, which certifies the field before performing the evaluations. The independent checker uses carryless reduction and a separate quotient-ring evaluation of the original defining sum.

* For \(e=3\), \(h(y)=y^8+y^2+y^{17}\). With modulus \(X^6+X+1\) (67), the outputs for inputs \(0,1,\ldots,63\), in hexadecimal, are:

  ```text
  00 01 2e 3e 27 2b 14 09 39 3d 13 06 21 28 16 0e
  25 36 33 31 1c 02 17 18 19 0f 0b 0c 1f 04 10 1a
  2a 2d 30 26 3f 35 38 23 05 07 1b 08 2f 20 2c 32
  37 22 15 11 3c 24 03 0a 1d 0d 3b 3a 29 34 12 1e
  ```

  Each value occurs once. The full permutation also replays in a second field representation with modulus 115.
* For \(e=5\), take modulus \(X^{10}+X^3+1\) (1033). The following encodings give a collision *within* the trace-1 layer:
  \[
   b=98,\quad a=42,\quad z=653,\quad (y,y+a)=(66,104),
     \quad h(y)=h(y+a)=593.
  \]
  They satisfy \(b^4+b=a,\ az=y,\ \tau(a)=0,\ \tau(y)=1\), and \(z^4+z=a^3+1+a^{-4}=380\). In fact the collision difference on the trace-1 layer is \(a^5(a^3+1+a^{-4}+z+z^4)\), adding \(a=a^5a^{-4}\) to the trace-zero difference. Alternatively the two evaluations can be performed from (1) alone. With modulus 2041 the corresponding tuple is \((b,a,z,y,y+a)=(104,133,326,59,190)\), output 927. The finite \(e=5\) case is not claimed to have a trace-zero collision as in Section 3.
* For \(e=7\), take modulus \(X^{14}+X^5+X^3+X+1\) (16427). The encoding \(b=34\) satisfies (2), and
  \[
   a=2802,\quad z=5678,\quad (y,y+a)=(10007,11749),
       \quad h(y)=h(y+a)=8993.
  \]
  Here \(z^4+z=a^3+1=12836\) and \(\tau(az)=0\), so this is also a certificate for the trace-sieve construction. With modulus 32743 a second tuple is \((b,a,z,y,y+a)=(76,15531,4840,15728,475)\), output 214.

These cases together with Sections 2 and 4 exhaust the stated range \(e>2\).
