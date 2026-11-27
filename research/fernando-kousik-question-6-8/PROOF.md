# The extension classification

Let \(q=4\), \(e\ge3\), \(n=1+2q+q^2+2q^3+2q^{e+1}\), and \(S_j(X)=\sum_{i=0}^{j-1}X^{q^i}\). For \(K=\mathbb F_{4^e}\), write \(\tau=\operatorname{Tr}_{K/\mathbb F_4}=S_e|_K\).

## 1. Literal polynomial and finite-field representative

From the defining identity,
\[
 g_{n,4}(Z^4-Z)=\sum_{a\in\mathbb F_4}(Z+a)^n.
\]
Let \(X=Z^4+Z\). Each \(T=Z+a\) satisfies \(T^{4^j}=T+S_j(X)\) by repeated fourth-power Frobenius. Put \(A=X\), \(B=S_2(X)\), \(C=S_3(X)\), and \(D=S_{e+1}(X)\). The summand is
\[
 T(T+A)^2(T+B)(T+C)^2(T+D)^2
       =(T^2+BT)(T^2+A^2)(T^2+C^2)(T^2+D^2).
\]
Among the power sums of the four translates \(T\) for \(0\le j\le8\), only \(\sum T^3=\sum T^6=1\) and \(\sum T^7=X\) are nonzero. In fact in the binomial expansion only the positive exponent multiples \(i=3,6\) can contribute from \(\sum_{a\in\mathbb F_4}a^i\), both with value 1. Their binomial coefficients give \(j=3,6,7\) as stated; for \(j=7\) the sum is \(Z^4+Z=X\). Hence
\[
 g_{n,4}(X)=A^2+C^2+D^2+B(A^2C^2+A^2D^2+C^2D^2)+BX.
\]
This identity holds formally, because it holds for every \(X\) in an algebraic closure (where a preimage \(Z\) always exists). With \(D'=D+X\), it becomes
\[
 g_{n,4}(X)=C^2+(D')^2+B\bigl(X^4+(X^2+C^2)(D')^2\bigr)+BX
          =X^{32}+(D+X)^2(1+B^9).                           \tag{1}
\]
The last equality uses \(B=X+X^4,\ C+B=X^{16}\), and \(X+C=B^4\).

To compare with Question 6.8, the displayed right-hand side there is
\[
 XC+B^4C+B^5+BC+S_e^2+X^4B+X^2 B S_e^2+BC^2 S_e^2 .
\]
This simplifies formally to \(X^{32}+S_e^2(1+B^9)\): the terms containing \(C\) but not \(S_e\) give \(X^{16}C\), the other terms not containing \(S_e\) give \(X^{16}B\), and \(X^2+C^2=(B^4)^2\). The difference of (1) and the displayed representative is exactly
\[
 (X^{4^e}+X)^2(1+B^9),
\]
because \(D=S_e+X^{4^e}\). In particular the two polynomials are congruent modulo \(X^{4^e}-X\). The displayed representative therefore has precisely the right values on the field where the question asks about permutation. On \(K\) write
\[
 g(x)=x^{32}+\tau(x)^2\bigl(1+(x+x^4)^9\bigr).               \tag{2}
\]

## 2. Odd extensions and the trace-zero layer

For odd \(e\) and \(x\in\mathbb F_4\), \(\tau(x)=x\), \(x^4+x=0\), and \(x^{32}=x^2\). Thus (2) is zero at all four subfield points, so cannot be a permutation.

For any \(e\), on \(\ker\tau\) the formula is the binary Frobenius \(x\mapsto x^{32}\), a bijection of that layer onto itself. We will exclude even \(e\ge6\) by producing a nonzero-trace \(y\) with \(g(y)\in\ker\tau\).

## 3. A two-trace collision criterion in even dimension

For \(e\) even the subfield \(\mathbb F_{16}\) is in \(K\). Put
\[
 \rho:K\to\mathbb F_{16},\qquad
 \rho(z)=\operatorname{Tr}_{K/\mathbb F_{16}}(z)
        =\sum_{i=0}^{e/2-1}z^{16^i}.
\]
If \(z\in K\) satisfies \(\rho(z)=1\) and \(\tau(z^9)=1\), then \(\tau(z)=\rho(z)+\rho(z)^4=0\). The map \(y\mapsto y+y^4\) is \(\mathbb F_4\)-linear with kernel \(\mathbb F_4\), and its image is contained in \(\ker\tau\). This image is all of \(\ker\tau\): both have cardinality \(4^{e-1}\), as the trace is a nonzero \(\mathbb F_4\)-linear map (its nonzero polynomial has degree \(4^{e-1}<4^e\)). Choose \(y\) with \(y+y^4=z\). Then
\[
 \rho(z)=\sum_{i=0}^{e/2-1}\left(y^{4^{2i}}+y^{4^{2i+1}}\right)
       =\tau(y)=1.
\]
Taking the trace of (2) and using \(\tau(1)=0\) for even \(e\), one gets \(\tau(g(y))=1+\tau(z^9)=0\). There is thus a \(w\in\ker\tau\) with \(w^{32}=g(y)\), for example \(w=g(y)^{2^{2e-5}}\). It satisfies \(g(w)=g(y)\) and \(w\ne y\), since the traces are 0 and 1 respectively.

## 4. The trace witness exists for all even \(e\ge10\)

Let \(Q=4^e\), and let \(\psi(t)=(-1)^{\operatorname{Tr}_{K/\mathbb F_2}(t)}\) be the nontrivial canonical additive character. For \(b\in\mathbb F_{16}\) and \(c\in\mathbb F_4\), write \(\chi_{16}(b)=(-1)^{\operatorname{Tr}_{16/2}(b)}\) and \(\chi_4(c)=(-1)^{\operatorname{Tr}_{4/2}(c)}\). The number \(N\) of \(z\in K\) satisfying the two conditions of Section 3 is given by independent orthogonality expansions in the two target fields:
\[
 64N
 =\sum_{u\in\mathbb F_{16},\,v\in\mathbb F_4}
   \chi_{16}(u)\chi_4(v)\sum_{z\in K}\psi(uz+v z^9).          \tag{3}
\]
This uses trace transitivity, for example \(\chi_{16}(u\rho(z))=\psi(uz)\), and the scale \(64=16\cdot4\). For completeness, \(\sum_{u\in E}(-1)^{\operatorname{Tr}_{E/\mathbb F_2}(ua)}\) is \(|E|\) for \(a=0\) and zero otherwise, as \(u\mapsto ua\) is bijective when \(a\ne0\).

The term \(u=v=0\) is \(Q\). For \(v=0,u\ne0\), the inner sum is zero because \(uz\) is bijective and \(\psi\) is nontrivial. The other \(16\cdot3=48\) masks have a degree-9 polynomial with nonzero leading coefficient. The complete additive Weil bound is \(8\sqrt Q\) in each such case, since degree 9 is prime to characteristic 2. In Artin–Schreier terms its pole at infinity is odd, so it cannot be a rational square-plus-itself plus a constant; a pole of a square-plus-itself has even order. Consequently
\[
 64N\ge Q-48\cdot 8\sqrt Q=Q-384\sqrt Q>0
\]
for \(2^e=\sqrt Q\ge1024\). Hence every even extension \(e\ge10\) has the collision.

## 5. Exact finite certificates for even \(e=4,6,8\)

Field elements are encoded by integers whose binary digits are coefficients in the basis \(1,\alpha,\alpha^2,\ldots\), where \(\alpha\) is the residue of \(X\) modulo the stated binary polynomial. The verifier checks that the nonzero power cycle of \(\alpha\) has full length and then does the arithmetic with those exact field operations. A second checker uses carryless modular reduction and evaluates the original defining sum in \(K[T]/(T^4+T+x)\).

For \(e=4\) and modulus \(X^8+X^4+X^3+X^2+1\) (285), the values of (2) for inputs \(0,\ldots,255\), in hexadecimal, are:

    00 01 69 68 f8 f9 c2 c3 a7 a6 44 45 86 87 e1 e0
    f7 f6 18 19 da db f5 f4 5c 5d 76 77 a3 a2 9e 9f
    4b 4a 78 79 d9 d8 08 09 ec ed 04 05 46 47 9b 9a
    10 11 64 65 fa fb ff fe 6e 6f 8e 8f b7 b6 f1 f0
    72 73 1f 1e dd dc ac ad 5b 5a 6a 6b 63 62 99 98
    07 06 e6 e7 ab aa c5 c4 b1 b0 43 42 81 80 2b 2a
    40 41 84 85 82 83 eb ea 1c 1d d5 d4 a8 a9 1b 1a
    e4 e5 6d 6c 88 89 3f 3e f2 f3 39 38 e3 e2 c1 c0
    12 13 7c 7d 31 30 d0 d1 fc fd 56 57 94 95 66 67
    7b 7a 0a 0b c8 c9 a5 a4 4e 4f b4 b5 bd bc 8c 8d
    e8 e9 5f 5e ba bb 33 32 16 17 34 35 ee ef 25 24
    3c 3d 55 54 53 52 97 96 cc cd 7f 7e 02 03 cb ca
    22 23 0d 0c cf ce 20 21 49 48 74 75 a1 a0 8b 8a
    15 14 2f 2e be bf d7 d6 36 37 51 50 93 92 70 71
    28 29 2d 2c b3 b2 c7 c6 26 27 60 61 59 58 b9 b8
    df de 0e 0f af ae 9c 9d 4c 4d 91 90 d3 d2 3b 3a

This is a permutation of all byte values. Both the entire table in this field and the version in the distinct field representation (modulus 501) check against the original defining sum.

For \(e=6,8\), explicit certificates from Section 3 are as follows (integers are decimal and encode polynomial-basis coefficients, not residues modulo the integer):

| \(e\) | Binary modulus encoding | \(z\) | \(y\) | \(w\) | \(g(y)=g(w)\) |
|--:|--:|--:|--:|--:|--:|
| 6 | 4179 | 10 | 1180 | 1278 | 12 |
| 6 | 8137 | 224 | 58 | 873 | 2035 |
| 8 | 65581 | 66 | 26884 | 34160 | 37251 |
| 8 | 131053 | 330 | 6202 | 4686 | 28143 |

The checkers confirm \(\rho(z)=\tau(z^9)=1\), \(z=y+y^4\), and the displayed distinct inputs and equal outputs. This finishes the even cases and proves that the only extension in Question 6.8 is \(e=4\).
