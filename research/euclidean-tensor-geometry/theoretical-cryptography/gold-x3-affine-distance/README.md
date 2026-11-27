# Independent certificate for the eight-bit Gold map \(x^3\)

## Status: reproduced known exact value

Let

\[
K=\mathbf F_2[t]/(t^8+t^4+t^3+t+1)
\]

and let \(F:K\to K\) be the Gold APN map \(F(x)=x^3\). If
\(\mathcal A\) is the set of all affine maps from the eight-dimensional
\(\mathbf F_2\)-space \(K\) to itself, then

\[
\boxed{d_H(F,\mathcal A)=240.}
\]

This value is **not new**. Biryukov, Tureček, and Udovenko's EUROCRYPT
2026 work [*Algorithmic Toolkit for Linearization of
S-boxes*](https://eprint.iacr.org/2026/913) computes provably optimal
linearizations for S-boxes of at most eight bits. Their public
[monomial result table](https://github.com/cryptolu/sbox_linearization/blob/main/summary_logs_monomial.txt#L217)
records size 16 for n8_monomial3, which is the same distance
\(256-16=240\).

This directory gives only a small, readable, dependency-free
**independent witness and verifier**. It is not a new theorem, a
cryptanalytic attack, or a result that should receive a release or DOI.

## Proof

Gábor P. Nagy's
[Theorem 18(iii)](https://doi.org/10.1007/s12095-025-00808-4)
proves that, in dimension eight,

\[
d_H(x^d,\mathcal A)\geq 240
\]

for every APN power exponent in the theorem other than \(d=9\).
The exponent \(3=2^1+1\) is a Gold APN exponent because
\(\gcd(1,8)=1\), so the published lower bound applies to \(F(x)=x^3\).

It remains to give an affine map with 16 agreements. In the polynomial
basis \(1,t,\ldots,t^7\), define the linear map \(L:K\to K\) by

\[
L(x)=
 \mathtt{b8}x+\mathtt{64}x^2+\mathtt{70}x^4+\mathtt{7a}x^8
 +\mathtt{41}x^{16}+\mathtt{79}x^{32}
 +\mathtt{12}x^{64}+\mathtt{fd}x^{128},
\]

where the hexadecimal constants denote elements of \(K\) in the same
polynomial basis. Equivalently, if input and output coordinates are
ordered from \(t^0\) to \(t^7\), the eight row masks of its binary matrix
are

\[
(\mathtt{41},\mathtt{d6},\mathtt{fe},\mathtt{56},
  \mathtt{7c},\mathtt{94},\mathtt{f4},\mathtt{84}).
\]

Direct evaluation in \(K\) gives exactly the following 16 solutions of
\(x^3=L(x)\):

\[
\{\mathtt{00},\mathtt{01},\mathtt{03},\mathtt{19},
  \mathtt{25},\mathtt{79},\mathtt{88},\mathtt{95},
  \mathtt{9e},\mathtt{a6},\mathtt{b7},\mathtt{c3},
  \mathtt{ca},\mathtt{d8},\mathtt{f3},\mathtt{f7}\}.
\]

Consequently \(d_H(F,L)=256-16=240\), so
\(d_H(F,\mathcal A)\leq240\). Together with Nagy's lower bound this gives
equality.

The chosen irreducible polynomial only fixes coordinates. Any two
realizations of \(\mathbf F_{256}\) are related by a field isomorphism,
which is \(\mathbf F_2\)-linear and sends \(x^3\) to \(x^3\). Conjugating
both \(F\) and an affine approximant preserves the number of agreements,
so the value 240 is coordinate-independent.

## Reproduce the certificate

Run:

    python3 verify_gold_x3_distance.py

The dependency-free verifier independently checks:

1. irreducibility of \(t^8+t^4+t^3+t+1\);
2. the APN derivative counts of \(x^3\);
3. additivity of the displayed binary matrix on all \(256^2\) pairs;
4. equality of the matrix and linearized-polynomial descriptions of \(L\);
5. the complete 256-point truth table and the exact 16-element agreement
   set above.

The script certifies the explicit upper-bound witness. The lower bound is
the cited published theorem, not a computational assumption in the
script.

## Prior-art boundary

The exact value 240 and optimal agreement size 16 were already public in
the EUROCRYPT 2026 work cited above. The explicit matrix in this directory
is an independently generated reproducibility witness. Nagy's 2025 lower
bound plus this witness gives a short independent proof of optimality.

Primary sources:

- A. Biryukov, P. Tureček, A. Udovenko,
  [*Algorithmic Toolkit for Linearization of
  S-boxes*](https://eprint.iacr.org/2026/913), EUROCRYPT 2026,
  DOI 10.1007/978-3-032-25333-0_9.
- G. P. Nagy,
  [*On the minimum Hamming distance between vectorial Boolean and affine
  functions*](https://arxiv.org/abs/2503.03905),
  Cryptography and Communications 17 (2025), 1703–1720,
  DOI 10.1007/s12095-025-00808-4.
