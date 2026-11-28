# Sparse coprime cyclic resultants for bounded-omega squarefree factoring

## Result

Fix an integer \(K\ge 3\).  There is a predetermined list of exactly
\(K-2\) exponents \(J_i=\lceil\log_2 n\rceil+O_K(1)\) with the following
property.

> **Theorem.**  Let \(n\ge2\) be squarefree and suppose
> \(\omega(n)\le K\).  Given \(n\) and the \(K-2\) exact values
> \[
>       S_i=\sigma(n^{J_i}),
> \]
> the complete factorization of \(n\) can be recovered deterministically in
> \(\operatorname{poly}_K(\log n)\) bit operations.  The actual value of
> \(\omega(n)\) need not be known.

The divisor-sum queries are nonadaptive.  This is a fixed-\(K\), squarefree,
oracle result.  It is **not** an ordinary polynomial-time algorithm for
general integer factorization, it does not cover repeated prime powers, and
it makes no claim that \(K-2\) queries are optimal.

For \(K=3\), this specializes to the one-high-power-sum squarefree triprime
result in the neighboring
`factor-one-sum-squarefree-triprime` directory.  The construction here also
uses the sharper normalization exponent \(J\ge\max(2,\lceil\log_2 n\rceil)\).

## 1. A concrete pairwise-coprime query list

Put
\[
 M=\lceil\log_2 n\rceil,\qquad J_0=\max(2,M),\qquad r=K-2,
\]
and let
\[
 a_K=r!,\qquad q=a_K\left\lceil\frac{J_0}{a_K}\right\rceil,\qquad
 m_i=1+q+(i-1)a_K\quad(1\le i\le r).
\]
Use \(J_i=m_i-1\).

The integers \(m_i\) are pairwise coprime.  Indeed, a common divisor of
\(m_i\) and \(m_j\) divides \((i-j)a_K\), while every
\(m_i\equiv1\pmod{a_K}\).  It must therefore divide \(i-j\), hence
\(a_K\), and so it is one.
Also \(J_0\le J_i=J_0+O_K(1)\).

No prime search or unproved prime-gap estimate is used.

## 2. Every query supplies the totient

Write \(n=\prod_{p\mid n}p\), and let \(m=J+1\).  Then
\[
 \frac{n^m}{\sigma(n^{m-1})}
 =\varphi(n)\prod_{p\mid n}(1-p^{-m})^{-1}
 =\frac{\varphi(n)}{A_m},
 \qquad A_m:=\prod_{p\mid n}(1-p^{-m}).
\]
For \(m\ge3\),
\[
 1-A_m\le\sum_{p\mid n}p^{-m}
 <\sum_{t=2}^{\infty}t^{-m}
 <2^{-(m-1)}=2^{-J}.
\]
If \(J\ge M\), then
\[
 (\varphi(n)+1)(1-A_m)<n\,2^{-J}\le1.
\]
Consequently
\[
 \boxed{\displaystyle
 \varphi(n)=\left\lfloor
       \frac{n^{J+1}}{\sigma(n^J)}
       \right\rfloor .}
\]
Thus any one of the supplied sums determines \(\varphi(n)\) exactly.

## 3. The sparse cyclic-resultant equations

Suppose temporarily that \(k=\omega(n)\ge3\) is known.  Let
\(e_j\) be the elementary symmetric functions of the \(k\) distinct prime
divisors, and set
\[
 P_e(X)=X^k-e_1X^{k-1}+e_2X^{k-2}-\cdots+(-1)^k n.
\]
The two endpoint values are known:
\[
 P_e(0)=(-1)^k n,\qquad P_e(1)=(-1)^k\varphi(n).
\]
The second identity eliminates \(e_{k-1}\), leaving exactly
\(k-2\) variables \(e_1,\ldots,e_{k-2}\).

For \(m\ge2\), put
\[
 G_m(X)=1+X+\cdots+X^{m-1}.
\]
Because the roots of \(P_e\) are the prime divisors of \(n\),
\[
 \operatorname{Res}_X(P_e,G_m)
 =\prod_{p\mid n}G_m(p)
 =\sigma(n^{m-1}).
\]
For the first \(k-2\) supplied pairs \((m_i,S_i)\), form
\[
 F_i(e_1,\ldots,e_{k-2})
 :=\operatorname{Res}_X(P_e,G_{m_i})-S_i.
\]
The true elementary-symmetric vector is an integer zero of all the \(F_i\).

## 4. Why the system is finite: the coprime-index lemma

Let \(u=(e_1,\ldots,e_{k-2})\) and let \(H_m(u)\) be the highest homogeneous
part of \(\operatorname{Res}(P_e,G_m)\).  For
\(\zeta^m=1\), \(\zeta\ne1\), define
\[
 L_\zeta(u)
 =\sum_{j=1}^{k-2}(-1)^j e_j(\zeta^{k-j}-\zeta)
 =\zeta Q_u(\zeta),
\]
where
\[
 Q_u(Z)=\sum_{j=1}^{k-2}(-1)^j e_j
          (Z^{k-j-1}-1).
\]
Then
\[
 H_m(u)=(-1)^{k(m-1)}
        \prod_{\substack{\zeta^m=1\\\zeta\ne1}}L_\zeta(u).
\]
Equivalently,
\[
 H_m(u)=(-1)^{k(m-1)}m\,
 \operatorname{Res}\!\left(G_m,\frac{Q_u}{X-1}\right).
\]
Every displayed linear factor is nonzero: its \(e_{k-2}\)-coefficient is
\(\zeta^2-\zeta\ne0\).  Hence \(\deg H_m=m-1\).

Now take \(k-2\) pairwise-coprime indices \(m_i\).  If a nonzero projective
vector \(u\) vanished on every \(H_{m_i}\), then for each \(i\) there would
be a nontrivial \(m_i\)-th root of unity \(\zeta_i\) with
\(Q_u(\zeta_i)=0\).  Pairwise coprimality makes the \(\zeta_i\) distinct.
But \(Q_u(1)=0\), \(Q_u\ne0\), and \(\deg Q_u\le k-2\).  The \(k-2\)
distinct nontrivial roots together with \(1\) are impossible.

Therefore the highest homogeneous parts have no common projective zero.

## 5. Deterministic recovery, including nonradical fibers

Let \(D_i=m_i-1\), homogenize \(F_i\) to \(F_i^h(z,e)\), and work in
\[
 B=\mathbb Q[z,e_1,\ldots,e_{k-2}]/(F_1^h,\ldots,F_{k-2}^h).
\]
The preceding lemma says that
\((F_1^h,\ldots,F_{k-2}^h,z)\) has only the affine origin.  Since a
polynomial ring is Cohen--Macaulay, this is a homogeneous regular sequence.
In particular, \(z\) is a non-zero-divisor in \(B\), and
\[
 \operatorname{Hilb}_B(t)
 =\frac{\prod_i(1-t^{D_i})}{(1-t)^{k-1}}.
\]
For every layer degree
\[
 \ell\ge\sum_i(D_i-1),
\]
multiplication by \(z:B_\ell\to B_{\ell+1}\) is an isomorphism and both
spaces have dimension
\[
 D=\prod_iD_i.
\]

All of these spaces and maps are obtained by exact row reduction of the two
Macaulay matrices in degrees \(\ell\) and \(\ell+1\).  Multiplication by
\(e_j\), followed by the inverse of multiplication by \(z\), gives the
\(D\times D\) multiplication matrix for the affine coordinate \(e_j/z\).
Every rational zero has each coordinate among the rational eigenvalues of
the corresponding matrix.  Factoring the characteristic polynomials over
\(\mathbb Q\), enumerating the at most \(D^{k-2}\) coordinate tuples, and
substituting them back into the \(F_i\) finds every rational zero even when
the ideal is not radical.

Keep only integer tuples.  For each tuple, reconstruct \(e_{k-1}\), factor
\(P_e\) over \(\mathbb Q\), and accept only \(k\) distinct positive primes
whose product is \(n\) and which reproduce all supplied divisor sums.
Try \(k=3,\ldots,K\); the cases \(k=1,2\) are handled directly from
\(n\) and \(\varphi(n)\).

## 6. Bit complexity

For fixed \(K\):

- \(m_i=O_K(\log n)\), and every supplied \(S_i\) has
  \(O_K((\log n)^2)\) bits;
- each dense \(F_i\) is computed by a fraction-free Sylvester determinant
  of polynomial size;
- the degrees \(D_i\), the Bezout length \(D=\prod D_i\), the number of
  monomials in each Macaulay layer, and all rational-matrix dimensions are
  polynomial in \(\log n\);
- coefficient heights remain polynomially bounded by determinant/minor
  bounds;
- exact rational linear algebra and deterministic factorization over
  \(\mathbb Q\) are polynomial-time.

Thus the complete procedure is deterministic
\(\operatorname{poly}_K(\log n)\).  The fixed-\(K\) qualification is
essential: no uniform polynomial bound is claimed when \(K\) grows.

## 7. Abundance-decision corollary

Shunia's abundance-to-comparison construction computes an exact
\(\sigma(x)\) using \(O(\log x)\) adaptive abundance queries, each at an
integer of \(O((\log x)^2)\) bits.  Here
\(x=n^{J_i}\) has \(O_K((\log n)^2)\) bits.  Therefore, for fixed \(K\), the
same squarefree family is factored with

- \(O_K((\log n)^2)\) abundance decisions, and
- abundance-query integers of \(O_K((\log n)^4)\) bits.

The \(K-2\) divisor-sum locations themselves remain predetermined.

## 8. Independent checks

A reviewer separate from the author rederived the unit-root leading forms,
the complete-intersection/Macaulay argument, and the bit bounds.  Exact
Macaulay reconstructions were independently run for:

- \(k=4\): \(n=210\), recovering \((e_1,e_2)=(17,101)\);
- \(k=4\): \(n=17017\), recovering \((48,838)\);
- \(k=5\): \(n=2310\), recovering \((28,288,1358)\);
- \(k=5\): \(n=15015\), recovering \((39,574,3954)\).

The bundled dependency-free checker separately verifies 2,920 exact
highest-term identities, 1,025 finite-field projective points, 62
normalization cases at the stated exponent, and 68 true sparse-resultant
equations.

## 9. Relation to prior work

The exact source comparison is recorded in `UPSTREAM.md`.  Briefly:

- Shunia uses many consecutive high-power divisor sums for general
  deterministic reconstruction and explicitly notes the cyclic-resultant
  identity.
- Eriksson gives a linear-exponent bounded-\(\omega\) reconstruction using
  \(2K\) consecutive sums, including arbitrary multiplicities.
- Hillar and Hillar--Levine study reconstruction of general polynomials from
  full or initial segments of cyclic resultants.

The precise increment here is different: known \(P(0)\), recovered \(P(1)\),
and \(K-2\) pairwise-coprime sparse indices force a finite complete
intersection for squarefree bounded-\(\omega\) inputs.  No absolute
priority or query-optimality claim is made.
