# \(K-2\) sparse high-power divisor sums for all bounded-\(\omega\) integers

## Result

Fix \(K\ge3\). Put
\[
 r=K-2,\qquad L=r!,\qquad
 M=\lceil\log_2 n\rceil,\qquad
 J=L\left\lceil\frac{\max(2,M)}{L}\right\rceil,
\]
and make the \(r\) nonadaptive queries
\[
 S_i=\sigma(n^{J_i}),\qquad J_i=iJ,\qquad 1\le i\le r.
\]

> **Theorem.** For every \(n\ge2\) with \(\omega(n)\le K\), allowing
> arbitrary prime multiplicities, the complete prime-power factorization
> of \(n\) can be recovered from \(n,S_1,\ldots,S_r\) deterministically in
> \(\operatorname{poly}_K(\log n)\) bit operations.

The actual value of \(\omega(n)\), the multiplicities, and the partition
of the primes are not supplied. The theorem is an oracle result for each
fixed \(K\); it is not an ordinary polynomial-time algorithm for general
integer factorization, and it does not claim that \(K-2\) queries are
necessary.

This simultaneously extends the neighboring results for one sum and
\(\omega\le3\), two sums and \(\omega\le4\), and \(K-2\) sums for
squarefree bounded-\(\omega\) inputs.

## 1. Normalization and coprime effective indices

For every exponent \(T\ge\max(2,M)\),
\[
 \frac{\varphi(n)\sigma(n^T)}{n^{T+1}}
 =\prod_{p^a\parallel n}(1-p^{-(aT+1)})=:A_T.
\]
The elementary bound
\[
 1-A_T\le\sum_{m=2}^{\infty}m^{-(T+1)}<2^{-T}
\]
gives
\[
 \boxed{\displaystyle
 \varphi(n)=\left\lfloor\frac{n^{T+1}}{\sigma(n^T)}\right\rfloor.}
\]
Thus \(S_1\) determines \(\varphi(n)\).

The reason for rounding \(J\) to a multiple of \(L\) is the following
uniform coprimality property. For every possible multiplicity
\(1\le a\le M\), set
\[
 m_{a,i}=aJ_i+1=aiJ+1.
\]
If \(i<j\), then a common divisor of \(m_{a,i}\) and \(m_{a,j}\) divides
\(aJ(j-i)\), and is coprime to \(aJ\). It therefore divides \(j-i\).
But \(j-i\mid L\mid J\), while \(m_{a,i}\equiv1\pmod{j-i}\). Hence
\[
 \gcd(m_{a,i},m_{a,j})=1.
\]
Only indices belonging to the same multiplicity \(a\) need this property.

## 2. What \(n,\varphi(n)\) reveal without factoring

Let
\[
 R=\frac{n}{\gcd(n,\varphi(n))},\qquad
 U=\gcd(n,R^M),\qquad V=n/U.
\]
For each \(p^a\parallel n\), the exponent of \(p\) in \(R\) is zero or
one. The largest prime divisor belongs to \(R\), so \(R>1\). Therefore
\(R=\operatorname{rad}(U)\), and \(U\) is a nonempty product of complete
prime-power components.

The equal-exponent blocks inside \(U\) are known exactly. Define
\[
 w_j=\frac{\gcd(U,R^j)}{\gcd(U,R^{j-1})}
     =\prod_{\substack{p\mid R\\v_p(n)\ge j}}p,
 \qquad
 u_j=w_j/w_{j+1}.
\]
Every nontrivial \(u_j\) is the known squarefree product of precisely the
primes that occur to exponent \(j\). Rename these known bases
\[
 u_1,\ldots,u_g
\]
and their known exponents
\[
 a_1,\ldots,a_g.
\]
The complementary integer \(V\) contains the remaining full prime powers,
but its radical and multiplicities need not be known.

The algorithm enumerates the following finite structural data:

* a positive count \(k_\ell\) of prime roots in each known base \(u_\ell\);
* a count \(h\ge0\) of prime roots in \(V\), with \(h=0\) exactly when
  \(V=1\);
* ordered exponents \(1\le b_1,\ldots,b_h\le M\);

subject to
\[
 k=\sum_{\ell=1}^g k_\ell+h\le K.
\]
There are only \(\operatorname{poly}_K(M)\) possibilities. Every proposed
solution is ultimately checked for distinct positive prime roots, the
correct exponents, product \(n\), totient, and every supplied divisor sum.

## 3. The polynomial system for one structural guess

For a known block \(u_\ell\) with proposed root count \(k_\ell\), introduce
the monic polynomial
\[
 P_\ell(T)=T^{k_\ell}-e_{\ell,1}T^{k_\ell-1}
 +\cdots+(-1)^{k_\ell}u_\ell.
\]
Its constant coefficient is fixed; the \(k_\ell-1\) remaining elementary
symmetric coefficients are variables.

For the unknown part \(V\), introduce variables \(X_1,\ldots,X_h\) and
the monomial equation
\[
 \prod_{j=1}^h X_j^{b_j}=V.
\]
Put \(G_m(T)=1+T+\cdots+T^{m-1}\). For each query \(i\), impose
\[
 \prod_{\ell=1}^g
 \operatorname{Res}_T(P_\ell,G_{m_{a_\ell,i}})
 \prod_{j=1}^h G_{m_{b_j,i}}(X_j)
 =S_i. \tag{3.1}
\]
At the true structural guess, the roots of \(P_\ell\) are exactly the
primes in \(u_\ell\), so multiplicativity of \(\sigma\) proves every
equation.

There is one special case. If \(h=0\) and \(g=1\), all prime factors have
the same exponent. When \(k=1\), the guessed polynomial is simply
\(P_1(T)=T-u_1\), so this zero-variable guess is checked directly. When
\(k\ge2\),
\[
 P_1(1)=(-1)^k\varphi(u_1)
\]
is known from \(\varphi(n)=u_1^{a_1-1}\varphi(u_1)\). Use this linear
identity to eliminate \(e_{1,k-1}\). This leaves exactly \(k-2\)
coefficient variables. For \(k=2\) there are no variables and the guess
is again checked directly; the projective boundary calculation below is
needed only for \(k\ge3\).

## 4. Product-projective compactification

The main point is that the affine system in Section 3 has only finitely
many complex solutions, including for incorrect structural guesses.

For each known block, use coordinates
\([z_\ell:e_{\ell,1}:\cdots:e_{\ell,k_\ell-1}]\) on
\(\mathbb P^{k_\ell-1}\) and the linear-coefficient homogenization
\[
 \widetilde P_\ell(T)=z_\ell\bigl(T^{k_\ell}+(-1)^{k_\ell}u_\ell\bigr)
 +\sum_{q=1}^{k_\ell-1}(-1)^qe_{\ell,q}T^{k_\ell-q}.
\]
If \(D_{\ell,i}=m_{a_\ell,i}-1=a_\ell J_i\), put
\[
 \mathcal R_{\ell,i}=(-1)^{k_\ell D_{\ell,i}}
 \prod_{\substack{\zeta^{m_{a_\ell,i}}=1\\\zeta\ne1}}
 \widetilde P_\ell(\zeta).
\]
This is homogeneous of degree \(D_{\ell,i}\) in its own block and reduces
in the affine chart to the required resultant. A block with
\(k_\ell=1\) is \(\mathbb P^0\) and has no infinite chart.
For each \(X_j\), use \([x_j:z_j]\in\mathbb P^1\). Homogenize
\[
 G_m(X_j)\quad\text{to}\quad
 \mathcal G_m(x_j,z_j)=\sum_{q=0}^{m-1}x_j^qz_j^{m-1-q}.
\]
Homogenize each resultant in its own coefficient block, and replace
(3.1) by the multi-homogeneous equation
\[
 \prod_\ell \mathcal R_{\ell,i}
 \prod_j\mathcal G_{m_{b_j,i}}(x_j,z_j)
 -
 S_i\prod_\ell z_\ell^{m_{a_\ell,i}-1}
      \prod_j z_j^{m_{b_j,i}-1}=0. \tag{4.1}
\]
The monomial equation becomes
\[
 \prod_j x_j^{b_j}-V\prod_jz_j^{b_j}=0. \tag{4.2}
\]

Suppose a common projective zero lies on the boundary, meaning that some
\(z_\ell\) or \(z_j\) is zero. Then the right side of (4.1) vanishes for
every \(i\). Consequently every one of the \(K-2\) query indices must be
**covered** by a zero of at least one constituent factor on the left.

### Coverage capacity of one constituent

The effective indices belonging to any fixed exponent are pairwise
coprime.

* At a finite known block, \(\mathcal R_{\ell,i}=0\) means that a root of
  \(P_\ell\) is a nontrivial \(m_{a_\ell,i}\)-th root of unity. One root
  can cover at most one query index. Since the product of all roots has
  absolute value \(u_\ell>1\), at least one root is not a root of unity.
  The block covers at most \(k_\ell-1\) indices.
* At an infinite known block \(z_\ell=0\), its homogeneous polynomial is
  \(TQ_\ell(T)\), where \(Q_\ell\ne0\) and
  \(\deg Q_\ell\le k_\ell-2\). It covers at most \(k_\ell-2\) indices.
* A finite nonzero \(X_j\) covers at most one index.
* At \(X_j=0\) or \(X_j=\infty\), the value of
  \(\mathcal G_m\) is respectively \(z_j^{m-1}\) or \(x_j^{m-1}\), so it
  covers no index.

### The boundary budgets

If some unknown coordinate is infinite, (4.2) forces another unknown
coordinate to be zero. Those two cover nothing. Even treating every known
block as finite, the total coverage is at most
\[
 \sum_\ell(k_\ell-1)+(h-2)=k-g-2\le k-3.
\]

If no unknown coordinate is infinite and \(h>0\), the boundary must contain
an infinite known block. All \(X_j\) are finite and nonzero; because their
weighted product is the integer \(V>1\), at least one is not a root of
unity. The total capacity is at most
\[
 \left(\sum_\ell(k_\ell-1)-1\right)+(h-1)
 =k-g-2\le k-3.
\]

If \(h=0\) and \(g\ge2\), at least one known block is infinite, and the
capacity is at most
\[
 \sum_\ell(k_\ell-1)-1=k-g-1\le k-3.
\]

Finally suppose \(h=0,g=1\) and \(k\ge3\). After the elimination using
\(P_1(1)\), the highest homogeneous factor at a nontrivial \(m\)-th root \(\zeta\) is
\[
 \zeta Q_e(\zeta),\qquad
 Q_e(Z)=\sum_{q=1}^{k-2}(-1)^q e_q
        (Z^{k-q-1}-1).
\]
The nonzero polynomial \(Q_e\) has degree at most \(k-2\) and already has
the root \(1\). It can therefore cover at most \(k-3\) query indices.

In every case a boundary point covers at most \(k-3\) indices, but it
would have to cover all
\[
 K-2\ge k-2.
\]
This is impossible. Hence the projective zero set has no boundary points.

Under the Segre embedding, the boundary is a hyperplane section. Every
positive-dimensional projective closed set meets every hyperplane.
Therefore a projective zero set disjoint from the boundary is
zero-dimensional. The original affine system has finitely many complex
solutions.

## 5. Deterministic exact recovery

All query exponents are \(O_K(M)\). The polynomials
\(G_{m_{a,i}}\) have degree \(O_K(M^2)\), and their coefficients, all
resultants, and all supplied values have \(\operatorname{poly}_K(M)\)
bits. The number of variables is bounded solely by \(K\).

A standard fixed-dimensional elimination algorithm now enumerates every
rational point, without a radical-ideal assumption. One explicit route is
Hermann's effective ideal-membership bound. For a chosen coordinate
\(X_q\), work over \(\mathbb Q(X_q)\) in the remaining variables. Since
the ideal is zero-dimensional, \(1\) belongs to the extended ideal.
Hermann's bound restricts the cofactor degrees to
\(D^{O_K(1)}\). Coefficient comparison gives a polynomial matrix over
\(\mathbb Q[X_q]\); a nonzero full-rank pivot minor
\(\delta_q(X_q)\) then lies in the original ideal after clearing
denominators. It can be found deterministically by exact rank
specialization and interpolation. Its degree and coefficient height are
polynomial in \(M\).

Factor every \(\delta_q\) over \(\mathbb Q\), enumerate the
\(\operatorname{poly}_K(M)\) rational-coordinate tuples, and substitute
them into the original equations. Factor every accepted \(P_\ell\) over
\(\mathbb Q\), and keep only distinct positive prime roots and prime
\(X_j\)'s that reproduce \(n,\varphi(n)\), the enumerated multiplicities,
and all \(S_i\). The true structural guess survives, so the complete
factorization is recovered.

## 6. Reproducibility and scope

The bundled checker verifies the normalization, the simultaneous
pairwise-coprime index construction, exact equal-order grouping, every
boundary-budget case through \(K=9\), and true query identities on mixed
multiplicity samples.

A separate symbolic audit should check the multi-homogeneous boundary
argument, the all-equal elimination, and at least one mixed \(K=5\)
instance before archival use.

The precise comparison with prior work is in \`UPSTREAM.md\`. No absolute
priority or query-optimality claim is made.
