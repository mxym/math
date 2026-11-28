# Instance-adaptive sparse divisor sums for bounded-\(\omega\) factoring

## Result

Fix \(K\ge3\). Put
\[
 L=(K-2)!,\qquad M=\lceil\log_2 n\rceil,\qquad
 J=L\left\lceil\frac{\max(2,M)}{L}\right\rceil,
\]
and define the predetermined stream
\[
 S_i=\sigma(n^{iJ}),\qquad 1\le i\le K-2.
\]

Recover \(\varphi(n)\) from \(S_1\), and form the exact split described
below. Let the true split have \(g\ge1\) known equal-exponent blocks,
containing \(k_1,\ldots,k_g\) primes, and let its complementary part contain
\(h\) primes. Write \(k=\sum_\ell k_\ell+h=\omega(n)\), and define
\[
 B(n)=
 \begin{cases}
 \max(1,k-g-1),&h=0,\\
 \max(1,k-g-2),&h>0.
 \end{cases}
\]

> **Theorem.** For every fixed \(K\ge3\) and every \(n\ge2\) with
> \(\omega(n)\le K\), the first \(B(n)\) values
> \(S_1,\ldots,S_{B(n)}\) suffice to recover the complete prime-power
> factorization of \(n\) deterministically in
> \(\operatorname{poly}_K(\log n)\) bit operations.

The parameters \(k_\ell\) and \(h\), and hence \(B(n)\), are not supplied.
The algorithm is genuinely adaptive: after stage \(s\), it solves every
structural guess whose displayed budget is at most \(s\), verifies any
candidate factorization, and requests \(S_{s+1}\) only if none succeeds.
The true guess is present by stage \(B(n)\).

Since \(g\ge1\),
\[
 B(n)\le K-2.
\]
For \(K\ge4\), the unique structure attaining \(B(n)=K-2\) is the
single known block with \(K\) equal-multiplicity primes; for \(K=3\),
every budget equals one. For \(K\ge4\), a concrete corollary is that the first \(K-3\) values
already factor every input except possibly the class with exactly \(K\) primes, all
multiplicities equal, and
\(n/\gcd(n,\varphi(n))=\operatorname{rad}(n)\). Only that class can require
the final predetermined value \(S_{K-2}\).

This is a theorem relative to a dedicated exact divisor-sum oracle. It is
not an ordinary polynomial-time algorithm for integer factorization. The
budget is sufficient and, when \(B(n)>1\), is equation-count sharp for the
polynomial system used here; no information-theoretic or integer query lower
bound is claimed.

## 1. Totient recovery and the structural split

For \(T\ge\max(2,M)\),
\[
 \frac{\varphi(n)\sigma(n^T)}{n^{T+1}}
 =\prod_{p^a\parallel n}(1-p^{-(aT+1)})=:A_T.
\]
Since \(1-A_T<2^{-T}\), \(\varphi(n)\le2^T-1\), and
\(A_T>1-2^{-T}\),
\[
 \varphi(n)=\left\lfloor\frac{n^{T+1}}{\sigma(n^T)}\right\rfloor.
\]
Hence the first query gives \(\varphi(n)\).

Set
\[
 R=\frac n{\gcd(n,\varphi(n))},\qquad
 U=\gcd(n,R^M),\qquad V=n/U.
\]
The exponent of each prime in \(R\) is zero or one, and the largest prime
divisor occurs in \(R\). Therefore \(R=\operatorname{rad}(U)>1\), and \(U\)
is a product of complete prime-power components.

For \(j\ge1\), define
\[
 w_j=\frac{\gcd(U,R^j)}{\gcd(U,R^{j-1})},\qquad u_j=w_j/w_{j+1}.
\]
Every nontrivial \(u_j\) is the known squarefree product of the primes
dividing \(U\) that have exact multiplicity \(j\) in \(n\). Rename these known bases
\(u_1,\ldots,u_g\), with known multiplicities
\(a_1,\ldots,a_g\). The algorithm enumerates positive root counts
\(k_\ell\), an unknown-complement count \(h\) (zero exactly when \(V=1\)),
and ordered exponents \(1\le b_1,\ldots,b_h\le M\), subject to
\[
 k=\sum_\ell k_\ell+h\le K.
\]
This uses only \(\operatorname{poly}_K(M)\) guesses and does not assume that
\(\omega(n)\) is known.

For every possible exponent \(1\le a\le M\), the effective indices
\[
 m_{a,i}=aiJ+1,\qquad 1\le i\le K-2.
\]
These indices are pairwise coprime. Indeed, a common divisor for \(i<j\) divides
\(aJ(j-i)\), is coprime to \(aJ\), and hence divides \(j-i\). But
\(j-i\mid L\mid J\), while \(m_{a,i}\equiv1\pmod{j-i}\).

## 2. Equations for a structural guess

For a known block use
\[
 P_\ell(T)=T^{k_\ell}-e_{\ell,1}T^{k_\ell-1}
 +\cdots+(-1)^{k_\ell}u_\ell.
\]
For the complement use variables \(X_1,\ldots,X_h\) and
\[
 \prod_jX_j^{b_j}=V. \tag{2.1}
\]
Writing \(G_m(T)=1+\cdots+T^{m-1}\), each oracle value gives
\[
 \prod_\ell\operatorname{Res}_T(P_\ell,G_{m_{a_\ell,i}})
 \prod_jG_{m_{b_j,i}}(X_j)=S_i. \tag{2.2}
\]

The additional equation that saves one query is the already recovered
totient. From
\[
 \frac{\varphi(n)}n=
 \prod_\ell\frac{(-1)^{k_\ell}P_\ell(1)}{u_\ell}
 \prod_j\frac{X_j-1}{X_j},
\]
put
\[
 C=\frac{\varphi(n)}n\prod_\ell(-1)^{k_\ell}u_\ell
\]
and impose
\[
 \prod_\ell P_\ell(1)\prod_j(X_j-1)=C\prod_jX_j. \tag{2.3}
\]
The rational coefficient \(C\) is cleared by multiplying by \(n\).

A candidate is accepted only after its polynomials split into distinct
positive primes and reproduce \(n,\varphi(n)\), all multiplicities, and all
supplied oracle values.

## 3. Product-projective boundary argument

Use \([z_\ell:e_{\ell,1}:\cdots:e_{\ell,k_\ell-1}]\) on each known
coefficient block and
\[
 \widetilde P_\ell(T)=
 z_\ell(T^{k_\ell}+(-1)^{k_\ell}u_\ell)
 +\sum_{q=1}^{k_\ell-1}(-1)^qe_{\ell,q}T^{k_\ell-q}.
\]
For \(D_{\ell,i}=a_\ell iJ\), the homogeneous resultant is
\[
 {\cal R}_{\ell,i}=(-1)^{k_\ell D_{\ell,i}}
 \prod_{\substack{\zeta^{m_{a_\ell,i}}=1\\\zeta\ne1}}
 \widetilde P_\ell(\zeta).
\]
For \(X_j\), use \([x_j:z_j]\) with affine value \(x_j/z_j\) and
\[
 {\cal G}_m(x,z)=\sum_{q=0}^{m-1}x^qz^{m-1-q}.
\]
Equations (2.1)--(2.3) become
\[
 \prod_jx_j^{b_j}-V\prod_jz_j^{b_j}=0, \tag{3.1}
\]
\[
 \prod_\ell{\cal R}_{\ell,i}\prod_j{\cal G}_{m_{b_j,i}}(x_j,z_j)
 -S_i\prod_\ell z_\ell^{D_{\ell,i}}
       \prod_jz_j^{b_jiJ}=0, \tag{3.2}
\]
and
\[
 \prod_\ell\widetilde P_\ell(1)\prod_j(x_j-z_j)
 -C\prod_\ell z_\ell\prod_jx_j=0. \tag{3.3}
\]

At a boundary point, every right-hand term in (3.2) vanishes, so every query
index must be covered by a zero constituent on the left. Pairwise
coprimality gives the basic capacities:

* a finite known block covers at most \(k_\ell-1\) indices, because one
  polynomial root cannot hit two indices and at least one root is nonunit
  (\(|u_\ell|>1\));
* an infinite known block is \(TQ(T)\), \(\deg Q\le k_\ell-2\), and covers
  at most \(k_\ell-2\);
* a finite nonzero unknown coordinate covers at most one;
* an unknown zero or infinity covers none.

Equation (3.3) lowers the relevant total by one more. If a known block is
infinite, its right side is zero. If instead the boundary contains an
unknown infinity, (3.1) forces another unknown coordinate to be zero, again
making the right side of (3.3) zero. Neither the infinity nor the forced zero
makes its factor \(x_j-z_j\) vanish. Therefore some known constituent has
the additional root \(1\), or some other finite unknown coordinate equals
\(1\). For a finite known block, the roots \(1\), a nonunit root, and all
nontrivial effective-index roots are distinct. For an infinite block,
\(Q(1)=0\) spends one of its degree slots. An unknown value \(1\) cannot
cover a nontrivial effective index. Thus one unit of query capacity is
indeed lost.

The three nonuniform boundary budgets are consequently:

* an unknown infinity (and hence an unknown zero):
  \[
    \sum_\ell(k_\ell-1)+(h-2)-1=k-g-3\le k-4;
  \]
* \(h>0\), no unknown infinity, and a known infinite block:
  \[
    \bigl(\sum_\ell(k_\ell-1)-1\bigr)+(h-1)-1
    =k-g-3\le k-4;
  \]
* \(h=0,\ g\ge2\), and a known infinite block:
  \[
    \sum_\ell(k_\ell-1)-1-1=k-g-2\le k-4.
  \]

For a guess with \(h>0\), either of the first two cases applies and the
boundary capacity is at most \(k-g-3\). Therefore
\[
 s\ge\max(1,k-g-2)
\]
query equations exclude every boundary point. For \(h=0,g\ge2\), the third
case has capacity at most \(k-g-2\), so
\[
 s\ge\max(1,k-g-1)
\]
suffices.

If \(h=0,g=1\), equation (2.3) is the familiar known value of \(P_1(1)\)
and supplies no new constraint. For \(k=1\), the guessed polynomial is
\(P_1(T)=T-u_1\) and is checked directly. For \(k\ge2\), eliminate
\(e_{1,k-1}\). This leaves \(k-2\) variables and the old boundary capacity
\(k-3\), so \(s\ge\max(1,k-2)=\max(1,k-g-1)\) again suffices. The case
\(k=2\) has no remaining variables.

Thus every structural guess is zero-dimensional as soon as its budget
\[
 B_{\rm guess}=
 \begin{cases}
 \max(1,k-g-1),&h=0,\\
 \max(1,k-g-2),&h>0
 \end{cases}
\]
has been reached.

Under the Segre embedding, the boundary is a hyperplane section. A
positive-dimensional projective closed set meets every hyperplane, so
absence of boundary points proves that every retained affine system is
zero-dimensional.

## 4. Exact deterministic recovery

The number of variables depends only on \(K\), all degrees are
\(\operatorname{poly}_K(M)\), and all coefficient heights and oracle-value
bit lengths are \(\operatorname{poly}_K(M)\). Fixed-dimensional effective
ideal membership over \(\mathbb Q\) gives, for every coordinate, a nonzero
univariate eliminant of polynomial degree and height without assuming that
the ideal is radical. Exact rational polynomial factorization, Cartesian
enumeration of rational coordinate roots, and final primality and identity
checks therefore run in deterministic \(\operatorname{poly}_K(\log n)\)
bit time.

At stage \(s\), enumerate only guesses with
\(B_{\rm guess}\le s\). False guesses are harmless: a returned candidate
is accepted only after exact primality, distinctness, product, exponent,
totient, and oracle-value checks, so an early stop always gives the unique
correct prime factorization. The number of stages is at most \(K-2\), and
the number of guesses is \(O_K(M^K)\). The true guess is included at stage
\(B(n)\), proving the theorem without knowing \(B(n)\) in advance.

## 5. Why the budget is sharp for this system only

Let \(v=k-g\) be the number of affine variables before the normalized
totient and monomial equations are counted. If \(h=0\), there is no monomial
equation; with one fewer query than \(k-g-1\), at most \(v-1\) equations
remain through the true point. If \(h>0\), the monomial equation is present;
with one fewer query than \(k-g-2\), the total is again at most \(v-1\).
Krull's height theorem therefore leaves a positive-dimensional complex
component whenever these expressions exceed the one-query floor.

The worst uniform case makes the obstruction explicit. For
\(h=0,g=1\), using \(P(1)\) leaves \(v=k-2\) coefficient variables. With
only \(k-3=v-1\) cyclic-resultant equations, the leading polynomial
\[
 Q_e(Z)=\sum_{q=1}^{k-2}(-1)^qe_q(Z^{k-q-1}-1)
\]
ranges over all degree-at-most-\(k-2\) polynomials vanishing at \(1\).
Choosing one nontrivial \(m_i\)-th root \(\zeta_i\) for each query gives
the boundary point
\[
 Q_e(Z)\ \propto\ (Z-1)\prod_{i=1}^{k-3}(Z-\zeta_i).
\]
Pairwise coprimality makes these choices disjoint.

These are exact complex-algebraic obstructions to zero-dimensional
elimination by the displayed equations. They do not prove an integer
collision, query optimality, or impossibility for a different use of the
same oracle values.

## 6. Reproducibility

The dependency-free checker verifies the totient identity, the simultaneous
coprime-index construction, the normalized-totient identity, all three strengthened boundary budgets, the
instance-adaptive budget of every abstract structural guess, true query
identities on mixed samples, and finite-field counts of the displayed
uniform boundary points.

The exact source comparison is in \`UPSTREAM.md\`. No absolute priority or
query-optimality claim is made.
