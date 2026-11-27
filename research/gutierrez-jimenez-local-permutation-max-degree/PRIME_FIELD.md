# Maximum degree with coefficients in the prime field

**Theorem 2.** For every prime power \(q=p^r>3\) and integer \(n\geq1\), there is a local permutation polynomial in \(\mathbb F_p[X_1,\ldots,X_n]\) on \(\mathbb F_q^n\) of total degree \(n(q-2)\).

This theorem does not assert that the particular recurrence (1) always attains the maximum: [PROOF.md](PROOF.md) gives counterexamples to that separate claim. The new general construction below is a Frobenius-equivariant exchange of two orbits. Previously established ranges are credited in [SOURCES.md](SOURCES.md).

## 1. A sufficient condition using an additive union of cosets

Let \(A\subseteq\mathbb F_q\) be stable under addition by 1 and let \(\sigma\) be a permutation commuting with Frobenius \(x\mapsto x^p\). Write \(Z=\sigma^{-1}(A)\). Require that \(A\) is Frobenius-stable, \(|Z|=0\) in \(\mathbb F_p\), and \(s=\sum_{z\in Z}z\ne0\). Define, as a polynomial function,
\[
G_n(x_1,\ldots,x_n)
=\sum_{i=1}^n\sigma(x_i)+\prod_{i=1}^n 1_Z(x_i).
\tag{1}
\]
Once all other variables are fixed, the varying-variable slice is either \(\sigma(x)+C\) or \(\sigma(x)+1_Z(x)+C\). In the second case the values in \(A\) are translated by 1 within \(A\), and values outside \(A\) are unchanged before the common shift. Both slices are permutations.

A univariate function \(u\) has its reduced representative over \(\mathbb F_p\) exactly when it commutes with Frobenius: in a field of characteristic \(p\), \(u(x)^p=\sum_i c_i^p (x^p)^i\), so uniqueness of representation and bijectivity of Frobenius give \(c_i^p=c_i\). This applies to \(\sigma\) and \(1_Z\), since \(Z\) is Frobenius-stable and its indicator is prime-field valued. Hence (1) uses only prime-field coefficients. The coefficient of \(X^{q-1}\) in \(1_Z\) is \(-|Z|=0\); the coefficient of \(X^{q-2}\) is \(-s\ne0\) by (4) of [PROOF.md](PROOF.md). For \(n\geq2\) the coefficient of \(\prod x_i^{q-2}\) in (1) is therefore \((-s)^n\ne0\), since the first sum contributes no mixed monomial.

When \(n=1\), use the transposition \(t(X)=X+\sum_{i=0}^{q-2}X^i\), of degree \(q-2\) and with coefficients in \(\mathbb F_p\), instead.

## 2. The orbit exchange over nonprime fields of odd characteristic

Assume first that \(p\geq5\) and \(r\geq2\). Take a prime divisor \(\lambda\) of \(r\), and work initially in \(E=\mathbb F_{p^\lambda}\subseteq\mathbb F_q\). Write \(\varphi(x)=x^p\); each element of \(E\setminus\mathbb F_p\) lies on a \(\lambda\)-cycle. The trace of an element of that degree is the sum of its orbit. We choose disjoint \(\lambda\)-cycles \(C\subseteq A\), \(B\subseteq E\setminus A\) with different traces. Exchange them using any bijection sending a chosen point of \(C\) to a chosen point of \(B\) and sending their successive Frobenius powers to one another; swap in both directions, fixing every other element of \(\mathbb F_q\). This is a Frobenius-equivariant permutation \(\sigma\). If \(A\) is a union of additive \(\mathbb F_p\)-cosets then \(|A|=0\) in the field and \(\sum_{a\in A}a=0\) (here \(p\) is odd). Replacing \(C\) by \(B\) in \(A\) gives precisely \(Z=\sigma^{-1}(A)\), with the same cardinality and nonzero sum \(\operatorname{Tr}_{E/\mathbb F_p}(b)-\operatorname{Tr}_{E/\mathbb F_p}(c)\).

- **If \(\lambda=p\):** take a root \(a\) of \(X^p-X=1\). Its successive Frobenius conjugates are \(a,a+1,\ldots,a+(p-1)\), so \(a\in E\) and they form one \(p\)-cycle, the full coset \(A=C=a+\mathbb F_p\), of trace zero. Choose \(b\in E\) of nonzero trace; the trace polynomial is nonzero of degree below the field size and defines an Fp-linear map into the prime field, so it is onto. Such \(b\) cannot be fixed by Frobenius because the trace of every prime-field element is zero in degree \(p\). Its orbit \(B\) is a \(p\)-cycle outside \(A\). This branch also works for \(p=3\), and the existence result when \(p\mid r\) is known from the authors' follow-up Theorem 2 via a different choice of permutation.
- **If \(\lambda\ne p\):** choose any \(a\in E\setminus\mathbb F_p\) and put
  \[
  A=\bigcup_{i=0}^{\lambda-1}(\varphi^i(a)+\mathbb F_p).
  \]
  The displayed cosets are distinct. If \(\varphi^j(a)-a=d\in\mathbb F_p\) for \(0<j<\lambda\), applying \(\varphi^j\) repeatedly gives \(\lambda d=0\), so \(d=0\) and \(a\) would be fixed by a generator of this prime-order Frobenius group. Thus \(|A|=p\lambda\), all in \(E\setminus\mathbb F_p\), and \(A\) comprises \(p\) full \(\lambda\)-cycles, one through each of the points \(a+c\) with \(c\in\mathbb F_p\). Their trace values \(\operatorname{Tr}(a)+\lambda c\) run through the entire prime field. Because \(p^{\lambda-1}\ge5^{\lambda-1}>\lambda+1\) for \(\lambda\ge2\), we have \(p^\lambda-p>p\lambda\). Take \(b\in E\setminus(A\cup\mathbb F_p)\). Its \(\lambda\)-cycle \(B\) is outside the Frobenius-invariant set \(A\). Choose one of the cycles \(C\) of \(A\) whose trace is different from that of \(B\).

The construction is made in the subfield only for convenience; all maps and indicators in (1) are interpolated on the target field \(\mathbb F_q\), with \(\sigma\) fixing the rest. The coefficient calculation in §1 uses \(q\), not \(p^\lambda\). Therefore it gives the required degree for every target extension containing this subfield.

## 3. Remaining cases

- **Characteristic three:** for \(q=3^r>3\) we have \(r\geq2\) and (3) of [PROOF.md](PROOF.md) gives \(s_j=1\) for every \(j\). Recurrence (1) of that proof then has maximum degree for every \(n\geq2\), and its coefficients lie in the prime field because inversion, addition and the transposition are Frobenius-equivariant.
- **Characteristic two:** use the general construction in §1 with \(\sigma\) the identity and \(A=Z=\{0,1\}\). The sum of the two points is 1 and their count is zero in characteristic two. The original paper's Theorem 4 already gives this characteristic via the indicator of the complement instead.
- **Prime field \(q=p>3\):** this range already follows from the original Theorem 5 with \(b=p-2\), since \(1<b<p-1\) and \(\gcd(b,p-1)=1\). To recall its short argument, iterate the \(b\)-ary local permutation \((y_1+\cdots+y_b)^b\) on a complete tree with \(b^k\) leaves. It is homogeneous of degree \(b^k\) and its monomial containing all leaves has coefficient \((b!)^{(b^k-1)/(b-1)}\ne0\): to involve every block at each node, the outer exponent distribution must be exactly one per block. Substitute inversion at each leaf. The unique all-leaf monomial becomes the maximal monomial \(\prod X_i^{p-2}\); other monomials miss a leaf and cannot contribute even after reduction. For any \(n\le b^k\), fix the extra variables at values where the coefficient of the remaining maximal monomial is nonzero. Such a specialization exists because that coefficient contains the nonzero all-leaf coefficient and is a nonzero reduced polynomial. These specializations lie in \(\mathbb F_p\). This proves the stated range, with the single-variable case as above.

Each branch supplies an explicit recipe in the target field, and the cases cover every \(q>3\). The verifier recovers orbit exchanges in characteristics 3, 5 and 7 (including \(q=25\), where the original recurrence fails), checks the local bijections and Frobenius equivariance, and checks leading coefficients by interpolation. Neither the existence claim nor the coefficient theorem depends on these finite checks.
