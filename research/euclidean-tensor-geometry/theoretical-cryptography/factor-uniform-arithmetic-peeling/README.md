# Arithmetic peeling on the last uniform divisor-sum branch

## Result

Fix \(K\ge4\), let \(M=\lceil\log_2n\rceil\),
\(c=\lceil\log_2(K-1)\rceil\), \(L=(K-2)!\), and choose
\[
 J=L\left\lceil\frac{\max(2,M(M+c))}{L}\right\rceil.
\]
The predetermined oracle stream is
\[
 S_i=\sigma(n^{iJ}),\qquad 1\le i\le K-3.
\]

The instance-adaptive bounded-\(\omega\) theorem leaves only one possible
\(K-3\)-query exception: \(n=u^a\), where \(u\) is squarefree with exactly
\(K\) prime factors and
\[
 R=n/\gcd(n,\varphi(n))=u.
\]
The first query still recovers \(\varphi(n)\), so \(u\), \(a\), and
\(\varphi(u)=\varphi(n)/u^{a-1}\) are known.

Write
\[
 u=p_1p_2\cdots p_K,\qquad 2\le p_1<p_2<\cdots<p_K.
\]

> **Theorem (two arithmetic peeling criteria).** The first \(K-3\) values
> factor this remaining uniform input deterministically in
> \(\operatorname{poly}_K(\log n)\) bit operations if either
>
> 1. \(1<\gcd(u,S_1)<u\); or
> 2. \(p_2/p_1\ge1+1/M\).

The conditions are sufficient, not necessary. The gap itself is not tested
without knowing the primes; instead the algorithm always computes the exact
integer-root candidate and accepts it only after primality and divisibility
verification. A successful peel is therefore self-certifying, but does not
by itself certify the displayed gap. The theorem narrows the
inputs requiring the final oracle value to those for which the smallest
primes are close and the simple gcd split is trivial. If neither peel
succeeds, the already predetermined value \(S_{K-2}\) completes the
factorization by the instance-adaptive theorem; choosing
\(L=(K-2)!\) from the start keeps this appended index coprime to the
earlier effective indices.

A second theorem below shows that both shortcuts can fail simultaneously
on infinite families for every polylogarithmic range of effective indices.
That is a limitation of these two arithmetic peels, not a lower bound for
the divisor-sum oracle or for integer factorization.

## 1. The exact first-prime statistic

Put
\[
 m=aJ+1,\qquad G_m(X)=1+X+\cdots+X^{m-1}.
\]
Since
\[
 S_1=\prod_{i=1}^K G_m(p_i)
 \quad\text{and}\quad
 \varphi(u)=\prod_{i=1}^K(p_i-1),
\]
the integer
\[
 A:=u^m-\varphi(u)S_1
   =u^m-\prod_{i=1}^K(p_i^m-1)
\]
is known and positive. After division by \(u^m\),
\[
 \frac A{u^m}=1-\prod_{i=1}^K(1-p_i^{-m}).
\]
The union bound and its strict one-term lower bound give
\[
 p_1^{-m}<\frac A{u^m}
 <p_1^{-m}\left(1+(K-1)(p_1/p_2)^m\right). \tag{1.1}
\]

Define \(q\) without numerical approximation as the least positive integer
satisfying
\[
 A q^m\ge u^m. \tag{1.2}
\]
It is found by binary search and exact powering.

### Exact recovery criterion

More generally, with \(k\) primes in \(u\), put
\[
 \Delta=(k-1)(p_1/p_2)^m.
\]
If
\[
 \Delta\le\frac m{p_1-1}, \tag{1.3}
\]
then \(q=p_1\). Indeed, the lower bound in (1.1) gives
\(Ap_1^m>u^m\). Bernoulli's inequality gives
\[
 \left(\frac{p_1}{p_1-1}\right)^m
 \ge1+\frac m{p_1-1}\ge1+\Delta.
\]
Together with the strict upper bound in (1.1), this yields
\[
 A(p_1-1)^m<u^m.
\]
Thus (1.2) selects exactly \(p_1\).

The output is always checked for primality and divisibility before it is
used, so an input outside the sufficient condition cannot cause a false
factor.

## 2. Why the stated gap guarantees the criterion

Assume \(p_2/p_1\ge1+1/M\). For every integer \(M\ge1\),
\[
 (1+1/M)^M\ge2.
\]
Since \(m=aJ+1\ge J+1\ge M(M+c)\),
\[
 \Delta
 \le(K-1)(1+1/M)^{-m}
 \le(K-1)2^{-m/M}
 \le2^{-M}.
\]
Also \(p_1-1<n\le2^M\), and hence
\[
 2^{-M}<\frac m{p_1-1}.
\]
Condition (1.3) follows, so exact binary search recovers \(p_1\).

For each available query, divide out the verified factor:
\[
 S_i'=\frac{S_i}{G_{aiJ+1}(p_1)}.
\]
These are exactly the divisor sums for
\[
 n'=(u/p_1)^a,
\]
which has at most \(K-1\) distinct prime factors. The indices
\(aiJ+1\), \(1\le i\le K-3\), are pairwise coprime because
\(J\) is a multiple of \((K-2)!\). The fixed-\((K-1)\) bounded-\(\omega\)
reconstruction therefore uses the same \(K-3\) values and finishes the
factorization. The larger quadratic choice of \(J\) remains
\(\operatorname{poly}_K(\log n)\) in exponent and bit size.

## 3. The proper-gcd split

Let
\[
 d=\gcd(u,S_1).
\]
If \(1<d<u\), then \(u=d(u/d)\) is a known partition into two nontrivial
squarefree products. No factorization of \(d\) is assumed. Treat the two
products as separate known blocks of the same exponent \(a\).

The product-projective reconstruction depends only on knowing each block
product and exponent; distinct blocks need not have distinct exponents.
Here \(h=0\), \(g=2\), and \(k=K\), so its instance budget is
\[
 \max(1,k-g-1)=K-3.
\]
Thus the same \(K-3\) oracle values factor both blocks and hence \(n\).

## 4. Infinite families where both peels fail

The preceding criteria do not dispose of every uniform input.

> **Proposition.** Fix \(k\ge4\), \(C>0\), and
> \(0<\varepsilon<\delta<1\). For arbitrarily large \(X\), there are
> odd primes
> \[
> X\le p_1<\cdots<p_k\le3X/2
> \]
> lying in one interval of length \(D=\lfloor X^\delta\rfloor\), with
> pairwise gaps at least \(X^\varepsilon\), such that for every integer
> \(1\le m\le(\log X)^C\):
>
> * \(\gcd(\prod_i p_i,\prod_iG_m(p_i))=1\);
> * the integer candidate (1.2) is strictly smaller than \(p_1\).

### Construction

Call a prime \(p\in[X,3X/2]\) bad if it divides a nonzero integer
\[
 d^m-1,\qquad 1\le |d|\le D,\quad
 1\le m\le\lfloor(\log X)^C\rfloor.
\]
The logarithm of the product of the absolute values of all these nonzero
integers is
\[
 O\!\left(D(\log X)^{2C+1}\right).
\]
Every bad prime is at least \(X\), so there are
\[
 O\!\left(D(\log X)^{2C}\right)=o(X/\log X)
\]
bad primes. By the prime number theorem, \([X,3X/2]\) still contains
\(\gg X/\log X\) good primes.

Partition the interval into \(O(X/D)\) bins of length \(D\). If no bin
contained \(k\) good primes separated by at least \(X^\varepsilon\), greedy
selection in every bin would bound the total number of good primes by
\[
 O_k(X^{1-\delta+\varepsilon})=o(X/\log X),
\]
a contradiction. Select such \(p_1,\ldots,p_k\) in one bin. For large
\(X\), every selected gap exceeds \(X^\varepsilon>1\); because the primes
are odd, their differences are nonzero even integers, so the excluded
integers \(d^m-1\) are indeed nonzero.

Since their ratios are below \(2\), no selected prime divides another minus
one: a positive multiple would have to be exactly that prime, making the
larger prime even. Hence the resulting uniform input is in the cross-free
branch.

### Trivial gcd for all the stated indices

For distinct selected primes \(p,q\), write \(d=q-p\), so
\(1\le|d|\le D\). The congruence \(q\equiv1\pmod p\) is impossible because
it would give the even prime \(q=p+1\). Therefore, if
\(p\mid G_m(q)\), then \(q^m\equiv1\pmod p\), so
\(p\mid d^m-1\), contrary to goodness. Also
\(G_m(p)\equiv1\pmod p\). Thus no selected prime divides the product of
the \(G_m(p_i)\), proving the gcd assertion.

### Failure of the root candidate

Uniformly for \(m\le(\log X)^C\),
\[
 (p_1/p_i)^m=1+o(1)
\]
because \(mD/X\to0\). Inclusion-exclusion in the definition of \(A\) gives
\[
 \eta_m:=p_1^mA/u^m=k+o(1);
\]
all terms involving at least two inverse prime powers are \(O_k(X^{-m})\).
The real threshold in (1.2) is
\[
 (u^m/A)^{1/m}=p_1\eta_m^{-1/m}.
\]
Since \(\eta_m\) stays bounded away from \(1\),
\[
 p_1-p_1\eta_m^{-1/m}\gg_k p_1/m\to\infty
\]
uniformly in the stated range. Its ceiling is therefore below \(p_1\), and
cannot divide \(u\).

## 5. Scope and reproducibility

The positive theorem is a deterministic sufficient condition for saving
the final oracle query on the last uniform branch. The proposition proves
only that the two displayed peels are incomplete, even for medium-spaced
primes and polylogarithmic effective indices. It does not exclude other
integer, \(p\)-adic, lattice, or global uses of the same oracle values.

For fixed \(k\) and multiplicity \(a\), the scheduled effective indices
are \(O_{k,a}((\log X)^2)\). Thus choosing any \(C>2\) in the proposition
covers the entire predetermined schedule for all sufficiently large \(X\).

The checker verifies the exact statistic, the binary-search candidate,
the gap implication, quotient-query identities after a successful peel,
proper gcd partitions, and finite examples illustrating the simultaneous
failure regime. Source locations and prior scope are recorded in
\`UPSTREAM.md\`.
