# Asymptotic spectral reduction for the product/join calculus

**Supplement to 005 v2 — 7 October 2026.**  
This note records a structural consequence of the exact invariant calculus in
\`paper.md\`. The theorem below is a written proof, not a numerical conjecture.
It does **not** assert that the currently known self-similar construction is
optimal, and it does not assert publication priority.

## 1. The join spectral parameter

For a full-dimensional convex body \(K\) of dimension \(d\ge 1\), retain the
005 v2 notation

\[
R(K)=\frac{|\Pi K|}{|K|^{d-1}},\qquad
g(d)=\frac{d^d}{d!},\qquad
Q(K)=\frac{a(K)R(K)}{g(d)}.
\]

Define

\[
\boxed{\lambda(K)=Q(K)^{1/(d+1)}
=\left(\frac{a(K)R(K)}{g(d)}\right)^{1/(d+1)}.}
\]

For the formal zero-dimensional point put \(Q=1\) and \(\lambda=1\).
Every simplex also has \(Q=1\), because
\(a(T_d)=1/(d+1)\) and \(R(T_d)=(d+1)g(d)\).

The join identities from 005 v2 are

\[
Q(A*B)=Q(A)Q(B),\qquad
\dim(A*B)+1=(\dim A+1)+(\dim B+1).
\]

Consequently, if \(\dim A=r\), \(\dim B=s\), and
\(n=r+s+1\), then

\[
\boxed{
\lambda(A*B)=
\lambda(A)^{(r+1)/(n+1)}
\lambda(B)^{(s+1)/(n+1)}.}
\]

Thus a join takes a dimension-weighted geometric mean of the two
\(\lambda\)-values. In particular,

\[
\lambda(A*B)\le \max\{\lambda(A),\lambda(B)\},
\]

and the \(k\)-fold self-join preserves the parameter exactly:

\[
\boxed{\lambda(K^{*k})=\lambda(K).}
\]

Equivalently, in the coordinates

\[
D(K)=\dim K+1,\qquad H(K)=\frac1{a(K)},\qquad L(K)=\log Q(K),
\]

join is literally addition:

\[
(D,H,L)(A*B)=(D,H,L)(A)+(D,H,L)(B).
\]

This linearization separates the two roles of the operations: joins cannot
create a new record value of \(\lambda\), whereas products may do so.

## 2. Exact asymptotic reduction theorem

Let \(\mathcal F=\bigcup_{n\ge0}\mathcal F_n\) be any dimension-graded
family of convex bodies that contains the formal point in dimension zero and
is closed under joins. It may also be closed under other operations. The
point-generated product/join class \(\mathcal C\) of 005 v2 and the class of
all convex bodies are two examples. Define

\[
U_n=\sup_{K\in\mathcal F_n} R(K)^{1/n}\quad(n\ge1),
\qquad
\lambda_*=\sup_{K\in\mathcal F,\ \dim K\ge1}\lambda(K).
\]

The suprema may be interpreted in the extended positive reals. Whenever
\(\lambda_*<\infty\), the following is an ordinary finite identity.

### Theorem 2.1. Spectral reduction

\[
\boxed{\lim_{n\to\infty} U_n=e\,\lambda_*.}
\]

Hence the all-dimensional exponential growth problem for \(R\) is exactly
equivalent to the one-body optimization problem for \(\lambda\).

### Proof

Let \(K\in\mathcal F_n\). The general inequality proved in 005 v2 gives

\[
a(K)\ge\frac1{n+1}.
\]

Since \(Q(K)=a(K)R(K)/g(n)\) and
\(Q(K)\le\lambda_*^{\,n+1}\),

\[
R(K)=\frac{g(n)Q(K)}{a(K)}
\le (n+1)g(n)\lambda_*^{\,n+1}.
\]

Therefore

\[
U_n\le\bigl((n+1)g(n)\bigr)^{1/n}
\lambda_*^{\,1+1/n}.
\]

Stirling's formula gives

\[
\lim_{n\to\infty}g(n)^{1/n}=e,
\qquad
\lim_{n\to\infty}(n+1)^{1/n}=1,
\]

and hence

\[
\limsup_{n\to\infty}U_n\le e\lambda_*.
\tag{2.1}
\]

For the reverse inequality, fix any positive-dimensional
\(K\in\mathcal F_d\), and put \(\lambda=\lambda(K)\).
For every sufficiently large \(n\), write

\[
n+1=k(d+1)+r,\qquad 0\le r\le d.
\]

If \(r=0\), take

\[
L_n=K^{*k}.
\]

If \(r>0\), take

\[
L_n=K^{*k}*T_{r-1},
\]

where \(T_{r-1}\) is the \((r-1)\)-simplex. Since a simplex is the join
of \(r\) points, \(L_n\in\mathcal F_n\). Because \(Q(T_{r-1})=1\)
and \(Q\) is multiplicative under joins,

\[
Q(L_n)=Q(K)^k.
\]

Consequently

\[
\lambda(L_n)
=Q(L_n)^{1/(n+1)}
=\lambda^{\,k(d+1)/(n+1)}
=\lambda^{\,1-r/(n+1)}
\longrightarrow\lambda.
\tag{2.2}
\]

Using \(a(L_n)\le1\), also proved in 005 v2,

\[
R(L_n)^{1/n}
=g(n)^{1/n}
\lambda(L_n)^{(n+1)/n}
a(L_n)^{-1/n}
\ge
g(n)^{1/n}\lambda(L_n)^{(n+1)/n}.
\]

Equations (2.2) and \(g(n)^{1/n}\to e\) imply

\[
\liminf_{n\to\infty}U_n\ge e\lambda(K).
\]

Taking the supremum over all fixed \(K\in\mathcal F\) yields

\[
\liminf_{n\to\infty}U_n\ge e\lambda_*.
\tag{2.3}
\]

Combining (2.1) and (2.3) proves the theorem. \(\square\)

### Remark 2.2. Relation with the product/Fekete argument

If \(\mathcal F\) is also closed under Cartesian products, the product
identity

\[
R(A\times B)=R(A)R(B)
\]

already makes the fixed-dimensional suprema supermultiplicative, so a
Fekete-lemma argument gives existence of their exponential growth rate
whenever an exponential upper bound is available. The additional content
of Theorem 2.1 is the exact identification of that rate with the one-body
spectral supremum \(e\lambda_*\), together with the fact that the same
identification only needs join closure, not product closure.

In particular, for the unrestricted Schneider projection problem, if

\[
M_n=\sup\{R(K):K\subset\mathbb R^n
\text{ a full-dimensional convex body}\},
\]

and

\[
\lambda_{\rm all}
=\sup_K
\left(\frac{a(K)R(K)}{g(\dim K)}\right)^{1/(\dim K+1)},
\]

then, in the extended positive reals,

\[
\boxed{\lim_{n\to\infty}M_n^{1/n}=e\lambda_{\rm all}.}
\]

Classical dimension-dependent upper bounds make the quantities finite; this
identity is a reformulation of the asymptotic extremal problem, not a claim
that the finite value of \(\lambda_{\rm all}\) is determined here.

## 3. Consequences for the point-generated product/join class

For the recursive class \(\mathcal C\) of 005 v2, put

\[
\Gamma_{\mathcal C}
=\lim_{n\to\infty}
\sup_{K\in\mathcal C_n}R(K)^{1/n}.
\]

Theorem 2.1 gives the exact reformulation

\[
\boxed{
\Gamma_{\mathcal C}
=e\sup_{K\in\mathcal C}
\left(\frac{a(K)R(K)}{g(\dim K)}\right)^{1/(\dim K+1)}.}
\tag{3.1}
\]

The certified self-similar sequence already in 005 v2 has root limit
\(\Lambda\) with

\[
2.8534<\Lambda<2.8535.
\]

Therefore (3.1) in particular proves

\[
\Gamma_{\mathcal C}\ge\Lambda>2.8534.
\]

More conceptually, an asymptotically optimal construction need not itself
converge through one fixed recursive recipe: it is enough to find
finite-dimensional bodies whose \(\lambda\)-values approach
\(\lambda_*\), because repeated joins promote each such finite body to an
all-dimensional exponential construction with limiting rate
\(e\lambda(K)\).

Conversely, no join node can be the first place where a strict
\(\lambda\)-record appears. Any strict record in a product/join expression
must occur at a product node. Joins are nevertheless essential because
they alter the auxiliary state \(a\) while preserving a self-join's
\(\lambda\), and can thereby prepare a body for a later product improvement.

## 4. Product formula in the spectral variables

The product identity gives an exact update rule useful for the remaining
optimization problem. If \(A,B\) have dimensions \(r,s>0\), then

\[
Q(A\times B)
=
Q(A)Q(B)
\frac{g(r)g(s)}{g(r+s)}
\frac{r\,a(A)+s\,a(B)}
{(r+s)a(A)a(B)}.
\tag{4.1}
\]

For an \(m\)-fold Cartesian power,

\[
\boxed{
Q(K^m)
=
a(K)^{1-m}Q(K)^m
\frac{g(d)^m}{g(md)}.}
\tag{4.2}
\]

Thus

\[
\boxed{
\lambda(K^m)^{md+1}
=
a(K)^{1-m}
\frac{g(d)^m}{g(md)}
\lambda(K)^{m(d+1)}.}
\tag{4.3}
\]

Equations (4.1)--(4.3), together with the join averaging law, reduce the
open asymptotic problem to controlling product gains in the two state
variables \((d,a)\) while \(\lambda\) records the objective.

## 5. Evidence and remaining gap

Exact finite-hull calculations already supplied in 005 v2 prove the sharp
recursive-class maximum through dimension fourteen. Additional exploratory
dynamic programming performed after that release found that the
\(T_5\)-based orbit

\[
K_{j+1}=(K_j\times K_j)*(K_j\times K_j)
\]

continues to lie on the extremal finite-hull trajectory through the checked
range, and searches over small fixed homogeneous product/join recursion
trees did not produce a larger limiting rate. These observations are
**discovery evidence only** and are not used in Theorem 2.1.

The highest-value unresolved statement is now more precise than
"find a dimension-uniform Bellman envelope":

\[
\textbf{determine }
\lambda_*=
\sup_{K\in\mathcal C}
\left(\frac{a(K)R(K)}{g(\dim K)}\right)^{1/(\dim K+1)}.
\]

A proof that the current self-similar orbit approaches this supremum would,
by Theorem 2.1, immediately determine the exact asymptotic growth constant
of the entire product/join class. Alternatively, any finite body with a
larger \(\lambda\) gives, automatically and rigorously, a better
all-dimensional exponential construction.

## 6. Scope and provenance

This supplement uses only the exact product/join calculus and
\(1/(d+1)\le a(K)\le1\) proved in 005 v2, plus the standard asymptotic
\(g(d)^{1/d}\to e\). It does not rely on floating-point optimization,
a solver oracle, or the exploratory searches mentioned in Section 5.

The product identity and projection-body background are inherited and
attributed in 005 v2. A focused public search did not locate this exact
spectral reformulation, but that is not a comprehensive novelty search.
No first-priority, best-known unrestricted bound, external peer review, or
journal-tier claim is made here.
