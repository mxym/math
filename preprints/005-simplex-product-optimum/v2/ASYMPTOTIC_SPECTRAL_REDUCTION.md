# Asymptotic spectral reduction for the product/join calculus

**Supplement to 005 v2 — 7 October 2026.**  
This note records a structural consequence of the exact invariant calculus in
`paper.md`.  The theorem below is a written proof, not a numerical conjecture.
It does **not** assert that the currently known self-similar construction is
optimal, and it does not assert publication priority.

## 1. The join spectral parameter

For a full-dimensional convex body (K) of dimension (dge 1), retain the
005 v2 notation

[
 R(K)=rac{|Pi K|}{|K|^{d-1}},qquad
 g(d)=rac{d^d}{d!},qquad
 Q(K)=rac{a(K)R(K)}{g(d)}.
]

Define

[
 oxed{lambda(K)=Q(K)^{1/(d+1)}
 =left(rac{a(K)R(K)}{g(d)}ight)^{1/(d+1)}.}
]

For the formal zero-dimensional point put (Q=1) and (lambda=1).
Every simplex also has (Q=1), because
(a(T_d)=1/(d+1)) and (R(T_d)=(d+1)g(d)).

The join identities from 005 v2 are

[
 Q(A*B)=Q(A)Q(B),qquad
 dim(A*B)+1=(dim A+1)+(dim B+1).
]

Consequently, if (dim A=r), (dim B=s), and
(n=r+s+1), then

[
 oxed{
 lambda(A*B)=
 lambda(A)^{(r+1)/(n+1)}
 lambda(B)^{(s+1)/(n+1)}.}
]

Thus a join takes a dimension-weighted geometric mean of the two
(lambda)-values.  In particular,

[
 lambda(A*B)le max{lambda(A),lambda(B)},
]

and the (k)-fold self-join preserves the parameter exactly:

[
 oxed{lambda(K^{*k})=lambda(K).}
]

Equivalently, in the coordinates

[
 D(K)=dim K+1,qquad H(K)=rac1{a(K)},qquad L(K)=log Q(K),
]

join is literally addition:

[
 (D,H,L)(A*B)=(D,H,L)(A)+(D,H,L)(B).
]

This linearization separates the two roles of the operations: joins cannot
create a new record value of (lambda), whereas products may do so.

## 2. Exact asymptotic reduction theorem

Let (mathcal F=igcup_{nge0}mathcal F_n) be any class generated from a
point and closed under joins.  It may also be closed under other operations;
the point-generated product/join class (mathcal C) of 005 v2 is the main
example.  Define

[
 U_n=sup_{Kinmathcal F_n} R(K)^{1/n}quad(nge1),
 qquad
 lambda_*=sup_{Kinmathcal F, dim Kge1}lambda(K).
]

The suprema may be interpreted in the extended positive reals.  Whenever
(lambda_*<infty), the following is an ordinary finite identity.

### Theorem 2.1. Spectral reduction

[
 oxed{lim_{n	oinfty} U_n=e,lambda_*.}
]

Hence the all-dimensional exponential growth problem for (R) is exactly
equivalent to the one-body optimization problem for (lambda).

### Proof

Let (Kinmathcal F_n).  The general inequality proved in 005 v2 gives

[
 a(K)gerac1{n+1}.
]

Since (Q(K)=a(K)R(K)/g(n)) and
(Q(K)lelambda_*^{,n+1}),

[
 R(K)=rac{g(n)Q(K)}{a(K)}
 le (n+1)g(n)lambda_*^{,n+1}.
]

Therefore

[
 U_nleigl((n+1)g(n)igr)^{1/n}
       lambda_*^{,1+1/n}.
]

Stirling's formula gives

[
 lim_{n	oinfty}g(n)^{1/n}=e,
 qquad
 lim_{n	oinfty}(n+1)^{1/n}=1,
]

and hence

[
 limsup_{n	oinfty}U_nle elambda_*.
 	ag{2.1}
]

For the reverse inequality, fix any positive-dimensional
(Kinmathcal F_d), and put (lambda=lambda(K)).
For every sufficiently large (n), write

[
 n+1=k(d+1)+r,qquad 0le rle d.
]

If (r=0), take

[
 L_n=K^{*k}.
]

If (r>0), take

[
 L_n=K^{*k}*T_{r-1},
]

where (T_{r-1}) is the ((r-1))-simplex.  Since a simplex is the join
of (r) points, (L_ninmathcal F_n).  Because (Q(T_{r-1})=1)
and (Q) is multiplicative under joins,

[
 Q(L_n)=Q(K)^k.
]

Consequently

[
 lambda(L_n)
 =Q(L_n)^{1/(n+1)}
 =lambda^{,k(d+1)/(n+1)}
 =lambda^{,1-r/(n+1)}
 longrightarrowlambda.
 	ag{2.2}
]

Using (a(L_n)le1), also proved in 005 v2,

[
 R(L_n)^{1/n}
 =g(n)^{1/n}
  lambda(L_n)^{(n+1)/n}
  a(L_n)^{-1/n}
 ge
 g(n)^{1/n}lambda(L_n)^{(n+1)/n}.
]

Equations (2.2) and (g(n)^{1/n}	o e) imply

[
 liminf_{n	oinfty}U_nge elambda(K).
]

Taking the supremum over all fixed (Kinmathcal F) yields

[
 liminf_{n	oinfty}U_nge elambda_*.
 	ag{2.3}
]

Combining (2.1) and (2.3) proves the theorem. (square)

## 3. Consequences for the point-generated product/join class

For the recursive class (mathcal C) of 005 v2, put

[
 Gamma_{mathcal C}
 =lim_{n	oinfty}
   max_{Kinmathcal C_n}R(K)^{1/n}.
]

The maximum can be replaced by a supremum without affecting the argument.
Theorem 2.1 gives the exact reformulation

[
 oxed{
 Gamma_{mathcal C}
 =esup_{Kinmathcal C}
 left(rac{a(K)R(K)}{g(dim K)}ight)^{1/(dim K+1)}.}
 	ag{3.1}
]

The certified self-similar sequence already in 005 v2 has root limit
(Lambda) with

[
 2.8534<Lambda<2.8535.
]

Therefore (3.1) in particular proves

[
 Gamma_{mathcal C}geLambda>2.8534.
]

More conceptually, an asymptotically optimal construction need not itself
converge through one fixed recursive recipe: it is enough to find
finite-dimensional bodies whose (lambda)-values approach
(lambda_*), because repeated joins promote each such finite body to an
all-dimensional exponential construction with limiting rate
(elambda(K)).

Conversely, no join node can be the first place where a strict
(lambda)-record appears.  Any strict record in a product/join expression
must occur at a product node.  Joins are nevertheless essential because
they alter the auxiliary state (a) while preserving a self-join's
(lambda), and can thereby prepare a body for a later product improvement.

## 4. Product formula in the spectral variables

The product identity gives an exact update rule useful for the remaining
optimization problem.  If (A,B) have dimensions (r,s>0), then

[
 Q(A	imes B)
 =
 Q(A)Q(B)
 rac{g(r)g(s)}{g(r+s)}
 rac{r,a(A)+s,a(B)}
      {(r+s)a(A)a(B)}.
 	ag{4.1}
]

For an (m)-fold Cartesian power,

[
 oxed{
 Q(K^m)
 =
 a(K)^{1-m}Q(K)^m
 rac{g(d)^m}{g(md)}.}
 	ag{4.2}
]

Thus

[
 oxed{
 lambda(K^m)^{md+1}
 =
 a(K)^{1-m}
 rac{g(d)^m}{g(md)}
 lambda(K)^{m(d+1)}.}
 	ag{4.3}
]

Equations (4.1)--(4.3), together with the join averaging law, reduce the
open asymptotic problem to controlling product gains in the two state
variables ((d,a)) while (lambda) records the objective.

## 5. Evidence and remaining gap

Exact finite-hull calculations already supplied in 005 v2 prove the sharp
recursive-class maximum through dimension fourteen.  Additional exploratory
dynamic programming performed after that release found that the
(T_5)-based orbit

[
 K_{j+1}=(K_j	imes K_j)*(K_j	imes K_j)
]

continues to lie on the extremal finite-hull trajectory through the checked
range, and searches over small fixed homogeneous product/join recursion
trees did not produce a larger limiting rate.  These observations are
**discovery evidence only** and are not used in Theorem 2.1.

The highest-value unresolved statement is now more precise than
"find a dimension-uniform Bellman envelope":

[
 	extbf{determine }
 lambda_*=
 sup_{Kinmathcal C}
 left(rac{a(K)R(K)}{g(dim K)}ight)^{1/(dim K+1)}.
]

A proof that the current self-similar orbit attains this supremum would,
by Theorem 2.1, immediately determine the exact asymptotic growth constant
of the entire product/join class.  Alternatively, any finite body with a
larger (lambda) gives, automatically and rigorously, a better
all-dimensional exponential construction.

## 6. Scope and provenance

This supplement uses only the exact product/join calculus and
(1/(d+1)le a(K)le1) proved in 005 v2, plus the standard asymptotic
(g(d)^{1/d}	o e).  It does not rely on floating-point optimization,
a solver oracle, or the exploratory searches mentioned in Section 5.

The product identity and projection-body background are inherited and
attributed in 005 v2.  A focused public search did not locate this exact
spectral reformulation, but that is not a comprehensive novelty search.
No first-priority, best-known unrestricted bound, external peer review, or
journal-tier claim is made here.
