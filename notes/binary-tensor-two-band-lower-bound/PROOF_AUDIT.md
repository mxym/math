# Proof audit and trust boundary

Date: 7 October 2026.

## Claims checked

The note proves one new mathematical statement: the explicit two-band tensors
\(U_p\), for every \(p\ge10\), have projection maximum exactly \(2\), the
displayed diagonal Gram matrix, and therefore the stated lower bound for the
best binary complete-commutator rigidity constant.  The asymptotic corollary
raises the rigorous lower leading constant from \(2^{-3/4}\) to
\(\sqrt{(2+\sqrt2)/(2(3+\sqrt2))}\).

The following points were re-derived during self-audit rather than inferred
from numerical experiments.

1. The distance formula is an orthogonal-projection identity.
2. The complete residual counts every ordered contraction with multiplicity
   \(\binom{p-2}{k}\); the Binet--Cauchy calculation gives \(R_p^2=\det G\).
3. For even \(p\), the projection energy is bounded by a coefficientwise
   comparison with \((a+b)^p\).  The only nontrivial central coefficient is
   controlled by \(\binom p4\), and the proof includes an induction-style
   monotonicity gate valid from \(p=10\) onward.
4. For odd \(p\), the middle cross term is nonpositive and the remaining
   polynomial is coefficientwise dominated by \((a+b)^p\).
5. The coordinate axes attain projection energy \(2\), so the upper estimate
   is exact, not merely a bound.
6. The four terms in \(G_{12}\) cancel exactly.  The two diagonal formulas
   were expanded independently in \(\mathbb Q(\sqrt2)\).
7. The asymptotic simplification and the strict comparison with
   \(2^{-3/4}\) use exact algebra.

## Computational replay

checks/check_exact.py uses the Python standard library only.  Its Q(sqrt(2))
type performs exact Fraction arithmetic and exact sign decisions.  It checks
orders 10 through 120 as diagnostics, separately checks the universal
integer gates used in the proof, and contains corrupted-formula negative
controls.  verify.py runs the same checker under ordinary Python and -O and
requires identical output.

The universal theorem does not follow from the finite loop.  Its all-order
scope is supplied by the written inequalities in Sections 3--5 of paper.md.

## Limits

This is a model-conducted proof and self-audit, not external peer review.  No
Lean formalization of the new theorem is supplied.  No optimizer, floating
point computation, SAT result, or unverifiable solver certificate is used.

The note does not establish convergence of \(C_p/p^{1/4}\), the optimal
leading constant, all-order equality cases, a higher-dimensional analogue,
or novelty/priority.


## Finite-band optimality audit

Section 7 was checked separately from the explicit witness calculation.  The
second derivative at the coordinate axes gives the necessary limit constraint
\(\gamma_1^2+\sqrt2\gamma_2\le1\).  The norm and both Gram-entry asymptotics
were recomputed term by term under fixed boundary width.  The remaining
profile problem reduces to three nonnegative quantities and an exact
one-variable factorization.  The checker now verifies the two polynomial
factorizations, both negative discriminants, and the positive H² coefficient
in Q(sqrt(2)).

This result is intentionally restricted to fixed-width palindromic boundary
profiles with axis local maximality.  It does not exclude a better lower
constant from growing-width, non-palindromic, or non-axis constructions.
