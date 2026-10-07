# Proof audit

Date: 7 October 2026.

## Statement audited

For the sharp binary constants \(C_p\) defined by

\[
\operatorname{dist}_F(T,\mathcal D_{2,p})\le C_p\sqrt{R_p(T)},
\]

the finite reflected boundary-profile construction in paper.md satisfies

\[
\liminf_{p\to\infty}\frac{C_p^2}{\sqrt p}
\ge
\frac{2S-\mathcal M(a)}{4\sqrt{SM_1}},
\]

and the explicit three-term profile proves

\[
\liminf_{p\to\infty}\frac{C_p}{p^{1/4}}>0.623586.
\]

## Analytic dependency audit

1. The exact identity \(R_p(T)^2=\det G(T)\) and the exact projection
   formula for distance are imported from the parent
   sharp-binary-tensor-rigidity note already present in this repository.
2. Reflection \(t_k=t_{p-k}\) cancels \(G_{12}\) pairwise. Direct index
   substitution gives the displayed exact formula for \(G_{22}\).
3. The \(G_{11}\) limit uses only fixed finite support. Each diagonal term
   has its stated binomial ratio; cross terms are \(O(p^{-1})\) and
   shifted-square terms are \(O(p^{-2})\).
4. Projection energy is reduced to an interval of length \(\pi/2\) using
   basis periodicity, not a parity-dependent tensor symmetry.
5. On the \(p^{-1/2}\) angular scale, the binomial/trigonometric factors
   converge uniformly on compact \(x\)-intervals to the Gaussian/Fock
   profile.
6. Maximizers cannot escape to \(|x|=\infty\): the surviving boundary
   terms are bounded by a fixed polynomial in \(|x|\) times
   \(e^{-x^2/4}\), while the opposite boundary is exponentially small in
   \(p\).
7. Squaring the defining rigidity inequality gives the final passage from
   the tensor quotient to the lower bound for \(C_p^2/\sqrt p\).

No numerical optimization enters these seven proof steps.

## Explicit certificate audit

The primary checker uses exact rational arithmetic to verify:

- the unique positive critical point is bracketed by
  \(1473/5000<y_*<29461/100000\);
- the degree-ten alternating Taylor sum is an upper bound for
  \(e^{-1473/5000}\);
- the resulting rational upper bound for the profile maximum gives
  the strict constant \(0.623586\);
- the new rational constant strictly exceeds the previous
  \(2^{-3/4}\) lower constant by the exact fourth-power comparison.

A second implementation does not import the primary checker. It instead
uses the reciprocal of a positive Taylor lower bound for \(e^L\) to
majorize \(e^{-L}\). It reaches the same target constant. Both implementations
pass under ordinary and optimized Python.

The frozen outputs are in results/.

## Concurrent two-band comparison

Before publication the shared main branch added
notes/binary-tensor-two-band-lower-bound, with asymptotic constant
\[
\kappa=\sqrt{2/7+\sqrt2/14}=0.6218758237\ldots .
\]
Its supplied exact verifier was rerun successfully, including
\(\mathbb Q(\sqrt2)\) formulas, orders 10 through 120, universal integer
gates and negative controls. The present primary and secondary checkers also
verify by rational squaring that
\[
 0.623586>\kappa.
\]
The present theorem is therefore not indexed as a duplicate of that note:
it provides a general finite-profile limit theorem and a stronger asymptotic
constant. The two-band note still has a distinct exact finite-\(p\) witness
statement.

The concurrent note was then strengthened by an axis-local
mechanism-optimality theorem. Its necessary condition is
\(\gamma_1^2+\sqrt2\gamma_2\le1\). For the present rational profile the
left side is exactly
\[
 B=12346629/9765625>1,
\]
already checked by both the profile algebra and the critical-point
certificate. Hence the two theorems have disjoint mechanism hypotheses at
the improved witness: the new constant comes from an off-axis projection
maximum. No conclusion of the concurrent optimality theorem is used as an
input to Theorem A.

## Diagnostic finite-order check

A non-proof floating diagnostic reconstructed the full tensors and directly
optimized their projection energy for \(p=30,60,120,240\). It observed
\(G_{12}=0\) and convergence of both \(\sqrt p R_p\) and the projection
maximum to the formulas in the paper. These diagnostics were used only to
catch indexing/sign mistakes; they are not part of the proof certificate.

## Remaining verification boundary

The asymptotic compactness argument and the imported parent identities are
written proofs, not Lean-formalized in this supplement. The exact checkers
certify only the displayed rational corollary once the analytic profile
theorem is established. No external human peer review has been performed.
