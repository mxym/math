# Core proof progress: prices, upper normals, and regularization

Status: unconditional partial formalization. This is NOT a proof of the sharp
four-cell inequality or of its equality classification.

## Newly checked mathematical statements

Let q be the actual standard Gaussian upper quantile of mass 1/4. For every
ambient dimension d and four actual strict Gaussian winning cells of mass 1/4,
`balanced_four_price_difference_bound` proves

    abs(b_i-b_j) <= q * norm(v_i-v_j).

No score-injectivity hypothesis is needed: positive cell masses imply it.
The proof pushes a normalized score difference through the actual Gaussian
linear-functional law and compares the actual cell measure with its winning
halfspace. Strict monotonicity of the actual Gaussian tail gives the bound.

If sum(b_i)=0 and every score-pair distance is at most D>=0, then
`centered_balanced_four_price_norm_bound` proves norm(b)<=q*D, where this
finite function-space norm is the maximum coordinate norm. For sequences of
such diagrams, `centered_balanced_four_prices_tendsto_subseq` constructs a
strictly increasing subsequence with convergent, still centered, prices.
These statements allow singular score configurations; they do not assert
convergence of Gaussian facet surface integrals.

For every finite real matrix size, define an upper normal by

    trace(A*(Y-Q)) <= 0 for every PSD Y with trace(Y)=1.

For PSD Q with trace(Q)=1 and symmetric A,
`upperNormal_iff_exists_multiplier` proves that this is equivalent to

    mu*I-A is PSD, and A*Q=mu*Q.

The multiplier is necessarily trace(A*Q). Testing normalized rank-one matrices
proves the quadratic-form inequality. Factoring arbitrary positive matrices
then proves that a zero trace pairing forces the entire product to vanish.
This includes off-diagonal complementary slackness, not just diagonal checks.

For arbitrary real PSD 3-by-3 matrices Q,L, an upper-normal relation, and an
arbitrary rectangular Gram factor M satisfying

    M*M^T = (1-epsilon)*Q + (epsilon/3)*I,

`upperNormal_regularized_residual_bound` proves, with mu=trace(L*Q),

    trace((L*M-mu*M)*(L*M-mu*M)^T) <= epsilon*mu^2.

Its preceding theorem proves the exact identity with
(epsilon/3)*trace((L-mu*I)^2). The estimate uses two PSD trace-pairing
inequalities, not numerical eigenvalues or a finite matrix grid. Every matrix
entry and every nonnegative epsilon is universally quantified.

## Dependency graph

    actual Gaussian measure + winning sets + one-cell Gaussian tail law
      + exact quarter-quantile profile
        -> PriceBounds
          -> PriceCompactness

    Mathlib positive matrices + proved C*-algebra factorization
      -> TraceSupport
        -> NormalCone
          -> RegularizedResidual

Both branches are imported by GaussianFour. MODULES.json fixes the full
compilation order; ROOTS.txt and audit/ list the exact audited declarations.

## Exact relationship to the global proof

PriceBounds closes manuscript equation (10); PriceCompactness supplies the
normalized-price subsequence needed for the boundary argument. NormalCone
closes the abstract positive-trace-one operator optimization step behind
(20). RegularizedResidual proves the matrix identity and estimate in (21)
in intrinsic three-dimensional coordinates.

The three-dimensional matrix slice has NOT been silently identified with the
actual four-score Gaussian covariance slice. The remaining analytic work must
construct that covariance value, prove its differential formula, transport
between the centered four-dimensional presentation and intrinsic coordinates,
and identify the gradient with actual Gaussian facet integrals. These results
alone do not give a Gaussian critical point, the mountain-pass deformation,
rank-two exclusion, or a sharp upper bound for arbitrary partitions.

The geometric Gaussian perimeter inputs and the tetrahedral arctangent
calculation remain unproved in this import closure. No axiom or conditional
main-theorem wrapper has been added. See GAPS.md for the full list.

## Provenance and rights

The baseline quartile/collinear development is commit addcab8a; this work
preserves its sources and prior verification evidence. New material is by
Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology; mxymmxym1@gmail.com;
ORCID 0009-0000-3864-3536. No external funding; AI-assisted research.
Existing licenses and third-party attribution remain in force. No external
human peer review or priority claim is made.

New original material retains all rights not otherwise granted; existing
repository licenses and third-party permissions are preserved.
