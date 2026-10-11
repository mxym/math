# Fixed-local purity: physical optimization and all-regime upper verification

This continuation verifies previously claimed research results; it does not prepare a preprint or Release. New proof source is separated from independent build and kernel evidence. The complete high-dimensional research program remains partially formalized.

## Exact statements

Let D=mn and C_m=m^2/(m^2-1). `apptPurityValues m n` is the set of actual trace(A*A).re values of complex density matrices on C^m tensor C^n that are PPT after every global unitary conjugation. `apptPuritySup m n` is its real supremum. The source proves this set nonempty and bounded for 2<=m<=n; no empty-set or unbounded-set convention supplies the result.

For m>=2 and n>=2m, the new finite sandwich is

    C_m-1/n^2 <= D*apptPuritySup(m,n) <= C_m+13m/n.

The lower bound is attained as an inequality by an actual projection-family density matrix; the upper bound quantifies over every APPT density matrix. Scaling the supremum is proved rather than assumed. Consequently, for every fixed m>=2,

    Tendsto (fun n => (mn)*apptPuritySup(m,n)) atTop (nhds C_m).

This is a genuine filter-limit theorem for the physical objective, not a substitution into the earlier growing-m theorem. It makes no claim that a finite-dimensional `IsGreatest` or all maximizing spectra have been formalized.

Combining the fixed-local upper bound with the previous growing-m upper theorem gives

    for every epsilon>0 there is N such that for all 2<=m<=n with mn>=N
    and all APPT density matrices A,
    D^2*(purity(A)-1/D) <= (1+epsilon)*max(8,4+D/(m^2-1)).

The one threshold is uniform in both dimensions and the state. This is the upper half only. Its growing-m lower counterpart still depends on unformalized graph limits and simultaneous constructions.

## Mathematical dependency review

1. The all-ones test of the actual arbitrarily permuted eigenvalue witness gives the linear paired-gap budget. Using the last top eigenvalue and the paper's lower pivot b gives (m-1)*lambda_R <= (m+1)*b, R=m(m-1)/2. The final physical theorem constructs and discharges the dimension and placement obligations.
2. Every eigenvalue between the top index R-1 and pivot index D-R-m (zero-based) lies in [b,((m+1)/(m-1))*b]. There are D-m^2+2 such indices. Every omitted eigenvalue is nonnegative and at most 3/D by the checked physical rank-two bound.
3. For an interval [b,r*b], x^2<=(r+1)*b*x-r*b^2. Summing, bounding bulk mass by one, and completing a square gives the bulk second moment at most (r+1)^2/(4*r*L), L its cardinality. Exceptional indices contribute at most 9*(D-L)/D^2. For n>=2m, L>=D/2 and D-L<=m^2. Exact algebra yields D*purity<=C_m+13m/n.
4. The existing physical projection construction is used at k=ceil((m-1)*n/2). With s=2k-(m-1)*n, the code proves 0<=s<=1 and the exact identity

       C_m-D*purity(rho_k) = C_m*s^2/[D(m-1)+2k]^2.

   The denominator is positive. Its lower bound gives an error at most 1/n^2. No real-valued rank or unproved spectral state is substituted for the actual integer-rank projection.
5. Nonemptiness and boundedness justify every conditional supremum operation. Positive scaling is proved for these sets. The two errors tend to zero with a common explicit epsilon threshold, yielding the fixed-m `Tendsto` theorem.
6. For the all-regime upper theorem, split at the previous growing-m threshold M. In the bounded-m part, the finite estimate gives D^2*(purity-1/D)<=D/(m^2-1)+13m^2. A total-dimension threshold exceeding max(2L^2,13L^4/epsilon), with L=max(M,2), absorbs this error uniformly. In the growing-m part, n/m<=D/(m^2-1) converts the earlier coefficient to the required one.

## Regression and verification boundaries

The new kernel roots include a genuine 2x4 APPT state with scaled purity 4/3, rejecting both one and the incorrect coefficient 1+1/2^2. A genuine 4x5 APPT state has the exact positive rounding gap 1/5415, rejecting equality with the continuous-rank optimum in that finite example. The real interval coefficient is also checked explicitly.

Development used isolated compiler diagnostics while the authorized Windows builder was offline. Diagnostic receipts state compiler errors literally and are not mathematical certification. They use fresh request directories and pinned base imports. Final certification uses the unchanged independent proof workflow, original module paths, the actual source hash inventory, full Lake construction and empty-kernel replay. A green diagnostic transport job is never used as a proof certificate.

Remaining tasks include joint projection-plus-spike sufficiency for the three-level counterexample; exact rectangular optimality and equality classification; multiscale/two-ended graph compactness and matching growing-m families; full sharp extrema in all regimes; and entropy and rigidity laws. None is inferred from the new fixed-m theorem or upper inequality.
