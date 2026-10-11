# Review of the uniform APPT purity upper half

The result is an all-state necessary bound, not a lower construction or a theorem assuming a particular extremizing spectrum. Dimensions are arbitrary integers 2<=m<=n for the spectral-pivot bound and 8<=m<=n for the explicit dimension-only estimate. The small-dimension threshold is technical, not a restriction on the limiting theorem.

## Dependency chain checked

1. The physical arbitrary-edge witness places the actual sorted eigenvalues by constructed global-unitary permutations. Its diagonal is bounded by the exact paper pivot b=lambda_(D-m(m+1)/2+1).
2. The minimum paired gap w is nonnegative and below every off-diagonal edge entry. Subtracting w times the complete adjacency matrix gives a nonnegative Hermitian residual graph with the required row order. Restoring the baseline gives the original PSD cap, not a different graph.
3. The all-ones test proves (m-1)w<=2b. The refined degree-square identity retains its full cross term before the nonpositive remainder is discarded. Residual edge sums are transported by the actual rowRank bijection.
4. Sorted centered variance and the generic spectral moment identity connect the graph inequality to the original trace(A*A).re. The result is V<=C b^2, C=max(8,4+D/(m-1)^2).
5. The first j eigenvalues, with j=D-m(m+1)/2+1, give j(b-1/D)^2<=V when b>=1/D. If C<j, exact real square-root normalization yields D^2 V<=C/(1-sqrt(C/j))^2. The strictness condition is essential because Lean division and square root are total functions.
6. The proof establishes D<=3j and C(m-1)^2<=27j for sufficiently large m. Hence sqrt(C/j)<=6/(m-1), yielding the explicit factor [m/(m-7)]^2. No numerical approximation to sqrt(27) is required.
7. The factor is at most 1+epsilon once m>=max(8,7+63/epsilon). An Archimedean choice yields one natural threshold independent of the larger dimension and the state. Thus n and the state may vary arbitrarily with m.

## Errors rejected during development

A Lean summation-scope mistake initially subtracted w outside a sum instead of inside every summand. Parenthesized summands repaired the identity; a three-element regression proves the expressions differ. A rational projection-family check rules out dropping the aspect-ratio term. Another exact regression rejects applying normalization at C=j, where a denominator becomes zero. No failed proof or timeout was counted as verification.

## Scope not inferred

The theorem proves the upper half directly for every density matrix; it does not define and evaluate a supremum, prove attainment of a matching lower limit, establish the compactness/forest lemma, or certify every research claim indexed alongside it. The all-dimensional equivalent also needs a separate fixed-m argument. Counterexample membership with an additional spike, finite rectangular optimality and equality, entropy extrema and rigidity remain unverified in their entirety.

The new source and audit runner preserve the pinned Lean/Mathlib versions and original quantum definitions. Local build and trust-zero replay passed; independent CI evidence is recorded separately by tested commit. No publication tree or immutable release is modified.
