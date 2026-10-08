# Complete exact three-subset spectrum for every degree

[Full rigorous research note](paper.md) proves the exact optimal marginal-preserving single-atom total-variation coefficient for the natural action of \(S_n\) on three-element subsets **for every integer \(n\ge3\)**.

**No finite combinatorial maximization remains in the final answer:**

- For \(n\ge48\), the optimum is given by one of **four explicit rational functions** of \(m=\lfloor n/4\rfloor\), selected by \(n\bmod4\). See Theorem 1 of paper.md.
- The 45 exceptional degrees \(3\le n<48\) are completely classified by an exact rational table and pre-existing fixed primal-dual certificates. In fact, the new branch formulas are already certified for \(r=0,2\) at \(m\ge6\).
- Every formula is *sharp*: matching nonnegative central probability measures with **exactly uniform triple-image marginals** attain it at arbitrarily small positive TV perturbations.
- The new sharpened expansion is
  \[
  C_n^{(3)}=1-\frac{18}{n}+\frac{288}{n^2}
   -\frac{\gamma_{n\bmod4}}{n^3}+O(n^{-4}),
  \qquad
  (\gamma_0,\gamma_1,\gamma_2,\gamma_3)=(3840,4000,3840,3968).
  \]
  Thus arithmetic periodicity first appears at the third correction order.

## Complete exact proof evidence

The infinite part is **not inferred from finite \(n\) data**. The proof specifies five conjugacy-class contacts in each residue class, then uses exact \(5\times5\) rational primal and dual linear systems. The universal dual inequality is reduced analytically to **40, 42, 41, 43 explicit rational-polynomial inequalities** in residues 0,1,2,3. Every such inequality has a frozen coefficientwise nonnegative rational-polynomial certificate after the shift \(q=m-m_0\ge0\), with \(m_0=6\) or 12.

- [Frozen all-parameter polynomial sign certificates](../certificates/three_subset_eventual_4branch_signs.json): all four branches, exact contact matrices, weights, dual values, and numerator/denominator coefficient arrays.
- [Independent standalone symbolic checker](../code/check_rank3_eventual_formula.py): uses only SymPy exact rational algebra, **reconstructs** both systems, every dual sign inequality, every contact, and checks all coefficients against frozen JSON. No numerical optimization or finite-\(n\) enumeration is used as a proof premise.
- [Independent standard-library integer/Fraction checker](../code/check_rank3_eventual_integer_replay.py): no SymPy or solver; replays every realizable short-cycle type at 23 selected degrees as large as 204, totaling **1,803,943 exact inequalities**, and crosschecks all 73 previously certified coefficients for 48–120.
- [Earlier finite rational certificates for 6–23](../certificates/three_subset_n6_23.json) and [24–120](../certificates/three_subset_n24_120.json), replayable with their existing optimizer-free checkers.
- [General all-rank orbital and exact maximum-minor theory](../universal-exact/README.md) for background.

## Reproduction

Run from the repository root. SymPy 1.14.0 is required for the symbolic identity and coefficient checker; standard Python 3 is sufficient for the independent integer check.

    python notes/sharp-robust-permanent/code/check_rank3_eventual_formula.py
    python notes/sharp-robust-permanent/code/check_rank3_eventual_integer_replay.py

The symbolic script verifies against the **existing frozen certificate** by default; using the optional --emit flag regenerates the certificate from exact formulas, rather than merely trusting fixed arrays. GitHub Actions also replays the published files.

## Mathematical scope

This settles the **complete exact finite-\(n\) rank-three problem**, including its infinite stable arithmetic branches. It strictly strengthens the previous exact table through \(n=120\), the earlier sharp \(1-18/n+O(n^{-2})\) asymptotics, and the general finite-maximal-minor formula when specialized to \(k=3\).

For arbitrary growing \(k\), the stronger problem of finding comparably short branch formulas remains open; the general exact maximal-minor formula is still available for every finite \((n,k)\).

This is an AI-assisted research result with complete mathematical argument and exact machine-replayable algebraic certificates. It is **not yet externally peer-reviewed, formally verified in Lean, or certified as a worldwide first discovery**.
