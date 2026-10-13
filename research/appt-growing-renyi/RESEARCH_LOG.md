# Moving-order APPT research log

14 October 2026, Asia/Shanghai. Current research starts from main
`9c10f10411ceb2886968ae8e741a79d8a53f0da6`. This local note reports actual
mathematical work, not external review or a new Lean audit.

1. Rechecked the primary AKW/Tran entropy scope before choosing the fixed-order
   limit-interchange gap. General finite-order APPT value theorems and their
   existing source/audit boundaries were inherited explicitly.
2. Derived a gap between the actual first and second normalized eigenvalues,
   using the physical four-unit star. Combined the global eight-unit paired-gap
   estimate with a bounded exceptional spectrum and O(1/m) middle interval.
3. Proved the unrestricted high-order upper bounds and an adaptive finite
   projection-plus-spike lower family. The correct completed square has cross
   term −cAT. A preliminary derivation missing its factor two was corrected
   before any proof was committed or published; a real 25×25 negative-PPT
   control now prevents reuse of the wrong coefficient.
4. Proved the bounded-aspect entropy criterion h/(1+χ_+)→0 and distinguished
   it from the stronger moment-excess h→0. Explicit actual APPT families show
   why purity optimality and the stronger peak tolerance are not necessary
   in all growing-order entropy regimes.
5. Derived the zero-order width restriction from the actual shifted star.
   Retained exact pivot centering after multiplying the kernel by α. Proved
   the uniform state identity, convex least-value endpoint optimization and
   the adaptive actual negative-family lower bound, including all finite-window
   near-minimizers and the alternating critical branches.
6. Connected endpoints to the inherited fixed-order values by finite-grid
   monotonicity on compact positive order intervals. This closes the uniform
   all-positive-order bounded-aspect profile and all-aspect sublinear-order
   profile without importing a nonexistent uniform fixed-order error.
7. Proved actual-state compact-order kernel continuity. Collected the complete
   limiting-order spectral criteria, including the previously unstated
   1/2<α<1 flatness implication and the distinction at moving transition orders.
8. Standard-library exact physical controls, rational identities and diagnostic
   evaluations passed ordinary/-O Windows and matching WSL runs. Full analytic
   statements are proved in the notes, not extrapolated from those cases.
9. Preserved the complete draft in local commit `5f9ba3fe4`; later clarification
   makes the common large-m thresholds explicit. Independent assistant review
   is requested at the breadth agent's current-route boundary. The package is
   not pushed or counted as an external peer-reviewed result at this stage.

No original Gaussian worktree file was edited. No new Lean module/root, solver
trust assumption, Release, DOI or aiXiv submission was introduced. The old
importance-rated broad research objective is not certified complete by this
APPT continuation or by a failed conjecture search.


## Completed proof and integration checkpoint

The subsequent ordinary proof chain closes the exact finite small-order
band, linear-order peak/bulk coupling, and finally every positive order for
arbitrary aspect as m grows. The last proof preserves finite protection
coefficients and the exact u_D endpoint. Its comparable-peak range forces D
exponentially large in alpha; its other range permits alpha much larger than
D without a trace expansion. Vanishing sublinear moment excess is proved
separately before taking logarithms.

The independent assistant's initial, linear and all-order full-read records
are now committed, with no unresolved mathematical changes. The previous
draft-status sentence above records that earlier checkpoint. The result
catalogues are updated only after these reviews. Parallel main 830a7f6c4,
including its separately completed sharp-purity formalization, was merged
without cherry-picking or altering its work. Its source-bound kernel receipt
is inherited, not a new audit of these entropy papers.

Read-only final checks again matched all 235 tree inputs to the original
source archive/receipt, all 91 APPTSubunit bound inputs, and all 27 preserved
Gaussian dirty files. No Lean build or root expansion was invoked.
