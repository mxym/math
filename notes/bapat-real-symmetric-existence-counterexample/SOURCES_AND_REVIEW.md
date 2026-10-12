# Sources and review scope

Date: 2026-10-08 (UTC).

## Input and attribution

The mathematical input before typesetting was the preparatory `PROOF_DRAFT.md`, SHA256 `fad4399c4586e718cedfc43a3d08248274c219d590a08742e511c4b8877ffed0`. This version already incorporates the precision changes requested by two independent reviews and the positive-denominator integer scaling corollary. The preparatory draft is not included in the release payload; the final self-contained proof is supplied as TeX, PDF, and complete Markdown. The review reports and final-copy report identify the applicable reviewed versions.

The typeset note adds no author's name, private identity, or affiliation. Authorship is for the owner to specify. AI-assisted drafting, checking, and exact finite computation are expressly disclosed in the manuscript. The term “independent review” denotes separate model-conducted mathematical examinations, not external journal review or Lean verification.

## Primary and versioned references

1. Lon Mitchell, “A note on Bapat's q-permanent conjecture,” Operators and Matrices 14(4) (2020), 915–919. DOI: https://doi.org/10.7153/oam-2020-14-56 . Publisher PDF: https://files.ele-math.com/articles/oam-14-56.pdf . The publisher PDF was opened and checked during preparation. Page 915 states the inversion-weighted Hermitian positive-definite formulation; the paper discusses the PSD extension and special cases. The PDF is linked, not copied into this package.
2. The already published complex counterpart, repository `mxym/math`, directory `notes/bapat-q-permanent-counterexample`, commit `c5d7f68e78b6c80912041c6cf1fd4d3cd950beb6`: https://github.com/mxym/math/tree/c5d7f68e78b6c80912041c6cf1fd4d3cd950beb6/notes/bapat-q-permanent-counterexample . The preparation workflow supplied this fixed published version. Its local remote-readback README was inspected and confirms that the order-200 matrix and its PD perturbation are complex Hermitian, with a separate asymptotic complex argument. A fresh public web fetch of the GitHub directory failed with a cache miss; no new online availability check is claimed here. The real proof is logically independent of that numerical complex witness.

The manuscript proves the elementary identities and limiting lemmas it needs. The remaining tools are standard measure-theoretic facts: the strong law for bounded independent samples, weak convergence against bounded continuous functions and its almost-everywhere continuous mapping form, compactness, Haar invariance, and monotone/Tonelli integration. No unverifiable specialized theorem is cited as a substitute for a proof step. No claim of global historical priority is made.

## Independent underlying reviews

- `review/INDEPENDENT_AUDIT.md`, unmodified report SHA256 `f3af25dc713625f0d70d14ec2808b4675d4c7102f5fbce17f7e3eb9eb3af5615`, records a PASS as a finite-existence proof. Its audited draft hash was `53ff4b0a29fc1e93553384bd30cb2ec184b4f12ca4a2b1a022cc13c92183a1ab`.
- `review/SECOND_REFEREE.md`, unmodified report SHA256 `cdcf08e960b8f0b505093b69459d9673fc7d839f1ee86f37d6d52ef30e823b0f`, records an independent adversarial PASS as a nonconstructive finite-existence theorem. Its audited draft hash was `78a5f7e5252c5ffac09a75d9254060275e9e8a94924e40382492468e71088357`.

Those reports audited predecessor snapshots, not the later PDF bytes. They include bounded literature checks; those checks are not exhaustive priority certificates. Their mathematical scripts and original logs are in `verification/`; fresh reproduction logs are separately named `*.rerun.log`. A fail-closed `__debug__` guard was added to both scripts without changing their mathematical bodies. Stripping exactly that guard reproduces the supplied original sources byte for byte, and fresh normal-mode outputs match both original logs byte for byte. The supplementary scaling and document checkers have the same guard. The independent guard-test driver uses no assertions and verifies 16 negative cases under `-O`, `-OO`, `PYTHONOPTIMIZE=1`, and `PYTHONOPTIMIZE=2`: all return code 2 with an explicit diagnostic and no success output.

## Final-copy expansions requiring explicit review

The typeset version makes these standard details explicit rather than relying on compressed references in the draft:

- Marked-inversion enumeration and two-row permanent expansion derive the endpoint identity directly from the actual inversion-number q-permanent.
- Matching monomial occurrences explains the Fischer product/cross-Gram identity.
- A countable dense family of continuous functions and the strong law establish existence of one deterministic equidistributed real sphere sequence.
- Coordinate phases and the simplex/Dirichlet monomial moment explain the projective normalization, including the CP3 factors (N+3)(N+2).
- The real Jacobian |d|^2 for (z,d) -> (zd,d) supplies the correctly normalized complex Cauchy density.
- Equation (26) explicitly proves integer denominator scaling, P_q(DB)=D^N P_q(B), and the corresponding derivative identity. A new exact script checks this algebra on finite examples.

No new generic-position condition, nondegenerate-Hessian assumption, moment-convergence claim, dimension bound, or numerical real witness is inserted. Arbitrary real row lengths, the open domain F != 0 of g, the moving-point continuous log truncation, the exact exterior-square transformation, conjugate peak equality, and the order of all finite choices are retained. The integer statement is a positive scalar-multiplication corollary, not a computed witness.

## Final-copy disposition

`review/FINAL_COPY_REVIEW.md` records PASS for the complete final mathematical source, its added short proofs, all retained analytic conditions, the finite choice order, and equation (26)'s integer conclusion. No mathematical source edit was requested. The reviewed frozen reading files are:

- `paper.tex`: SHA256 `ac6983f69f78175ce119b253f22ae11336ba1e23af9e4c8b13b51d9b30e86411`
- `paper.pdf`: SHA256 `fcdf05b20799ec290db09a437fdce2b4d94fce636928a62caf14b318af7cdbdd`
- `proof.md`: SHA256 `20834610bc357b08ac69075d3102fc9e31df7bbebd2f6809114327a9ac4e2fa7`

Later mathematical edits require renewed review. Package metadata and checksum refreshes do not alter the frozen mathematical copy. The report also records the independent final-copy reruns; its safety addendum covers the fail-closed Python guards and their negative tests.


## Portable release packaging

After the final mathematical review, the build wrapper was changed to use ordinary `pdflatex` by default and an explicitly supplied optional `LOCAL_TEX_DIR` for a pre-existing custom format/font-map directory. A temporary-stub test checks default/custom command selection and rejection of a missing custom format without rerendering or changing the frozen PDF. The distributed `build-pass2.log` is explicitly labeled as a publication projection: only the preparation environment's absolute custom TeX directory has been replaced by `<LOCAL_TEX_DIR>`. The underlying raw log is retained locally, outside the release. No mathematical source, PDF, Markdown proof, or final-copy report changed in this packaging step.
