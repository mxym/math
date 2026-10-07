# Cross-audit and extensions, 2026-10-07

This research pass read the current catalogue and substantive parts of manuscripts 001--005, including work produced by parallel tasks. Existing versioned manuscripts were preserved. It did not certify the entire OpenAI collection or every line of the parallel manuscripts.

## Substantive outputs

- 006: modulus-robust nonlinear avoidance, all nonflat smooth germs, and a C1/flat-smooth differentiability boundary. The finite routing proof is reproduced, not merely invoked via the affine main theorem. Core progress was disclosed in commit 61eb89311e19eb6539b97acb46207197b0508d64; full source in 478be8879564e99843ad0bc69ca6192379e5b59e.
- 007: an independent tail-sensitive convex-gradient interpolation theorem for BV-slice densities, with a sharp finite-moment exponent. Its transport corollary removes the bounded-target restriction under the potential-stability input from 001, requiring any p>2. Full source in 72eb17dfd6448f879192b6763b9b5c99b4c072f7.

## Scope of cross-review

001: inspected the conditional-cell exponential inequality, barycenter normalization, moving-site cancellation and total-variance estimate, P2 completion, bounded-gradient interpolation and Gaussian sharpness construction. This supplied the hypothesis to be combined with the independent new interpolation theorem. No assertion of a complete external audit of all finite-cell regularity or compact-companion details is made.

002: inspected the abstract five-hypothesis planar sieve interface and quadratic-order scope. Extending to general number fields would require a genuinely new geometric/entropy interface: the two-kernel intersection and norm-degree bounds are specific to the planar quadratic setup. No higher-degree result is claimed, and the entire entropy telescope was not reverified in this pass.

003: inspected the refined cover estimate, superlacunary scale schedule and transfer strategy. The Assouad-dimension-two estimate does not by itself lower the nonembedding threshold below two. The inherited derivative/crossing obstruction was not fully reaudited; no smaller-dimensional obstruction is claimed.

004: strengthened the absolute-location quantifier in template placement and checked the finite-output dependency needed for nonlinear perturbations. A qualitative affine blocker alone would not justify the extension.

005: the simplex-product optimization is already closed in its stated class. No claim of an unrestricted projection-body maximizer is added.

## Verification and publication standard

Both new manuscripts were compiled twice locally and every rendered page was visually inspected. Their source blobs match the uploaded files. Nine exact robust-cover regression cases and 6000 exact piecewise-affine interpolation checks passed locally, including Python -O runs. The repository workflow independently replays these finite checks and builds the PDFs. The checks do not formalize the analytic arguments, and the 006 toy is not an arbitrarily-small-density witness.

The sources, explicit dependencies, limitations and reproduction scripts are public. Neither journal suitability at the top-four level, mathematical priority, nor independent peer review has been certified. Upstream OpenAI Apache-2.0 notices remain applicable; no additional license for new material is selected by this record.
