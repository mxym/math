# Bell–Skandera: an ended weak scalar-arithmetic stage

This is a modest ended-stage research record, not a conjecture resolution. The Bell–Skandera main question remains unresolved by this work. The candidate is not real-rooted and is not a counterexample to that question. No priority claim is made.

The auxiliary observation has a limited scope: positive integral coefficients and constant term one, strict Newton inequalities, irreducibility, positive discriminant, positive algebraic norm, and the uniform weak bounds
`Tr((a lambda+b)^2) >= 7` for every nonzero integer pair `(a,b)` do not imply the Kruskal–Katona inequalities. These particular trace bounds use only `|Norm(a lambda+b)| >= 1`; they discard the actual norm magnitude.

Retaining that magnitude already excludes this candidate. At `(a,b)=(1,-3)`, the square trace is 34 and the absolute norm is 355, while
`34^7 = 52,523,350,144 < 103,787,006,575 = 7^7 * 355^2`.
Thus the observation is not an obstruction to the full family of affine norm constraints, to higher-degree resultant constraints, or to arithmetic methods in general.

Run `python3 verify_arithmetic_relaxation.py` using ordinary Python 3. The verifier uses exact integer and rational arithmetic, requires no external packages or downloads, and refuses to run when assertions are disabled. The proof gives the all-integer-pairs argument; finite sampling is not substituted for that quantified claim. The generated JSON includes the stronger actual-norm negative certificate.

The original private delivery was corrected during independent review. `provenance/ORIGINAL_HANDOFF_MANIFEST.json` and `provenance/ORIGINAL_SHA256SUMS` preserve its hashes; `review/REVISIONS.diff` shows the revisions. The original source-audit record is retained, with its dated inspection scope; the publisher has not performed a new literature search. Third-party PDFs and exploratory scans are excluded. See `review/INDEPENDENT_REVIEW.md` and `verification/RUN_RECORD.json` for the completed review and reproduction. This record is published as a small note, without a Release.
