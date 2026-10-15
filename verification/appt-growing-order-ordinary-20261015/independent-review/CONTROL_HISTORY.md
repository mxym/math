# P review, correction and actual-control history

This is an internal AI-agent ordinary mathematical review, not external
human review or formal verification. All run identifiers below are UTC.
No author checker was executed by the reviewer. No author manuscript was
edited by the reviewer, and no Lean/kernel scope was changed.

1. The initial 188-line manuscript c719b61b... and 29-line map 85a416fd...
   were frozen and read. The reviewer found a genuine false literal P2
   range: fixed m, alpha->infinity and alpha/logD->infinity do not force
   D->infinity. For m=n=2, the maximally entangled all-unitary test gives
   lambda_1<=1/2, and the actual normalized I+2|v><v| state attains it.
   Consequently E_alpha tends to log(2), contradicting the original
   unqualified fixed-m corollary's log(3). That original P2 range did not
   receive a mathematical PASS.

2. The author corrected the fixed-m branch to require D=mn->infinity,
   including c=infinity, producing the 190-line manuscript 50d20926...
   and 30-line map 8481ff22.... This is a real corollary-range correction,
   not a status edit or an unchanged original target. At THIS correction,
   P0/P1 were unchanged. The full original source/map/checker remain in
   both the author's before-fixed-dimension-quantifier-fix directory and
   this review's snapshots. REVIEW_HISTORY.md openly records the error.

3. Independent run **20261015T091232.667475Z: PASS**, against the corrected
   v2 statement with its original weaker upper error. It contains 65 exact
   rational decreasing-row graph tests, 1,488 exact all-integer-rank tests
   for uniform-Schmidt witnesses, 96 dimension/order cases and 576 actual
   family/convex-mixture/singular-state comparisons. There are 25 cases
   with alpha>D and 144 m=2 head checks. Six incorrect assertions are
   actually executed, rejected with AssertionError and retained separately.
   These finite tests do not enumerate all Schmidt vectors, global
   unitaries or feasible matrices.

4. The AUTHOR then strengthened the upper cutoff from exp(-sqrt(a)) to
   1/a. The final 192-line source 3d038944... and 31-line map d2976594...
   claim U=2m/(D-m)+(2log(a)+log48+2)/a and uniform absolute rate
   O(D^-1/2+log(alpha)/alpha). This is new stronger mathematical content,
   separately reread in full. The corrected v2 manuscript/map/checker/
   history are retained in before-sharper-upper-rate and this review's
   P-v2 snapshot. The P2 correction remains byte-identical in the v3 tail.

5. Independent run **20261015T091753.210538Z: PASS**, after changing only
   the explicit U formula in the reviewer checker. All 576 actual-state
   comparisons and the same exact/negative controls were actually rerun
   against the stronger bound. The earlier executed checker remains in
   its run. No unexpected mathematical-checker FAIL occurred in either
   independent run. The original source-range error in item 1 is still
   recorded; two successful finite runs do not retroactively certify it.

The six retained rejected variants are: the original fixed-D c=infinity
corollary; omitting exact trace mean normalization; dropping the fixed-m
log(q) branch; using a fractional rank below one when alpha>D; extending
the fixed-m c=0 formula to bounded order; and applying the row graph
inequality without decreasing weights. Each PASS run preserves the actual
exception records, not an unexecuted list of intended tests.

The separate AUTHOR runs 090459.816232Z, 090615.061888Z and 091342.637637Z
report PASS. Their scripts/results and bound source bytes were read/copied/
hash-checked, not reexecuted. The first run's 104 finite family tests did
not detect the original P2 quantifier error; no claim is made that its
PASS covered that false literal corollary. The second adds its countercase;
the third updates the strengthened U. The latest complete 93-line checker
was read and contains no import of earlier packets or their controls.

A separate initial CAPTURE helper assumed that exactly one tracked file
was named SHARP_ASYMPTOTIC.md; its assertion failed because a research copy
and a byte-identical preprint copy both exist. The helper source and actual
trace excerpt are retained in history/. The corrected helper names the
research path explicitly and snapshots both. This setup failure is not
counted as a mathematical-checker failure and was not hidden by deleting
its source.

All independent scalar and rational checking code was newly written by
the reviewer, without importing or AST-selecting author functions. Decimal
diagnostics use 240-digit Mpmath. They are evidence of finite arithmetic,
not interval certificates, exhaustive quantum optimizations, formal proof,
or substitutes for the uniform mathematical read in REVIEW.md.
