# Independent complete ordinary review of Q0-Q3

**PASS.** The full proposed mathematical proof and whole-target map were independently
read and checked. No mathematical gap or required mathematical correction was found.
This is an independent AI subagent ordinary review, not external human peer review,
Lean verification, or a new audit of the inherited formal declarations.

The reviewed theorem is the exact minimal EVENTUAL purity onset

    N_2(m)=ceil((m^2+5m+7)/4)

for every sufficiently large integer m, over the original complex density matrices
remaining PPT after EVERY global unitary. The review covers all larger n, every
optimizing projection matrix, its unique integer rank and parity-dependent purity,
and a genuine APPT integer-rank state beating the bulk at n=N_2(m)-1.
It does not provide an effective starting m or assert the formula for all small m.

## Actual source coverage and final-change binding

The initial `PAPER.md` was read in full, lines 1-361, SHA-256
`ad4059967adde63692ff5507a72caa3777fd97e29779aa128c4ef43da594085d`.
The initial `THEOREM_MAP.md` was read in full, lines 1-37, SHA-256
`2324fadc329231142c6ddf7539ba27961aa4eb4abcbb49b4cd068ca37d007a5f`.
Together these are 398 mathematical source/map lines.

The support README 1-36, literature note 1-41, and author script 1-207 were
also read completely: 284 support lines. The entire 2,429-line author JSON was
parsed and every result row structurally checked; sequential reading of all its
raw lines is NOT claimed. The author script was not imported or rerun.

The immutable cited ordinary C0-C4 paper 1-461 and E0-E4 paper 1-377 were
read completely to verify their correct invocation: 838 dependency lines.
Their credited earlier mathematical inputs remain credited; no earlier Lean
certificate or original broader audit has been rerun or expanded.

Only final review-status text changed. Actual final changed lines were read:
PAPER 3,360,361; map 3,37; README 3,15,16. Exact reverse replacements reconstruct
the already fully read initial bytes and original hashes for all three files.
There are ZERO mathematical changes, and no second complete final-text reading
is claimed. The final hashes are:

- PAPER: `41edf08c0ed2d8cd9d6e15f9eeeba0c4814cab2c9a0e81565af7eab39b090d6e`.
- Map: `23ff66d7abdce792e3575d6f0d624a79cb9f98392a7e689d82fdf803015db1e0`.
- README: `541f85f47fe609b03a395d6c88090770f2fde2aa38ad581a270da3d503868961`.

Snapshots, literal status differences, exact reverse checks, supporting hashes,
and per-source line scopes are recorded in `REVIEW.json`.

## Mathematical checks on the complete physical domain

The exact clipped chord yields the signed purity comparison with both the
kappa*T term and finite quadratic budget correction retained. Continuous rank
is used as a comparison bound, with actual integer states handled separately.

For EVERY potentially profitable actual spectrum, E0 coercivity bounds the
budget c. The relative O(c/m) estimate excludes even arbitrarily tiny nonzero
budgets near the empty profile. C0 then squeezes its correction to zero, and
C4's full l1/c compactness localizes the ENTIRE actual list to the nonempty
critical branch. Sequential contradiction makes this uniform throughout the
whole relevant dimension band; no finite-head ansatz enters this step.

Every original anomaly is filled into an actual Schmidt-witness slot. The
nonnegative resolvent walk bound keeps every walk from the main edge and the
first walk from ALL remaining mass, including overlapping slots and a growing
tail. The resulting exact cost implies c-c0>=1.6*tau. Subtracting actual profits
then yields V<=V0-tau/4 with a strict uniform margin and no additive error
independent of tau. Only after this unrestricted argument is the upper scalar.

The exact one-head parametrization solves the finite implicit cost equation.
Its uniform C2 expansion on [1,3] gives the displacement 8/m and constant term
7/4. This compact interval is justified by the prior whole-spectrum localization.
The rational lower displacement 2+8/m has the displayed positive exact remainder.

Integer locking is valid because B_m has fractional part 1/4 or 3/4. That fixed
margin dominates the O(1/m) scalar remainder. The strict upper purity margin
has order m^-8, versus the exact q integer-rounding loss of order m^-11.
The coarse E0 theorem covers every larger n beyond the critical band.
The exact interval equality theorem and scalar integer optimization give every
optimizing matrix and the strictly unique ceiling rank, including half integers.

The lower single-edge witness is genuinely boundary PSD, with aI-P positive
definite and exact rank-one product equal to one. Spectral rearrangement and
edge permutation congruence cover every Schmidt vector and global unitary.
Its actual trace is optimized and then rounded to an INTEGER rank; the exact
loss remains order m^-11 while its gain at N-1 is order m^-8. The endpoint
counts are sufficient eventually. Thus the lower proves minimality for ALL
larger n, rather than just a crossing within the trial family.

The actual m=3,n=8 pole beats the bulk and correctly rejects an indiscriminate
all-small-m extension. Literature disclosures are bounded and partial; this
review provides no independent historical-priority or exhaustive primary-paper
audit. Subsequent W0-W3 research is outside this review.

## Independent finite controls and preserved evidence

`check_independent.py` was written independently and executed once, with every
control passing. It imports or reruns no author verification code. It includes:

- 19 exact symbolic identities, expansions, rank-loss and trace-loss formulas.
- 9 exact Fraction witnesses filling ALL R+K slots and retaining the entire tail.
- 76 exact single-edge boundary PSD matrices, of rank m-1; strict PD fails there.
- 72 exhaustive integer q-rank problems, with strictly unique ceiling winners.
- 22 genuine all-unitary single-head states with actual integer ranks, on both
  sides of the proposed eventual threshold.
- 5 compact scalar maxima checked by exact Sturm root counts and 180-digit
  evaluation, separate from the whole-domain applicability proof.
- 2 rejected false extensions: all-small-m universality and dropping the 7/4
  constant from the onset. The raw evidence is retained.

The raw execution report is `RUN_20261014T085613.824211Z.json`, with SymPy 1.9
and mpmath 1.2.1. There were no failed or invalid independent executions, and
no records were deleted. Author controls were parsed separately: 8 symbolic
groups, 26 lower and 26 same-family upper cases, 26 parity cases, 126 finite
patterns, and 60 tiny-tail cases. The author's m=8 and m=16 positive small-m
family profits remain as data rather than being relabeled as theorem violations.

Finite controls complement the complete ordinary proof. Neither author nor
reviewer finite experiments are described as whole-domain certificates.
