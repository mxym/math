# Round 3 actual finite residue growth

Owned source modules: `Entry002/GenericResidueGrowth.lean` and
`Entry002/GenericGrowthContradiction.lean`. All edits and compiler outputs are in
`${PRIVATE_WORKSPACE_PATH}`. Round 2 and the frozen
archive were not edited. No target definitions were modified.

The intended manuscript link is the actual nested selected residue observations
in v3 `references/entry002-v3-source.tex`, section 8, lines 512–541, following the
per-batch information cost in section 7, lines 447–510. The families start empty,
remain in one fixed finite prime pool, and observe one literal law
`(TimeLaw.at 0).advance (commonSchedule z ns N)`. The increment random variable is
the actual `incrementWord z (len j)`. No separate law is introduced per charge.

Proof reuse source: OpenAI math, family 028, pinned commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, Apache-2.0,
`../upstream-028/GaussianMoat/BatchCertificate.lean`, lines 71–90 and 111–148.
The dependent finite recursion and the final sum/telescope/strict-excess argument
are adapted. The new recursion additionally retains initially empty families,
actual label support, cardinality increments, actual log-weight increments, and
honest prefix budgets. Arbitrary additive `L`, actual `SignedResidueData L`, and
the actual basis and planar embedding replace Gaussian lattice/residue objects.
No Gaussian `certificate_no_walk` theorem or Gaussian lattice ball is imported
as a result. Existing main modules already provide generic information
inequalities and the genuine common-schedule telescope; those are used directly.
Requested guessed reference names `MainEntropy.lean` and `EntropyBudget.lean`
do not exist in the pinned upstream snapshot; the actual provided reference is
`BatchCertificate.lean` together with `InformationTelescope.lean` and the generic
compiled telescope in `Entry002/GenericTimeKernels.lean`.

New deterministic APIs:

* `commonSchedule_split_timeLaw` and `residueWordCharge_split_schedule` identify
  exact factorizations of the same law, including dependent residue observations.
* `actual_residue_growth` performs the finite dependent induction. Its local
  premise is the genuine actual selected-rate extension `ResidueGrowthStep`.
* `actual_residue_growth_rate_bound` derives the bound on the sum of rates from
  actual charges of the selected nested families and the actual step-ball
  cardinality. Its smoothing guard uses the predetermined prefix batch weights.
* `exists_uniform_growth_smoothing_size` chooses the smoothing length from
  predetermined batch budgets before any family or walk is selected.
* `finite_residue_growth_contradiction` derives `False` from the proved bound and
  strict scalar excess; it does not assume the contradiction as an input.
* `finite_allBins_growth_contradiction` additionally derives the rate sum from
  `allBins_rate` and exact `binEnum_sum` in `GenericNumericalSchedule.lean`.

Remaining application obligations are explicit: establish each local selected
rate on this literal common law using actual coverage/point-entropy and numerical
schedule guards, then instantiate the finite scalar excess. Neither an
ArithmeticInterface no-walk conclusion nor MainTarget is claimed by these
conditional finite-growth modules.

Verification commands (with local official Lean 4.34.1/mathlib toolchain):

    ELAN_HOME=$PWD/.elan .elan/bin/lake build Entry002.GenericGrowthContradiction
    ELAN_HOME=$PWD/.elan .elan/bin/lake env lean /tmp/Entry002Round3GrowthAudit.lean

Compiler evidence: `round3-residue-growth-build.log`, 3598 jobs, clean.
Audit evidence: `round3-residue-growth-axioms.log`, all 18 owned declarations
checked. Every audit reports only `propext`, `Classical.choice`, `Quot.sound`.
The actual theorem statements are printed in the same audit log.
Admission/Gaussian-specialization scan: `round3-residue-growth-admission-scan.log`
(empty). Source SHA256: `round3-residue-growth-sha256.log`.
