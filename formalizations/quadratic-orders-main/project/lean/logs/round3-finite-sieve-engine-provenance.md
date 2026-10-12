# Actual finite planar sieve engine proved

Owned module: `Entry002/GenericFiniteSieveEngine.lean`.

`ArithmeticInterface.large_step_prime_pool_no_walk` derives a finite actual
prime pool from the unchanged five-field ArithmeticInterface for every D≥1.
The pool is chosen before all lattice walks. The proof has no certificate,
coverage, positive-information, no-walk, component-finiteness, or target-result
hypothesis. The actual D-step metric is the basis/embedding metric.

`finiteSieveTarget_proved : FiniteSieveTarget` then proves the unchanged complete
generic finite planar sieve statement. Small step bounds follow by monotonicity
of edges; the actual Q² component bound follows from the existing proved
periodicity/König reduction. MainTarget still separately requires supplying the
arithmetic interface for all quadratic orders.

New proof chain:

1. A5 fixes δ first. `A.common_window_parameters` chooses a and separation K
   afterward and constructs actual dense separated finite dyadic windows using
   that same δ. The positive rate coefficient is topCoefficient(a)/4.
2. `exists_window_rate_excess` chooses a finite number W of windows from the
   actual `wordStepBall` cardinality. A common scalar m and actual windows J are
   chosen before all walks by intersecting proved eventual thresholds.
3. The actual finite pool is `dyadicPrimePool data J W`. Families are constructed
   by finite induction within `precedingDyadicLabels data (allBins W J) j`,
   retaining actual support, nesting, and hence honest predecessor log budgets.
4. Every charge is derived by `eventually_common_window_batch_charge`, using
   proved actual top/middle/bottom endpoint entropy, true-lattice backward
   coverage, actual posterior passing lists, and integer package sampling.
5. Every selected family observes the one literal law
   `(TimeLaw.at 0).advance (commonSchedule z (commonBlocks a m W J)
   (windowSmoothing W m))`. The normalized variable is the actual
   `incrementWord z (batchWordLength (binEnum (allBins W J) j))`.
6. `actual_selected_window_charge_sum_le` uses the actual pool logarithmic weight
   and true step-ball alphabet in the information telescope. The independently
   proved smoothing error contributes at most one in total.
7. The derived sum is at most log(actual step-ball.card)+1; `allBins_rate` and
   the chosen W give a strictly greater lower bound, deriving False.

Manuscript provenance: entry002 v3 §7–8, literal reference
`references/entry002-v3-source.tex`, lines 447–541. Finite dependent selection
and scalar summation are adapted from OpenAI math family028,
`../upstream-028/GaussianMoat/BatchCertificate.lean`, lines 71–90 and 111–148,
pinned commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0.
No Gaussian no-walk theorem, Gaussian metric normalization, fake lattice norm,
axiom, sorry, or native_decide is introduced or used.

Compiler command:

    ELAN_HOME=$PWD/.elan .elan/bin/lake build Entry002.GenericFiniteSieveEngine

Final engine compilation succeeds, 3889 jobs, with no warnings or errors.
Compiler log:
`round3-finite-sieve-engine-build.log`.

All four owned declarations, including the complete universal target proof,
were checked with #print axioms. Every result reports only propext,
Classical.choice, Quot.sound; the transitive dependency tree contains no
additional or admission axiom. Full statements and proofs are printed in
`round3-finite-sieve-engine-axioms.log`. The admission/Gaussian scan log is empty.
`round3-finite-sieve-engine-sha256.log` records the engine source and unchanged
Targets/Sieve hashes. All work is isolated in round3; round2/frozen workspaces
were not modified.
