Continuum leading-power avoidance with nonlinear remainders
Separate proof checkpoint; original geometric version 3 remains frozen.

EXACT TARGET AND QUANTIFIERS
Fix a nonempty countable indexed family A_l of subsets of (0,infinity).
For each A_l there must be integers G,J>=1 such that every block of G dyadic
bins from index J onward contains a point of A_l. No measurability of A_l is
required. The family is an input to the theorem, BEFORE the avoiding set.
For every 0<epsilon<1 there is ONE closed, nowhere-dense, one-periodic E with
Lebesgue measure of E intersect [x,x+1] > 1-epsilon for every real x.
This E works for all l; real s,alpha>0; real y,c with c!=0; finite M>=0; and
arbitrary tail-defined functions f satisfying eventually on A_l:
  |f(a)-y-c*a^s| <= M*a^(s+alpha).
For EVERY rho>0 the values f(a) outside E with a in A_l and 0<a<rho include
infinitely many DISTINCT points. All tail functions/errors may depend on each
other; no regularity/measurability is imposed.

Written-reference comparison: archive/WRITTEN_PROOF.txt sections 1--8 has the
same family-first / E / all-real-parameters order. Its 'every sufficiently
small rho' is equivalent to every rho>0 by inclusion of smaller tails.
The formal theorem uses total f:real->real. DistinctMisses.totalTailExtension
and sampling_evidence/FinalTargetAudit.lean prove the tail-defined formulation.
The periodic result is stronger than its compact E intersect [0,1] corollary,
which is delivered separately and is not itself claimed to be periodic.

FORMAL ENDPOINTS (project/ContinuumRemainder/FinalProof.lean)
  robustCompactBlockerSpec_proved : RobustCompactBlockerSpec
  continuum_power_target : ContinuumPowerTarget
  compact_power_avoidance : the explicit compact [0,1] consequence
No endpoint assumes a routing/blocker specification. Specification.lean only
defines the targets; every routing, sampling, error, and measure premise used
by the endpoint is discharged by the concrete construction.

PROOF ROADMAP (all names are modules under project/ContinuumRemainder)
1. Sampling and Counting: LogSyndetic selects actual a_n in A_l intersect
   (0,2^-h). Their real input logs z_n=-log_2(a_n) have uniform upper/lower
   gaps and tend to infinity; a_n tends to zero. Each sufficiently late OPEN
   output window has uniformly many active inputs for every s in [s0,s1].
   Exact finite candidates retain the absolute U+T+|k| factor.
2. LogGeometry: generalize active point separation and earlier-key stability
   to real z_n; reuse the independently verified finite tree/routing geometry.
3. LogSignatures and LogRouting: the previously verified affine sign-arrangement
   theorem gives boundary-complete representatives for (s,log t). Their active
   local readouts agree for EVERY table assignment. Centers remain arbitrary.
4. LogRoutingProbability and SampleLocalProbability: prove own addresses are
   free/distinct and terminal addresses distinct after all selectors are fixed.
   Reuse the verified finite joint law and obtain the actual continuum miss
   bound, with actual sample counts and representative entropy.
5. ErrorDomination and ErrorSchedule: prove actual error<=positive radius r_U;
   prove T(U)=O(log U) and 4*2^(U+T+2)*r_U tends to zero. SampleSchedule chooses
   branching, depth, gaps, then arbitrarily late U with logarithmic window
   length. It simultaneously meets entropy, boundary, tail and buffer budgets.
6. SampleStableProbability: actual missed centers force local misses at the
   first default vertex. The exact atom partition and no-default law yield
   miss probability <=2p at every stable real center, without target assumptions.
7. RobustRepair and RobustAssembly: actual open inner and doubled outer buffers
   absorb every allowed error, including equality at the radius. The defined
   missed-center set is closed; finite Fubini gives expected densities <=2p and
   <=3p. Choose one actual outcome; cover exceptional centers openly; full
   perturbed-sequence convergence repairs EVERY center, yielding a blocker
   of density <6p. FinalProof closes RobustCompactBlockerSpec unconditionally.
8. Exhaustion: budgets indexed ONLY by (l,N,j,k,q,h), with compact real powers
   [1/N,N], lower error rates 1/j, magnitude bounds q, and signed coefficients.
   They produce a common open small U; E=real minus U. TopologyConclusion proves
   all shifted unit-density bounds, closedness, empty interior and compact
   corollary. DistinctMisses proves |f(a)-y|>=|c|a^s/2>0 eventually: arbitrarily
   small missed values approach y without equalling y, forcing infinite values.

BOUNDARIES AND LIMITS
Both activation endpoints are inactive. Grid cells are left-closed/right-open;
negative lifts/wraparound and all earlier selector reads retain exact keys.
Sign representatives include zero, intersections, coincident/degenerate cuts,
and compact parameter endpoints; logarithms are taken only after positivity.
Free-bit/terminal independence is proved at each fixed real parameter; shared
auxiliary selector reads are allowed. Zero atom masses/outcome weights require
no division. Empty finite candidate families are covered by the infinite-tail
repair. Radius is strictly positive; allowed error equality uses two OPEN
buffers. The nonnegative U+k and exponent upper bounds are retained. Negative
coefficients use reflection with half-open measure endpoint equivalence.
The positive power remainder rate alpha>0, nonzero c, bounded log gaps, fixed
countable family, and strict measure slack are essential stated hypotheses.
There is no theorem here for one E covering all configurations, arbitrary slow
remainders, all C1/flat germs, or merely positive upper Banach log density.

REUSE, EVIDENCE AND TRUST
All 45 ContinuumGeometric source modules are byte-identical to the verified
version-3 base. archive/verified-geometric-version3.zip has SHA256
747386b02dbd12ae6f7b763d79fdb1e9bd70ca1e195e1b84d943cb0bcff82cb5.
New proof sources are frozen in source-freeze.json; complete package hashes are
MANIFEST.json. Scoped sampling/error/exhaustion audit proofs and exact controls
are retained in project/*_evidence. ExpandedTargetProbe.lean independently
expands the target. No sorry/admit/new axiom/native_decide/unsafe is used.
Trust limits: official pinned Lean kernel/toolchain, unchanged pinned mathlib
and transitive dependencies, standard propext/Classical.choice/Quot.sound,
and accurate interpretation of the formal definitions. Classical choices and
huge finite trees make this an existence theorem, not a practical construction.
The original theorem's independent PASS does not transfer automatically to this
stronger theorem. External independent review, novelty and publication gates
remain separate; no publication/push/external contact was performed.

REPRODUCTION
Use official Lean 4.34.1 commit 5045d0056413266e57c625dcd7c365b10e377c52 and
mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 with the exact transitive lock.
For a new machine, unpack archive/verified-geometric-version3.zip separately
and follow its reproduce.py bootstrap after reading applicable network/runtime
instructions; preserve proxy/TLS/security settings. Do not run lake update.
Then replay this checkpoint using that toolchain and dependency packages cache:
  python3 reproduce.py --toolchain-bin /path/to/lean/bin \
    --dependency-cache /path/to/base/project/.lake/packages --output ${ORIGINAL_TEMP_PATH}
  python3 -O reproduce.py --toolchain-bin /path/to/lean/bin \
    --dependency-cache /path/to/base/project/.lake/packages --output ${ORIGINAL_TEMP_PATH}
Add --trust-zero for an empty trust-level-zero imported-closure replay.
The script creates a fresh own build in each output, verifies source/dependency
hashes/revisions and all new theorem axiom sets, compiles expanded/partial-tail
probes and exact positive controls, and requires all false controls to fail.
Checks use explicit runtime exceptions and remain enabled under python -O.

VALIDATION COMPLETED
Both evidence/normal-pass/report.json and evidence/optimized-pass/report.json
are byte-identical PASS (SHA256
99940d5cda8bac62600fbbfe9443f145c84ec6c4e90fca959d4bc8cb87e5234f).
Each run built from an absent own build directory, audited every new public
proof, and compiled six positive scoped audits plus the expanded target probe.
All six false controls failed for the intended false mathematical goal.
Two root-local empty trust-level-zero imported-closure replays passed, including
a fresh optimized build, with empty diagnostic logs. Internal complementary
reviews passed. No mathematical obligation remains in the assembled target.
The stronger external independent review and novelty gate remain PENDING.
Historical passing-audit selection and two false-fixture syntax issues were
corrected in the harness/fixtures; all frozen proof sources stayed unchanged.
