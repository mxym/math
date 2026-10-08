# Changelog

## 2026-10-08 — complete Lean classification of all cycle chromatic-polynomial infinite log-concavity

- Closed the full **all-cycle graph-to-coefficients Lean proof chain** beyond the independently published C17 case. For **every n≥3**, proved the actual Mathlib `SimpleGraph.cycleGraph n` proper-q-coloring count equals evaluation of \((X-1)^n+(-1)^n(X-1)\) for every q, including q=0,1,2. The proof uses a complete-graph walk encoding, injectivity/cardinality equivalence and exact matrix-trace recurrence.
- Proved the **complete infinite log-concavity iff classification** for the absolute coefficients under zero extension: **3≤n≤11 iff all iterates stay nonnegative**, with a Lean-verified invariant-preservation argument for arbitrarily many iterates; five independent finite failures at n=12..16; and a **single symbolic factorization and positivity proof for every n≥17** detecting a negative third iterate at index 2. No finite scan is generalized without proof.
- Published eleven kernel-replayed mathematical modules, a root Lean library with fixed toolchain and Mathlib versions, per-source SHA-256, thirteen exact kernel axiom inventories restricted to the three standard axioms, a failing invalid-proof regression, a reproducible Lake replay script and a read-only GitHub Actions workflow. The earlier single-C17 formalization belongs to a parallel task and is preserved, not relabeled as newly authored. No Lean proof of an unrelated graph family or external human peer-review claim is made.

## 2026-10-08 — refute the arbitrary-mass Gaussian regular-simplex conjecture

- Gave a complete counterexample to Heilman 2019 v1 Conjecture 1.16:
  for every $0<p<1/4$, all regular-tetrahedral partitions with masses
  $(p,(1-p)/3,(1-p)/3,(1-p)/3)$ are strictly suboptimal for the Gaussian
  squared first-moment objective. Exact facet integrals and an actual
  equal-measure ball exchange prove strict gain. A strict mass-price
  argument rules out other regular apexes; weak compactness and an
  extreme-point argument prove existence of a genuine optimizer.
- Released the full six-page proof, exact quadratic-field controls and
  four partial Lean lemmas with a fresh 7,680-declaration empty-kernel
  replay. The equal-mass conjecture remains untouched. The related
  positive-noise unequal-mass theorem is credited; worldwide novelty
  and external human review are not asserted.
- Separately proved a positive-measure Erdős similarity class extension
  for growing logarithmic gaps $o(\log\log z_n)$ and useful late annuli,
  including ratio-zero and zero-logarithmic-density examples. Released
  its complete nine-page proof, exact controls and four partial Lean
  algebraic lemmas with a 7,157-declaration empty-kernel replay. This
  result does not resolve the full Erdős similarity conjecture.

## 2026-10-08 — strengthen sharp Bellman oscillation to every binary-orbit level

- Upgraded the newly certified 005 **no-quadratic-germ** theorem from an asymptotic `limsup` statement to an **every-index signed excursion**: for each `j>=1`, at least one of two explicit attainable ratios from `K_j*point^(*2^(j−1))` differs from its forced quadratic by `>1/4000` in the required positive/negative direction. It is not a numerical conjecture: **all nine** finite indices `j=1..9` pass strict rational Robbins/log-interval checks, and a single rational inequality `3/(64*1024)+1/(30*1024²)<1/20480` together with analytic dimension inequalities excludes **every j>=10**.
- Retained the independent canonical nonanalytic Gamma-profile failure (`d=8`, strict margin `>1/20000`), prior 005 geometric dependencies and interval replay outputs. This is a necessary constraint on a specific sharp scalar proof architecture, not an assertion about the still-open unrestricted spectral optimum.

## 2026-10-08 — prove universal no-quadratic-germ oscillation and reject canonical nonanalytic Bellman interpolation

- Strengthened the entry-005 sharp-Bellman method obstruction from positive powers/polynomials/analytic germs to **all continuous-at-zero homogeneous scalar profiles with a quadratic asymptotic expansion**, requiring only standard separate product/join induction on actual point-generated bodies. The binary `T5` orbit forces the unique coefficient `alpha=8/81*(c*+log(27/(4*pi))/2)`; a second actual family joining `2^(j−1)` points to the `j`th orbit body gives limiting self-product slack `<−1/200`. Therefore **every** sharp profile has explicit nonzero second-order oscillation: `liminf |psi−alpha*t²|/t²=0`, `limsup >1/4000`, excluding even twice-differentiable profiles **without a convexity hypothesis**. An independent exact rational checker certifies all numerical premises; the infinite statement is proved analytically.
- Derived a **canonical continuous nonanalytic Gamma-series profile** that interpolates all exact binary orbit anchor values, but proved it fails separate product closure by `>1/20000` at the actual dimension-eight body `(T1 x T2)*point^(*5)`. Independently reproduced the strict failure by a standard-library 136-bit outward-rounded rational interval checker with Binet–Stirling remainder bounds and a separate 192-bit SageMath/Arb `log_gamma` implementation. Every omitted infinite-series term is rigorously bounded; no finite extrapolation or floating optimizer is used.
- Published full analytic proofs, stand-alone ordinary/optimized reproducible programs, adversarial mutation controls, SHA-256 file inventories and read-only CI. The previously published formal-jet statements are now correctly interpreted as **conditional consistency identities only**: the stronger theorem proves no globally separately-closed smooth sharp scalar profile exists. The full product/join spectral constant remains open; no mathematical priority or external human review is claimed.

## 2026-10-08 — prove nonanalyticity and a unique divergent formal germ for every sharp T5 Bellman potential

- Proved that any scalar homogeneous Bellman potential that is **exactly sharp on the binary T5 orbit** and separately preserves the inherited product/join inequalities **cannot be real-analytic at H/D=0**, even with an infinite convergent Taylor series or unrestricted signed coefficients. The proof combines exact orbit interpolation with the **full Euler–Maclaurin Stirling series**, the factorial divergence of its Bernoulli coefficients, an analytic invertible variable change and uniqueness of asymptotic coefficients along the orbit’s geometric parameter sequence.
- Strengthened this to an all-orders **smooth-germ rigidity theorem**: if a sharp separately inductive profile is C∞ at the origin, then **every odd Taylor coefficient vanishes** and the even Taylor series is uniquely specified by an explicit Bernoulli/rational recurrence with zero convergence radius. Computed and independently replayed all exact coefficient formulas through t^12, along with a 16-term Stirling-Bernoulli prefix and analytic coordinate identities; the infinite conclusion follows analytically, not by extrapolation.
- Added exact standard-library Bernoulli/formal-series checkers, four new adversarial corruption cases, updated source hashes/CI and clear scope distinctions: these exclude real-analytic scalar **proof potentials**, not the binary T5 optimum itself, and do not assert the existence of any smooth nonanalytic sharp replacement.

## 2026-10-08 — exclude every finite polynomial sharp Bellman profile by infinite prime-rank rigidity

- Proved **multiplicative independence of every single binary-T5 orbit-step rational multiplier** by using Bertrand's postulate to choose a new prime dividing each central-binomial multiplier but none of its predecessors. Therefore these infinitely many rational logarithms are **linearly independent over Q**. This is an exact infinite theorem, not inferred from the first 13 prime witnesses replayed by the new standard-library checker.
- Combined that prime-rank theorem with the already proved **forced interpolation equality at every T5 orbit state** to rule out **all finite-degree homogeneous polynomial and finite-piece polynomial-spline potentials**, with arbitrary signed real coefficients, from certifying the candidate sharp growth constant by separate product/join Bellman closure. Neither convexity nor power-coefficient positivity is assumed for this no-go. At each fixed polynomial degree, all nondecreasing polynomial profiles have a **strict positive (degree-dependent) nominal rate gap**, by a compactness/Vandermonde argument.
- Added a complete mathematical proof and explicit Legendre-valuation replay of thirteen orbit levels, plus two new hostile controls for prime and valuation data. Updated reproducibility CI, proof audit and public navigation, retaining the earlier even-power sharp three-state dual proof unchanged. This is an obstruction to a proof architecture, **not** a claim that the T5 candidate is or is not globally optimal.

## 2026-10-08 — prove all-degree Bellman power-cone obstruction and sharp orbit constraints

- Established a **strict method-theoretic obstruction for all nonnegative even degrees, including arbitrary summable infinite series**, in the full point-generated projection-body product/join calculus: separate product-closure on just three explicit actual-body self-products forces a nominal logarithmic ceiling `T>486139/10^7`, strictly above the T5 binary-orbit value. The infinite-degree three-state moment LP is solved **exactly**, with unique positive primal degrees `2,4,8`, an explicit rational 3x3 dual and a certified all-degree analytic tail; this is **not** a lower bound for the actual class optimum.
- Derived the exact binary-recursion continuation series and proved its tempting scalar sharp upper potential fails join-superadditivity on `(T1 x T2)*(T1 x T2)` with a rigorously negative defect below `-3/10`. Proved **any continuous convex homogeneous sharp Bellman supersolution** must interpolate the entire T5 orbit exactly and must have an explicit uniquely determined quadratic germ at zero. A rational convex non-power hinge function was shown to evade the three isolated tests but to fail at the attained 85D binary orbit state, sharply limiting the no-go scope.
- Supplied complete standalone mathematical proofs, independently replayable standard-library rational/series checkers, ordinary/optimized mode comparisons, five hostile corruption tests, pinned file hashes, detailed source attribution, and a read-only CI workflow. The unrestricted spectral optimum remains open; no misleading global-optimality or priority claim is made.

## 2026-10-08 — prove infinite strict product-depth hierarchy and complete depth-two projection spectrum

- Established an **infinite strictly increasing hierarchy** of spectral optima for every fixed product nesting depth `k` in the point-generated Cartesian-product/affine-join class. At each finite `k` the maximum is *attained* and is an *exactly computable algebraic number*, whereas no finite depth attains the full-class limit. The corresponding asymptotic growth rates `e*lambda_k` strictly increase, so every bounded-depth grammar loses by a **dimension-exponential factor**. The proof combines a uniform sublinear product multiplier, a constructive central-binomial amplification step, and a certified finite-depth search cutoff.
- **Completely classified every depth-two expression in all dimensions**: the sharp primitive product state is the 42-dimensional square of the join of two `T5 x T5` blocks, with exact rational `Q=257554342358885086515/36893488147419103232`, hence spectral constant `Q^(1/43)`. Two analytic infinite tails and an **independent 2,770,504-candidate exact checker** (over 1,214 dimension splits) exclude all competitors. An independent producer pins each split's winning rational state, and a 170D third-depth example strictly exceeds the depth-two optimum.
- Released a complete mathematical proof, predecessor-source hashes and attribution, ordinary/optimized Python replays, four adversarial corruption controls, frozen finite split certificates and read-only CI. Historical entry-005 calculus, depth-one and Bellman packages remain unchanged. No exact all-depth optimum, external peer-review or priority claim is made.

## 2026-10-08 — convex Pareto envelope and universal even-row permanent transfer

- Strengthened the sharp four-row permanent/determinant inequality into a **complete convex Pareto envelope**: every convex functional nondecreasing in |per A| has its normalized optimum at one of the flat rank-one and monomial endpoints. Consequently, for every **real exponent r>=1**, the exact sharp power objective is max((3/2)^r,1+c), with complete equality classification and critical coefficient c=(3/2)^r-1.
- Proved a general even-row balanced Laplace transfer theorem valid in dimension 2m for all m>=1, and the universal bosonic symmetric-tensor coefficient identity sum(alpha! |c_alpha|^2)=per(UU*) with its exact collision-free orthonormal-row equality condition.
- Supplied 41,066 exact permutation/shuffle sign replays for n=2,4,6,8, rational bosonic/fermionic Gram checks, all-power endpoint controls, frozen ordinary/optimized reports and updated CI. The sharp 3x6 rectangular inequality that would close the full six-row case is stated only as an **unproved target**, not a theorem; no external referee, priority or full Lean claim is made.

## 2026-10-08 — sharp uniform nesting gap in every dimension from 55 onward

- Strengthened 005's **first mandatory nesting at d=55** to a **sharp all-dimensional multiplicative theorem**: for every integer `d>=55`, the full arbitrary-tree optimum divided by the two-layer join-of-two-simplex-products optimum is at least the known exact 55D rational ratio `666588049410094050176708629890606697662639715/661941565426077453299492872184552524829687808 > 1.007`. Equality is attained **only at d=55**; `d>=56` gives a strict factor `>101/100`, and the entire infinite tail `d>=85` gives `>209/200`. Additionally, the ratio grows **at least exponentially**: it exceeds `(1009/1000)^(d-84)/45` for each `d>=85`.
- Independently extended the complete two-layer sharp Pareto certificate from D=56 through D=85 (11,234 new attained states, 2,837,399 checked exact point/block operations), recorded thirty nested rational witnesses for `d=55..84`, and derived a continuous sharp two-layer envelope from the previously certified global block inequalities.
- Closed **all dimensions d>=85** by an explicit binary-orbit 85D body, join extensions using its remainder class modulo 11, monotonicity of the state ratio, eleven rational-power comparisons and an additional exact exponential-rate inequality; no finite-range extrapolation or float optimizer entered the proof. Included a self-contained written argument, source manifest, normal/optimized exact checker, adversarial corruptions, and read-only CI. All historical 005 source packages remain byte-preserved.

## 2026-10-08 — sharp norm-six principal-sieve period 1122

- Proved the exact minimum successful finite principal-ideal
  scalar period **1122** for 14 Euclidean steps in Z[sqrt(-2)];
  this is a factor-187 jump from the norm-four phase.
- Certified every lower squarefree period with 682 integer
  nonzero-voltage paths, and completely replayed 204,800 allowed
  residues as 6,688 components of maximum sieve size 2,283.
- Proved a separate closed exceptional **90-prime** component
  and global explicit prime size range [90,2283] for
  sqrt(6)<=D<sqrt(8). Published [full paper and code](notes/sqrt-minus-two-sqrt6-period/README.md).
  Exact arithmetic replay passed; no human-review/priority claim.

## 2026-10-08 — sharp radius-two prime graph jump and sieve classification

- Established the global Z[sqrt(-2)] component bound **7**, attained
  by exactly two components, for 2<=D<sqrt(6), all others <=2.
- Determined the unique minimal ten-step principal-ideal sieve at
  scalar period 6, including all composite-generator alternatives;
  generator complexity jumps from two to three at D=2.
- Released [complete proofs and integer evidence](notes/sqrt-minus-two-radius-two/README.md)
  with direct finite closure, three voltage obstructions, five
  lower-period witnesses, independent checker and 2,048-family replay.
  AI-assisted, no claimed priority or external peer review.

## 2026-10-08 — original literal sharp simplex upper Main

- Added the frozen 304-file v2 upper Main source package. It preserves 123 mathematical modules and the original target/constants, proving the bound for every prescribed maximizing simplex about its own centroid. The certified input is the complete 204-file composition; the originally delivered 203-file patch was missing one source and is not retrospectively called complete.
- Retained 12 adjacent final-copy audit receipts. Historical independent mathematical review and the producer's exact fresh-wrapper runs establish 123 rebuilt modules, 848 public proofs, 1,833 owned declarations, and genuine empty-kernel replays of the 54,277-declaration literal Main and 55,067-declaration all-owned closure. The final-copy reviewer rehashed the actual fresh objects/logs and independently tested source/cache attacks and literal/kernel controls; it did not repeat the whole compilation/replay.
- Integration passed normal/optimized sealed-source checks, deterministic archive reproduction, and both 91-case/730-entrypoint packaging suites. Prior repository content remains intact, with only additive navigation edits. This is the original gSharp upper theorem, not a later improved-constant candidate, and it excludes the separate lower proof. No new blanket license, authorship assignment, CI workflow, novelty or external human peer-review claim is made.
## 2026-10-08 — prove exact dimension 55 is the first mandatory nesting crossover for projection-body optima

- Extended the **complete all-tree Pareto certificate** from dimension 48 through **dimension 55**, validating 3,066 new attained states and **2,523,858** complete join/product closure candidates with an independent rational checker. The exact source was regenerated byte-identically from the SHA-pinned 48D base.
- Independently computed the entire join-of-two-simplex-products **two-layer subclass** through dimension 55, validating **5,611** Pareto states and **430,360** exact atom additions with a separate checker. Verified that all-tree and two-layer sharp maxima **coincide for every dimension 1–54**, but not at dimension 55.
- Proved both sharp dimension-55 rational values and explicit maximizers. The all-tree winner is `B(4,4) * B(5,5)^(*2) * [T7 x (B(4,4) * B(4,4))]`; the two-layer winner is `B(5,6) * B(5,5)^(*4)`. Their exact difference is strictly positive. Consequently **55 is the first dimension where nested product/join operations are necessary to attain a class optimum**. The earlier dimension-85 strict witness remains true; no assertion about geometric uniqueness, unrestricted convex bodies or asymptotic optimality is made.
- Added complete manuscript, production/checker separation, negative controls, ordinary/optimized exact replay logs, pinned hashes, dependency audit and read-only CI. Kept the historical version-2, version-5, dimension-48 and dimension-85 packages unmodified.

## 2026-10-08 — sharp four-row permanent/determinant tradeoff and parity tensor norms

- Proved the **exact** four-row complex-matrix inequality |per A|+c|det A|<=max(3/2,1+c) times the product of row Euclidean norms for every real c>=0, including all equality matrices and an averaged six-pair deficit controlling near-extremizers.
- Extracted the all-width two-row symmetric/alternating minor-energy theorem with sharp constant max(2-2/n,1+c) and complete three-regime equality classification, rather than only enumerating small sizes. An exact diagonal-to-flat interpolation certifies a quadratic critical deficit.
- Determined the exact complex-valued L2 norm max(1,(2/3)(1+24|t|)) for the S4 even/odd parity-mixture family, its sharp **within-family** TV threshold 1/4, and exact nonidentical-column tensor norm product. Broader uniform-marginal S4 laws and the nonreal coefficient pencil remain unresolved.
- Published a self-contained proof, integer-polynomial identity checker, independent Fraction tensor replay covering 43,896 permutation tuples, frozen ordinary/optimized reports, audit, hashes and read-only CI. The classical permanent-only result is attributed; older numbered entries remain unchanged. No external peer review, full Lean proof or priority claim.


## 2026-10-08 — exact small-radius Z[sqrt(-2)] prime graph and sieve classification

- Proved the complete graph structure at every real radius D<2,
  with exactly two exceptional 3-vertex paths, generic components
  of size at most 2, and no new prime edges at the norm-3 threshold.
- Proved sharp principal-sieve period 6 and classified all successful
  optimal-period ideal lists using three minimal positive bases and
  four maximal negative voltage witnesses, allowing composite generators.
- Published the complete [research note](notes/sqrt-minus-two-sharp-moats/README.md),
  12 finite exact witnesses, independent checker, and mutation tests;
  independently enumerated all 2,048 subfamilies of the 11 divisor ideals.
  AI-assisted, not priority-certified, Lean-formalized or human-refereed.
## 2026-10-08 — classify two-layer simplex-product spectra and prove an 85D nesting-depth gap

- Determined the unique global two-simplex-product spectral block optimum `(p,q)=(5,5)` with `log Q/D = log(189/128)/11`, and the distinct affine-defect optimum `(4,4)` with `log Q/(D-H)=log(175/128)/4`, valid for all positive integer pairs. Both infinite parameter tails are closed analytically, with 56 and 380 exact rational finite comparisons.
- Proved the exact two-layer join-of-products asymptotic growth constant `e*(189/128)^(1/11)` and a **strict dimension-85 separation**: a product of earlier joins, followed by a join, exceeds all 85-dimensional two-layer bodies. The strict asymptotic depth gap follows from an exact rational single-witness spectral comparison. No unrestricted-class sharp dimension-85 value, first crossover, or full optimum is claimed.
- Added complete proof, portable exact checker, normal/optimized replay, hostile parameter controls, dependency audit and source hashes, leaving historical 005 versions and the previous 48D all-tree certificate untouched.

## 2026-10-08 — sharp all-tree projection-body extrema through dimension 48

- Proved an exact Pareto-dominance dynamic program for arbitrary point-generated Cartesian-product/affine-join expression trees, with full induction showing no optimum is lost by coordinatewise frontier pruning. This is an all-dimensional algorithmic theorem.
- Independently certified sharp normalized projection-body maxima for **all dimensions 1–48**, extending 005 v2's exact range through dimension 14. At dimension 48 the optimum is `105488578125/34359738368 > 3` times the simplex, attained by the join of three `T4 x T4` and two `T5 x T5` blocks. Each checked dimension has an optimal join of simplex products; complete equality classification is not asserted.
- Added a 6,494-state exact rational certificate, independent checker for 1,956,775 product/join candidate pairs, read-only reproduction commands, negative controls, complete optima table and trust-boundary audit. Inherited v2 geometry remains pinned and untouched; no extrapolation to dimension 49+, asymptotic optimum, unrestricted convex bodies, priority, or external peer review is claimed.

## 2026-10-08 — literal simplex-truncation sharpness in Lean

- Published the exact 365-file v2 sharpness formalization and deterministic archive, preserving all 125 mathematical modules. The literal truncationSharpnessGoal uses the actual geometric defect, a global maximum inscribed simplex, its original centroid, and exponent 1/(d−1), with no assumed formula for these objects. It existentially selects a maximizing simplex and does not assert the same excess for all maximizers.
- Retained the independent final-copy review and selected evidence: 125 fresh modules, 850 public proof declarations, 1,849 safe owned roots, and a 55,163-declaration actual empty trust-zero kernel replay. Integration reran normal/optimized integrity, deterministic archive construction, and both 83-case/666-entrypoint packaging suites. Reused dependency caches remain part of the stated trust boundary.
- Added the [release manifest](releases/2026-10-08-simplex-truncation-sharpness-v2.json), preserved all earlier releases and unrelated files, and added only navigation to existing files. The sharpMainGoal upper theorem is not part of this historical lower-bound checkpoint. No new blanket license, authorship assignment, CI workflow, novelty certificate or external human peer-review claim is introduced.

## 2026-10-08 — exact norm of every complex three-row permanent pencil

- Proved the **exact global norm** for all complex determinant coefficients: the optimal normalized three-row pencil constant is the maximum of `2/sqrt(3)`, `|1+lambda|`, `|1-lambda|`, `|lambda+i/sqrt(3)|`, and `|lambda-i/sqrt(3)|`. Five elementary row configurations attain the candidates. The earlier exact coefficient lens is the corresponding norm sublevel set and remains intact.
- Derived an explicit Hermitian determinant decomposition with three nonnegative terms, proved all-parameter sufficiency analytically, and certified two universal polynomial identities by 4,096 exact rational six-variable interpolation nodes each. Ordinary/optimized Python modes and corrupt-formula controls pass.
- Strengthened the permutation application to an **exact optimal amplification factor** `max(1,(sqrt(3)/2)(1+6|t|))` for every uniform-marginal three-row law, including outside the stable TV region, and to its sharp product over independent nonidentical columns. Ten rational witness cases (960 permutation tuples) replay exactly; the general tensor identity is proved by induction.
- Updated the manuscript, audit, source manifest, frozen reports, and read-only CI without changing historical source manuscripts. No world-first/priority, complete Lean or outside human-review claim is made.

## 2026-10-08 — complete complex permanent–determinant coefficient lens and endpoint

- Classified the exact complex coefficient lens `|lambda|^2+2|Re lambda|<=1/3` for the all-matrix sharp pencil `|per A+lambda det A|<=2/sqrt(3) product_i ||row_i(A)||_2`. Its largest centered disk gives the sharp `|per A| + (2/sqrt(3)-1)|det A| <= (2/sqrt(3)) product_i ||row_i(A)||_2` for every **complex** 3x3 matrix, with joint sharpness and all equality cases (zero row, monomial, equimodular-column rank one). This is a strict complex strengthening of the existing real three-row result, not a duplicate claim to the known real radius.
- Derived the exact iff radius `1/sqrt(3)-1/2` for **complex-valued** L2 permutation products with uniform one-point marginals, endpoint equality types, and independent/nonidentical-column tensorization.
- Added the full Hermitian principal-minor proof, exact rational 1024-node full lens certificate, independent Q(sqrt3) 256-node disk certificate, 60 exact Q(i,sqrt3) matrix-entry regressions, negative controls, ordinary/optimized output comparisons, audit, hashes and read-only CI. No earlier numbered manuscript was changed; no priority, external referee or complete Lean claim is made.

## 2026-10-07 — Eisenstein graph maxima and sharp principal-sieve periods

- Proved exact unique largest irreducible-element component sizes 48
  (six-unit steps) and 132 (eight-neighbor steps); remaining components
  are bounded by 6/74, respectively.
- Proved optimal scalar periods 6 and 546 for finite principal-ideal
  sieves, and completed the unique optimal two-generator and four-list
  optimal four-generator classifications, even allowing composites.
- Added 333 lower-period and 36 composite-rigidity voltage witnesses,
  five quotient partitions, two exceptional closures, an independent
  exact checker and tamper tests.
  See [the research note](notes/eisenstein-prime-components/README.md).
  No external referee or priority claim.

## 2026-10-07 — reconcile parallel independent-arity 005 proofs

- Recorded that the `de012fc` and `b64b11c` proof packages concern **one identical all-positive-integer independent-arity classification**, not two distinct advances. Their different analytic tail decompositions and exact rational checkers both replayed successfully; hashes and the older 005 v5 winner certificate were checked.
- Linked each package to the other and added a scoped model-assisted cross-audit. Preserved the two proof records and avoided retroactive claims of independent first discovery or external review.

## 2026-10-08 — unified traditional avoidance manuscript, revision 2

- Published the exact reviewed 14-page PDF and TeX with the complete traditional proof, compact/geometric corollaries, source correspondence, and preserved missing-hypothesis correction history. The frozen 30-file public package preserves all 17 original revision-2 source members without editing the mathematics or assigning authorship.
- Verified all 12 external formalization/evidence links at the actual prepublication base. Bound the complete 184-file geometric and 278-file continuum formalizations to that remote tree. Both normal and optimized integration runs passed all public checks, the 65-module/759-declaration/20-step/57-declaration source comparisons, and isolated three-pass PDF rebuilds with exact extracted-text equality. No new Lean build or kernel replay is claimed by these manuscript checks.
- Added adjacent public packaging-review and integration records, a frozen archive, and a [release manifest](releases/2026-10-08-unified-avoidance-revision2.json). Retained all prior repository files and releases. Independent model review does not certify novelty or constitute external human peer review; the author field remains blank and no new blanket license or CI workflow is added.
## 2026-10-07 — certify the unique second-best homogeneous product/join recursion

- Strengthened the two independently produced first-place classifications: among all positive integer triples `(m,k,p)` with `K_0=T_p, K_{j+1}=(K_j^m)^{*k}`, the **unique second-best asymptotic projection-volume rate** occurs at `(2,2,6)`, below winner `(2,2,5)`.
- Proved all other triples satisfy the strict universal bound `log Λ < 10479/10000`, while `(2,2,6)` is strictly above that threshold by an exact level-five lower interval, the analytic all-level multiplier `D_j>3`, and the unchanged first-place upper certificate. New normal/optimized `Fraction` checker covers 27,690 regular finite triples, 208 sharpened finite triples, and 930 large-join endpoint inequalities, with three analytic infinite tails.
- Preserved and cross-credited the independently developed all-arity proof using a cutoff of 20; repaired one accidental formula-control character in that proof without changing its mathematics or certificates. No claim is made about nonhomogeneous trees, full Lean formalization, external peer review or universal priority.

## 2026-10-07 — classify all homogeneous projection-body product/join arities

- Proved a sharp **unique optimum** for all simplex-seeded homogeneous recursions `(K^m)^{*k}` with arbitrary positive integers `(m,k,p)`: `(2,2,5)` uniquely maximizes the limit. The strict competitor log ceiling `131/125` is separated from the inherited lower endpoint `2.8534`.
- Added a complete analytic proof splitting the infinite parameter tails and a standard-library exact rational checker for 6,155 finite competitor triples, 19 boundary simplex roots, and all tail endpoints. Machin arctangent bounds certify the input pi interval; both regular and optimized Python modes agree. Original 005 v2/v5 sources remain unchanged.
- Recorded the inherited-geometric and winner-certificate trust boundary; this does not optimize arbitrary alternating/nonhomogeneous operation trees, certify priority or constitute external review.

## 2026-10-07 — continuum-power remainder avoidance in Lean

- Added the frozen 278-file stronger source package, retaining all 110 project Lean files without changes. Its closed endpoint proves prescribed-family continuum-power avoidance with eventual power-controlled remainders and infinitely many distinct escaping outputs in every positive tail, together with the compact corollary.
- Published the exact deterministic source archive, six adjacent final-copy review files, and a [release manifest](releases/2026-10-07-continuum-remainder-avoidance.json). The fresh-copy wrapper rebuilt 65 owned modules, checked 568 public theorems, and replayed 34,923 endpoint-union and 35,620 all-safe closure declarations into empty trust-level-zero kernels. The final-copy reviewer independently cross-checked its artifacts/logs and ran 72 hostile entrypoint checks; it did not repeat the full build/replay. The historical independent mathematical audit retains its own attribution.
- Corrected public attribution of the retained import-only KernelReplay test: the genuine empty-environment replays belong to the independent replay programs. Preserved all prior releases and unrelated files. No new blanket license, installed CI workflow, novelty certification, or external human peer-review claim accompanies this release. The family is fixed before E; arbitrary slow remainders and a universal-family avoiding set are outside scope.

## 2026-10-07 — Fock-profile variational ceiling for binary tensor rigidity

- Completed the natural square-summable finite-first-moment closure of the reflected boundary-profile variational problem and proved that its supremum is attained.
- Replaced the previous three-term lower witness by an exact five-term rational Fock polynomial, raising the rigorous tensor liminf lower constant from 0.623586 to > 0.6238973.
- Proved an infinite-dimensional dual operator ceiling Lambda_prof <= 779/2000 by parity rank-one Schur complements, alternating rational exponential bounds and 28 rational t-intervals with strictly positive exact Bernstein coefficients. Hence 0.6238973 < kappa_prof <= 0.6240993511.
- Replayed the committed checker from the public raw GitHub file under ordinary and optimized Python; both runs pass. The ceiling applies only to the reflected boundary-profile mechanism and does not improve the true tensor upper constant 2^(-1/2). No external peer review, complete Lean formalization or priority claim is asserted.


## 2026-10-07 — full original geometric-avoidance Lean proof

- Added the exact independently model-audited 184-file revision-2 source package for the closed original all-real affine-geometric MainTarget, with one common compact set, strict Lebesgue-measure bound and arbitrarily late escaping terms for every 0 < q < 1.
- Published adjacent final-copy audit evidence and a deterministic source archive. The final independent replay rebuilt 46 modules, checked 454 public roots, and replayed the 34,771-declaration main closure in an empty trust-level-zero official Lean kernel. All 21 positive, 22 intended negative and 1,176,885 exact arithmetic controls passed, with 136 packaging-guard outcomes. Integration independently repeats source-integrity, packaging and deterministic-archive checks.
- Preserved the entire historical 101-export checkpoint and all unrelated repository files. The [release manifest](releases/2026-10-07-geometric-avoidance-v2.json) binds the source, audit evidence and additive navigation. No stronger nonlinear-remainder proof, new installed workflow, blanket license, personal-author assignment, online-bootstrap validation, remote-CI success, novelty or human peer-review claim is included.

## 2026-10-07 — boundary-profile binary tensor rigidity

- Proved a general finite boundary-profile limit theorem for the sharp binary complete-commutator constants, reducing every fixed reflected edge profile to an explicit Gaussian/Fock variational quotient.
- Certified the rational three-term profile a0=1, a1=4627/3125, a2=-58 sqrt(2)/125 and obtained liminf C_p/p^(1/4) > 0.623586.
- Reconciled the concurrently published exact two-band family: its asymptotic profile is contained in the new framework, its closed constant 0.6218758237... is strictly smaller by an exact rational-squaring check, while its all-p>=10 finite closed formulas remain a distinct strength.
- After the concurrent note proved that same constant optimal for fixed-width palindromic profiles with axis-local projection maxima, certified that the new profile violates the necessary condition exactly: gamma1^2 + sqrt(2) gamma2 = 12346629/9765625 > 1. Thus the stronger bound is an explicit off-axis mechanism, not a contradiction of the subclass optimality theorem.
- Added two separately implemented exact rational checkers using different exponential majorants, frozen reports, a proof audit, and ordinary/optimized replay. Numerical finite-order optimization is diagnostic only; no novelty, human peer-review or whole-paper formalization claim is made.

## 2026-10-07 — binary T5 limit interval

- Strengthened entry 005's inherited binary T5 recursion from the previous one-sided endpoint to the certified two-sided interval 2.853465550695797 < Lambda_(2,5) < 2.853465550704.
- Retained the Robbins exponential correction, used rigorous Machin/Taylor bounds on both sides, and reduced the endpoints to exact-rational logarithmic comparisons after reconstructing R_7.
- Added a standard-library checker passing ordinary and optimized Python. The result fixes the rate of this particular recursive construction to an interval of width below 8.3e-12; it does not prove global optimality in the product/join class or alter the positive-sextic Bellman upper theorem.

## 2026-10-07 — source-overlap and target-tail synthesis

- Added the exact independently model-audited 108-file synthesis package: six-page written proof, editable source, 57 byte-exact historical dependencies, proof reconstruction, finite regression controls and deterministic source archive.
- The global zero-extended density-root characterization holds for 1 < s < infinity and characterizes the linear-overlap method. Applications retain the separate (P), second-moment and proper-convex/L2 hypotheses; inherited sufficient directions and derived bounds remain attributed.
- Repeated normal/optimized integrity, fail-closed packaging and regression checks during integration. The [release manifest](releases/2026-10-07-transport-source-tail-synthesis-v1.json) records exact file identities. No universal transport necessity, full Lean proof, human peer review, novelty or priority certification is claimed. Historical mathematical files and the programme coverage map remain preserved.

## 2026-10-07 — dimension refinements of sharp simplex stability

- Published the exact 40-file quadratic-dimensional written refinement, with coefficient at most 4096 d², as the strongest dimension bound in this repository. The sharp 1/(d−1) exponent, every prescribed maximum simplex and its original centroid remain unchanged.
- Preserved the exact 35-file 2^20 d^6 companion method, including its 11-page PDF, shared weighted-anchor argument and linear lower obstruction. These are stages of the same entry-005 refinement; optimal dimension order remains unresolved.
- Included independent model-conducted final-copy evidence, frozen deterministic source archives, fresh normal/optimized finite and integrity replay, and a [changed-file manifest](releases/2026-10-07-dimension-refinements-v1.json). No full Lean, human peer-review, novelty or priority claim is made. All unrelated historical bytes and Git modes are preserved.

## 2026-10-07 — additive 101-export Lean checkpoint

- Added seven finite stochastic-matrix exports and 26 projection-cap/constant exports to the preserved 68-export project. All original theorem signatures, logical axiom sets, protected proof/pin/source bytes and prior compiler declarations are preserved.
- Independently repeated normal and optimized clean owned-module builds and adversarial checks. The actual-body cap/Hausdorff theorem uses genuine intrinsic projection-volume deficits; the exact scope and trust boundary are in the [final integration audit](verification/2026-10-07-lean101-independent-audit/README.md).
- Published the exact 452-file frozen tree, deterministic [source archive](releases/2026-10-07-lean101-verified-checkpoint.tar.gz) and [release manifest](releases/2026-10-07-lean101-v1.json). Five goals remain unproved definitions; no full sharp simplex/avoidance result or actual simplex-volume bridge is included. Historical unrelated files are unchanged.

## 2026-10-07 — continuum powers, semiconvex entropy and conditional quadratic fluctuations

- Added the exact independently audited 29-file continuum-power avoidance release, with its 11-page written proof, preserved source snapshots, exact finite controls and deterministic source archive. The affine geometric-progression consequence is restricted to the dated BGKMW Question 1 formulation; no current-open/priority or general positive-upper-Banach-density theorem is asserted.
- Added the exact 29-file semiconvex Gaussian entropy release, nine-page proof, sharp strict-horizon comparison, conditional extension and counterexamples. The helper-domain correction and metadata-only final-copy correction are disclosed; no general nonconvex LSI is claimed.
- Added the exact 70-file conditional conserved-quadratic release and complete deterministic archive. Smooth compact support, H1–H6 and input F remain explicit; pasted covariance, true first-moment transfer and unresolved true covariance remain distinct.
- Preserved every older proof, Lean, certificate, source archive and workflow byte/mode. Fresh integration replay is scoped to finite controls and exact integrity, with no new PDF rebuild, complete Lean, human peer review, journal or novelty claim.

## 2026-10-07 — bounded clusters, critical covering gauges and arithmetic sieves

- Added the exact independently audited 47-file avoidance/covering release: a 10-page bounded-cluster selector proof, a 14-page prescribed-gauge Banach nonembedding proof with its supporting analytic appendix, 14 pinned primary-source snapshots, preserved upstream credit/license and exact finite replay.
- Added the exact independently audited 26-file conditional rank-one/all-degree-restoration arithmetic supplement, with a nine-page proof, unchanged cubic F6/F8chain certificates, archival originals, strict public checker derivatives and ordinary/optimized replay.
- Added both unchanged deterministic source/certificate archives and a changed-file manifest. Finite avoiding maxima 6 and 56 remain separate from irreducible cardinality bounds; the supplied rank-one gate and exact step-set hypotheses remain explicit.
- Preserved every older proof, Lean, certificate, archive and workflow file byte/mode. Four narrow catalogue/status edits explain scope, replay and the documented arithmetic directional-reference typo without changing frozen payloads. No universal avoidance/moat, minimal dimension, full-paper Lean, human peer review or novelty claim is made.

## 2026-10-07 — sharp simplex endpoint, strict-domain slack and positive sextic bound

- Added the independently audited 45-file eight-page sharp simplex package, attaining 1/(d-1) for arbitrary convex bodies and every prescribed maximum simplex about its own centroid. Explicit local/global constants and the preserved truncation family establish sharpness for this theorem class; the earlier 1/d package is unchanged.
- Added the separate 18-file 12-page retained-deficit/strict-domain complete-calculus note. Complete constant two and its proof architecture remain credited to OpenAI's pinned direct manuscript; the quantitative strict-domain gap may vanish in the outer limit. No first-resolution or novelty claim is made.
- Added the independently reviewed corrected 15-file seven-page positive sextic Bellman package, with the product/join-class bound 2.8534 < Gamma_C <= exp(104867/100000) < 2.85386. The exact optimum, inherited lower construction and unrestricted-body question remain unchanged.
- The corrected certificate/audit ZIP preserves all 143 original entries and adds exactly two recovered ancestor manifests, yielding 145 entries and all 63 pinned ancestor sources. Retained historical full-tail arithmetic reports and fresh integrity/coverage checks have separate scopes; no fresh full-tail replay is claimed by this integration.
- Added four narrow navigation/status changes and a changed-file manifest. Preserved all older proof, Lean, certificate, workflow and source archive files and modes. Analytic model audits, finite arithmetic replay and PDF/integrity checks are not whole-paper formalization, human peer review or priority certification.

## 2026-10-07 — 002v4 verification repair

- 002v4 verification repair: enforce integer witness fields, bind endpoint data and labelled subsets to the stated sieves, clarify the squarefree-q definition, and refresh manifest hashes. All 19 corruption controls reject in normal and optimized Python; valid replay outputs are unchanged. Mathematical claims and scope are unchanged.
- Added [focused independent audit/control evidence and offline replay](verification/2026-10-07-002v4-verification-repair/README.md), with source pins, exact original checker bytes and normal/optimized results. The [repair manifest](releases/2026-10-07-002v4-verification-repair-v1.json) binds the five-file repair and evidence package. All Lean68, compact cubic, certificate, main manuscript and unrelated source bytes are preserved.


## 2026-10-07 — finite Lean68 and compact cubic supplements

- Added the final independently audited 109-file public68 Lean export, preserving its proof, reporting, coverage, signature/axiom log and control bytes. Lean 4.34.1 and all nine dependency revisions are pinned; all 68 exported declarations use only propext, Classical.choice and Quot.sound.
- The formalized scope covers finite/scalar algebra, recurrences and normed-relation/cofactor mechanisms. Full convex geometry, integration, exposedness, geometric stability/classification and global optimality remain outside scope.
- Added the separate 21-file ten-page compact cubic contact/mean package. Its exact-source sign-off is unchanged, and the public TeX has only the three approved review-status substitutions. Gaussian, matched-layer, activity-summed and unsummed full-unit-amplitude extensions are excluded.
- Added reader links and a changed-file manifest. Publication integration checked exact hashes/modes and replayed the cubic offline review verifier and finite checker; it relies on the already completed independent Lean rebuild. All historical manuscript/certificate bytes and unrelated files are preserved.


## 2026-10-07 — stronger endpoint stability and bibliographic correction

- Added the complete five-page integrated-witness proof of the explicit 1/d lower-end modulus for arbitrary convex bodies and every maximum inscribed simplex with its own centroid. The separate 1/(d-1) truncation obstruction leaves a gap.
- Added the complete 44-page symmetric upper-end assembly, with both explicit 1/(3d) and 1/(3(d-1)) bounds for the full affine line/plane product equality class. The standalone geometry interface explicitly states origin symmetry; the obstruction ceiling remains 1/d.
- Added an independent 11-page bibliographic correction bundle for the historical 1/(6d) theorem, without changing its mathematical proofs. The corrected article is the active catalogue reference; the original release bytes remain untouched. The separate v4 attribution patch is retained for review, not applied.
- Published exactly 129 audited package files, source archives for both stronger proofs, explicit dependency pins and bounded normal/optimized verification. All 60 final PDF pages were inspected. File identity, model-assisted analytic review, finite replay and visual checks have distinct scopes.
- Preserved every historical numbered version, earlier note package, concurrent file and mode. Narrow catalogue/verification edits and a non-self-referential changed-file manifest record integration. No inverse-Minkowski dependency, novelty/priority certification, optimal composed exponent, human peer review or full Lean verification is claimed.

## 2026-10-07 — mixed Bellman ceiling and simplex-truncation obstruction

- Added the 11-page mixed Bellman proof, exact finite and infinite-tail certificates, portable verification, dependency map and editable source archive. The claim Gamma_C <= exp(1049/1000) < 2.855 is restricted to finite point-generated product/join expressions and affine isomorphisms on affine hulls; rank-dropping maps are excluded.
- Added the actual separate independent Bellman checker, full historical audit and unchanged exact evidence. The public replay freshly checks all finite rectangles, tail intervals and elementary constants in both Python modes; other copied control reports are explicitly historical evidence.
- Added the eight-page exact simplex-truncation proof and 33-file package. It establishes an exponent ceiling 1/(d-1) and necessary endpoint constants, not a universal endpoint upper estimate. It does not depend on the separate inverse-Minkowski positive extension.
- Added narrow catalogue and verification navigation plus a changed-file release manifest. Numbered manuscript versions, Lean files and unrelated supplements remain byte- and mode-identical. No priority, external peer-review, formalization or optimal-universal-bound claim is made.

## 2026-10-07 — 002 v4 Gaussian F8 period optimality

- Proved that every successful finite principal-ideal periodic sieve for the Gaussian eight-neighbor step graph has common scalar period at least 130; the version-3 five-generator period-130 sieve attains equality.
- Reduced arbitrary principal-generator lists to the maximal Gaussian-prime sieve over the radical of the common scalar period, so composite, nonprimitive, inert, split and ramified generators cannot evade the lower-period obstruction.
- Added exact nonzero-voltage witnesses for all 79 squarefree radicals below 130 (5009 stored F8 steps, maximum witness length 129), plus an independent checker that reconstructs prime generators, ideal membership and the complete failed-radical list.
- Replayed the frozen period-130 positive certificate, recovering 4608 allowed residues, quotient component bound 580 and the inherited conservative Gaussian irreducible-component bound 92820.
- Classified the sharp-period five-generator endpoint: every successful period-130 sieve needs at least five generators, and with exactly five the list is unique up to associates and order. Exact endpoint witnesses cover all 47 nonunit divisor ideals of 130, all 31 proper prime subsets and 123 proper-subideal replacements.
- Proved the parallel Z[sqrt(2)] F8 classification: minimum principal-sieve period 14; at the sharp period at least two generators are needed, and the two-generator endpoint is exactly one of the two conjugate pairs {sqrt(2), 3+sqrt(2)} or {sqrt(2), 3-sqrt(2)} up to associates/order.
- Added 38 exact real-quadratic failure witnesses covering all nine lower radicals, all 11 nonunit divisor ideals at period 14, five failed prime subsets and 24 proper-subideal replacements; ordinary and optimized replays are byte-identical.
- The optimality claim is restricted to the finite principal-ideal periodic-sieve framework; it is not an unrestricted lower bound on all proofs or on the true Gaussian component size.

## 2026-10-07 — 006 v2 log-bi-Lipschitz profile avoidance

- Proved that positive logarithmic upper Banach density is preserved by every profile whose logarithmic-coordinate map is bi-Lipschitz on a tail.
- Extended the version-1 robust nonlinear-avoidance theorem from integer monomial leading terms to arbitrary prescribed countable families of such profiles and vanishing relative-error moduli.
- Added simultaneous corollaries for arbitrary prescribed positive power exponents, power-log profiles, differentiable slowly varying factors, and all convergent Puiseux germs through rational leading exponents.
- Reran the inherited version-1 exact robust-cover checker under ordinary and optimized Python with byte-identical reports; SHA-256 efd03ab6f3d92e2f96b10f4441114dcabccde2cc314bb6f872f59a3410d67e50.
- Added a proof audit and pinned v2 source manifest. The theorem does not claim simultaneous avoidance of uncountably many profiles, all C1 diffeomorphisms, or flat smooth germs; no novelty or formalization claim is made.

## 2026-10-07 — symmetric upper-end and restricted virial/stress supplements

- Added the 11-page symmetric projection-cone stability proof, explicit d^15 deficit^(1/(6d)) bound and corner-truncated-cube obstruction to powers above 1/d. The distance is to the full line/plane product equality class; optimal exponent and dimension-independent power are distinguished.
- Added the 12-page full-density virial/stress proof under compact initial support and pinned H1--H6 imports. This is a restricted first-order mean result, not a complete one-particle corrector or an extension of the fluctuation theorem to unbounded tests.
- Included complete editable source archives, precise public dependencies, proof-audit scope, package manifests and normal/optimized offline verification. Preserved the already visually audited PDF bytes; no Lean formalization, external peer review or novelty claim.
- Clarified only the Bellman audit summary's phrase “affine images” to “affine-isomorphic images on their affine hulls,” consistent with v2's dimension-indexed recursive class. No manuscript bound, proof or certificate changed.
- Preserved every unrelated file and mode, including parallel 005 work. The additive release manifest pins the base commit/tree and each changed payload file.

## 2026-10-07 — functional hard-sphere manuscript and effective-rigidity supplement

- Added manuscript 009: strong-dual generalized-J1 convergence of exactly centered hard-sphere fluctuation fields on the prescribed regular kinetic interval, conditional on the explicitly restated pinned upstream analytic package. All new geometry, localization, remainder, chaining and topology proofs are included.
- Repaired and independently rechecked the repeated-pair schedule-slot extraction before public release. Added the 19-page PDF, all nine TeX files, source archive, precise dependency inventory, public technical audit and artifact checks. No quantitative CLT rate, fixed-Sobolev tightness, or true-flow high-moment transfer is asserted.
- Added a nine-page quantitative simplex-rigidity supplement with explicit d-dependent constants and exact checks. Credited the stronger prior planar Banach–Mazur estimate; no novelty, optimality, dimension-independent or symmetric upper-end stability claim.
- Recorded the independent 005 v4 equality audit. Preserved all historical version files and unrelated parallel work, and recorded a complete changed-file manifest.

## 2026-10-07 — critical boundary slow-variation supplement

- Extended 008's critical source-boundary construction to positive C2 slowly varying factors under the stated derivative hypotheses. Proved the sharp implicit modulus at every sufficiently small distance, not merely along a sequence.
- Proved the logarithmic / iterated-logarithmic / pure one-third hierarchy and a necessary-and-sufficient root-Sobolev criterion within the precise displayed family.
- Included a counterexample showing why the implicit inverse cannot generally be replaced by the naive power argument. No general source classification or fixed atom-count obstruction is asserted.
- Added a complete six-page source/PDF bundle, clean rebuild and visual checks, proof-review record and exact changed-file manifest. Original version files are unchanged; no new numbered paper, priority claim or external peer-review claim.

## 2026-10-07 — manuscript 001 version 5 and supporting audits

- Added exact minimum-density weight and fixed-source Sobolev little-o results; cross-credited the root-density/Fisher criterion shared with 008.
- Added a smooth full-support construction with the necessary stronger scale separation for stretched-exponential logarithmic-power obstructions, with sequence and endpoint qualifications explicit. Retained the complete v4 Gaussian results and pinned v3 potential dependency.
- Added a separately audited six-page hard-boundary stretched-exponential supplement and an independent analytic audit/expanded exact replay of 008. No additional numbered paper or duplicate-result count.
- Added a dated 005 clarification: explicit spectral exponential bound, fixed-dimension stability scope, and a later navigation-only historical hash difference. Frozen v2/v3 files are unchanged.
- Preserved historical papers and parallel publications; recorded source, build, review, and changed-file hashes.

## 2026-10-07 — manuscript 005 version 3

- Proved the random-law determinant comparison with complete simplex-support lower-equality cases under a finite first moment; retained singular horizontal tuples and derived an exact cancellation-defect identity with finite sign witnesses.
- Closed the explicitly reserved general-convex-body equality case for the cone invariant and proved uniform dimensionwise qualitative affine stability in maximum-simplex position.
- Proved the sharp centrally symmetric bound a <= 1/2, universal planar equality, and an exact octahedron strict case. No complete higher-dimensional upper-equality classification is claimed.
- Strengthened spectral nonattainment to an explicit Cartesian square of a self-join, with a sufficient threshold and rational cross-powered comparisons. The optimal recursive asymptotic constant is not determined or numerically improved.
- Published independent exact checking of 23 laws, 18,199 ordered tuples, 1,149 balanced-sign cases, five spectral recipes, 126 octahedron minors and seven rejected corruptions. Normal and optimized reports agree byte-for-byte.
- Preserved full-default replays of 004, 005 v2 and the new parallel 008; these are finite checks, not external reviews of their infinite arguments. Updated the catalogue without overwriting parallel manuscripts or dirty shared worktree files.
- Complete v3 proof and certificate disclosure: `43bb307c76ec83d09feb2fe3aa74b2a40e3d2bdc`. Added a read-only, commit-pinned CI replay; no first-priority claim or new material license is made.

## 2026-10-07 — manuscript 001 version 4

- Added a focused 13-page continuation on sharp logarithmic second moments: full-Gaussian exponent min(1/3, beta/(beta+1)), the loss-free beta=1/2 transition, and the beta=0 no-uniform-modulus obstruction in dimension at least two.
- Established the exact order (q−2)^(-1/6) of the best finite-q Gaussian one-third constant for fixed dimension at least two, with exact normalized constant one in dimension one.
- Included the stated full-support strongly convex C1,1 source extension with globally Lipschitz gradient; no arbitrary hard-boundary extension or individual sharpness for every non-Gaussian source is claimed.
- Explicitly uses the complete public v3 all-P2 potential theorem at commit 5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3. The theorem is restated as a proof input, not independently re-proved. Version 3 retains the broader earlier results and full cell-calculus proof.
- Preserved all historical versions and unrelated entries. Added local build inputs, source archive, artifact checks, and a changed-file SHA-256 manifest. No formal verification, external peer review, or priority certification is claimed.

## 2026-10-07 — transport and quadratic version 3

- Manuscript 002: 26-page version 3 with arbitrary nonzero nonunit principal-generator certificates, exact quotient-component bounds, and selected-norm restoration.
- Added complete four-step/eight-step certificates for Z[i] and Z[sqrt(2)], with conservative full irreducible component bounds 20/92820 and 179200/351232, respectively. The failed Q30 Gaussian eight-step candidate is explicitly distinguished from the successful Q130 certificate.
- Added separate 41-test norm-prime and 24-test general-principal suites, independent lift/multiplication-image checks, and 184 arithmetic checks. These do not prove the general analytic theorem or certify optimality.
- Added a geometry-dimension literature comparison, distinguishing the full source sheet from compact witness assemblies and avoiding any claim that dimension two is minimal.
- Manuscript 001: 30-page v3, titled Sharp Brenier stability under target moment bounds; full-Gaussian q>2 sharp one-third map stability, the specified smooth full-support source extension, hard-boundary finite-q rate (q−2)/(3q−2), and the q=2 no-uniform-modulus obstruction. Sharpness and endpoint obstructions require dimension at least two; dimension one is isometric.
- Geometry remains v1. Every historical v1/v2 file and independent entry 004/005 is preserved byte-for-byte. Exact version-3 changed-file hashes are recorded in the release manifest; disclosure is determined by the commit that publishes them.


## 2026-10-07 — density and simplex-product additions, v1.1

- Added manuscript 004: logarithmic upper Banach density criterion, infinite hits in every affine copy, countable simultaneous avoidance, and effective finite rational-certificate search. Its complete written proof does not claim the unrestricted Erdos similarity conjecture.
- Added manuscript 005: exact simplex-product optimization in every dimension, unique optimal dimension multiset, sharp period-thirteen recurrence beginning at 100, and sharp dimension-mass stability with additive constant 112.
- First complete source disclosure: `e6c776cae39477baa4e1a03d59a1547417f1a68e`, 2026-10-07 01:00:08 UTC. The v1.1 numbering records revision of private drafts, not earlier publication.
- Remote workflow replayed seven strict rational inequalities, eighty finite no-tie checks, and exhaustive optimal-partition DP through 300; it also passed six exact cover-checker regression cases, including boundary-only obstructions. The similarity toy cover is not a computed small-measure witness for the full theorem.
- Both PDFs, verifier outputs, and SHA-256 records were built and committed at `e894ed8678052e45ecd9f1714b6a996cfea33cf3`. Versioned release: [density-simplex-20261007-v1.1](https://github.com/mxym/math/releases/tag/density-simplex-20261007-v1.1), published 2026-10-07 01:03:06 UTC. GitHub's immutable-release flag is not enabled; fixed content commits and hashes are recorded without claiming external archival certification.
- Added a [post-publication source comparison](comparisons/2026-10-07-density-simplex.md). No priority, external peer review, or proof-assistant certification is asserted.
- Preserved the pre-existing manuscripts 001--003 and their revision history. Added an elementary balanced-projector covering note, excluding only one Borsuk route.

## 2026-10-07 — post-publication literature comparison

- Added exact scope comparisons with primary transport and quadratic-walk papers, including earlier semi-discrete W2 one-third estimates and the partial indirect verification of Merigot’s quarter-power result.
- Recorded the v2 publication commit without changing the v1 or v2 manuscript bytes.

## 2026-10-07 — extensions release v2

- Manuscript 001: all-P2 centered potentials, absolutely continuous curve lifting, and exponential conditional-cell transport control. The map modulus remains bounded-target only.
- Manuscript 002: exact integer certificates, conservative computable component bounds, and a proof that finite-certificate search terminates. Small executable examples are included with explicitly limited scope.
- Manuscript 003 stays at v1 after a fresh correctness audit.
- All v1 manuscript files remain byte-for-byte unchanged. No priority or full formal-verification claim is added.

## 2026-10-07 — initial research release v1

- Added three complete manuscripts, each with PDF and editable source.
- Recorded upstream dependencies, verification scope, build instructions and file hashes.
- Preserved explicit distinctions between mathematical proof drafts, external peer review, machine formalization and novelty assessment.

Disclosure time is the timestamp of the Git commit that first adds this release, not the time at which a local draft was prepared.

## 2026-10-08 — complete five integrated manuscripts and strengthen reproduction

- Consolidated four near-complete research lines into five full papers with editable sources, 88 PDF pages, precise theorem scopes, classical inputs, formal coverage and source pins. Incorporated related parallel permanent/orbital work through the recorded integration snapshot.
- Added a continuous sharp-simplex proof with the quadratic coefficient and full truncation obstruction, and a self-contained standard-library polynomial certificate for all four infinite triple-action primal families. It checks complete Cramer identities and publishes every coefficient.
- Replayed 20 exact checkers, retained imported-helper assertions even under an optimized launcher, and rejected deliberately false/corrupted proof obligations. Recompiled the partial fractional Lean exports. Full fresh Lean replay status and its exact trust boundary are recorded separately.
- Repaired the sealed continuum verifier's cache-miss handling of Lean import-all syntax via a pinned external adapter; preserved historical proof sources and seals. No external peer-review, journal-submission or priority claim is added.

## 2026-10-08 — repair complete-cache-miss continuum reproduction

- Restore pinned Mathlib compilation options and recursively visit cached dependency imports in the sealed-verifier adapter. Use the separately pinned comment/string-aware scanner, with direct Lean parser controls. Preserve proof sources, original seals, artifact guards and kernel replay checks.
- Publish actual compiler-option diagnostics and aborted-run outputs, and rebuild all five PDFs. The still-running full Lean outcomes remain separately marked in the finalization status.

## 2026-10-08 — complete current simplex kernel audits and publish declaration graphs

- Rebuilt 123 upper and 125 lower modules from their sealed sources. Rechecked 848/850 public proofs and 1,833/1,849 owned declarations against their exact historical names, types, owners, kinds and axiom sets.
- Replayed every required declaration in empty trust-zero kernel environments: 55,066 upper and 55,162 lower declarations, plus 54,276 for the literal upper Main. Preserve the sealed harnesses' historical-count rejections and original reports; publish complete current graphs and an independently checked complete-root-closure continuation.
- Clarify that the lower main target is existential sharpness; all-maxima classification, best-maximum and free-translation Banach--Mazur assertions have separate full written proofs. Add a Chinese manuscript guide and correct a TeX separator.
- Complete the continuum cache union over every pinned package, retaining its actual cache-failure diagnostics. The continuum full replay remains in progress in the separately recorded status.

## 2026-10-08 — finish full continuum replay and close the five-paper audit

- Freshly rebuild all 65 owned continuum modules and 1,107 missing pinned external modules. All 568 public proofs and 1,454 owned declarations match the historical inventory; the complete declaration graph is identical.
- Pass the unchanged original empty-kernel checks at 34,923 endpoint-union and 35,620 all-safe declarations, the 1,322 defining-module source/artifact guards, the injected-axiom rejection, all 66 semantic/boundary controls, and 88 packaging-integrity cases in normal/optimized entry points.
- Publish complete current reports, graphs, source/object comparisons and all 1,249 raw logs. Mark all scoped full Lean replays complete, retaining earlier failures and the precise written-versus-formal proof boundaries. No external peer review or submission is represented as completed.

## 2026-10-08 — exact optimal 197 sieve and explicit conditional 197-prime reduction

- Published the [exact finite principal-ideal sieve optimum](notes/sqrt-minus-two-exact-sieve-optimum/README.md): a prior universal 197-point CRT obstruction and a matching explicit six-stage sieve prove M_sieve=197. The SHA256-pinned 204,800-point parent partition was refined by all 14-step connected-component and mixed-radix shifts for 19, 5, 41, 43, 59, 67 with an independent exact checker. The actual irreducible graph is proved only to lie in [90,197].
- Published the [conditional genuine prime-graph theorem](notes/sqrt-minus-two-conditional-prime-197/README.md): 197 distinct monic irreducible integral quadratics are explicitly produced, and their product's lack of a fixed prime divisor is rigorously verified. A single classical Schinzel-H prime-value instance would imply infinitely many size-197 actual prime components, hence B_D=197, **but H is unproved and the equality is not unconditional**. Both notes have mutation tests and full scope documentation; no historical-priority or external-human-referee assertion.

## 2026-10-08 — universal finite-sieve CRT minimax duality

- Established the [abstract exact minimax theorem](notes/periodic-sieve-admissibility-minimax/README.md) for arbitrary integer-lattice dimensions, finite symmetric graph steps and any local prime residue predicates, including finite attainment. The general theorem uses only CRT and finite rooted connected shapes, with no numerical solver. Proved the exact equivalence between finite norm-residue and finite principal-ideal sieves in Z[sqrt(-2)], so the previous **197** matching certificates are a sharp instance. The actual prime-only maximum remains only in **[90,197]** and is not claimed solved.
