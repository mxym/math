# Independent full Lean audit: prescribed-family continuum power remainders

7 October 2026

Public-copy derivative: original findings retained; private transport identifiers removed, package paths updated, and the release documentation correction marked implemented. Original report digest is recorded in provenance/INPUT_ARCHIVE.json. Paths below are relative to the package root.

## Verdict

**PASS for the stronger mathematical theorem and its compact corollary.**
No unresolved mathematical construction premise, wrong quantifier order,
vacuous configuration hypothesis, altered real/measure/topology semantics,
nonstandard axiom, or proof escape was found.

**Historical documentation/evidence correction, implemented in this public copy.** The submitted README describes its import-only `submitted-evidence/KernelReplay.lean`
as an empty trust-level-zero imported-closure replay. That file contains only
`import ContinuumRemainder.FinalProof`. It does not construct a new empty kernel
environment or replay the stored declarations. Its successful `--trust=0`
import and empty log do not establish the explicit proof-closure replay claimed.
The original submission remains unchanged; public evidence copies redact local machine paths only, with original and derivative hashes recorded in provenance/PUBLIC_DERIVATIVE_LEDGER.json. This audit supplies actual
independent empty-environment replay, and does not retroactively validate the
author's description of the earlier import-only check. The public README and provenance documentation correct that attribution; the original submitted evidence remains identified as historical. No mathematical source correction is requested.

This is independent AI/model semantic review and Lean kernel verification, not
external human peer review or novelty/priority certification. Standard trust in
the official Lean implementation and the interpretation of ordinary mathlib
real-number definitions remains.

## 1. Exact theorem certified

For a **fixed prescribed nonempty countable family** `(A_l)` of subsets of the
positive real numbers, assume that for each family member there are positive
integers `G,J` such that every block of `G` dyadic bins from `J` onward contains
a point of that member. The bins are exactly `(2^(-i-1),2^(-i)]`. No
measurability or countability hypothesis is imposed on the individual `A_l`.

For every `0 < epsilon < 1`, there exists **one** closed nowhere-dense,
one-periodic set `E` such that its genuine Lebesgue measure in every shifted
closed unit interval is strictly greater than `1-epsilon`. After `E` is chosen,
the theorem simultaneously quantifies:

- every member of the prescribed family;
- every real `s>0` and `alpha>0`;
- every real center `y` and nonzero real coefficient `c`;
- every finite real `M>=0`;
- every arbitrary function satisfying
  `|f(a)-y-c*a^s| <= M*a^(s+alpha)` eventually on that family member.

For **every positive input-tail radius**, infinitely many **distinct real
output values** from that tail lie outside `E`. This is a set-of-values
`Infinite` assertion, not an assertion merely about infinitely many indices or
inputs. No regularity, continuity, or measurability of `f` is presumed.

The main formal endpoint is the closed theorem
`ContinuumRemainder.continuum_power_target : ContinuumPowerTarget`.
`robustCompactBlockerSpec_proved` discharges the construction specification
unconditionally. `compact_power_avoidance` gives a compact nowhere-dense subset
of `[0,1]`, of measure strictly greater than `1-epsilon`, with the same avoidance
property. The compact corollary does not assert periodicity.

The formal endpoint uses total real functions. A separate independently
compiled theorem, `IndependentSemanticReview.fully_partial_eventual_target`,
extends the result to functions genuinely defined only on a positive tail,
with an error bound that holds only eventually within that domain, and every
positive requested radius. Taking minima of the requested radius, domain
radius, and eventual-bound radius proves the precise partial formulation.

`audit/checks/ExactMain.lean` applies the main theorem in an empty context, expanding every
project-specific target predicate, including the dyadic-bin condition. Its
fully printed expressions use the standard `Real` arithmetic/topology and
`Real.measureSpace` Lebesgue volume. Independent interval-volume identities
compile, including volume(`[0,1]`)=1. A countable set of configurations is
represented by its countable subtype, so the indexed-family formulation
covers the ordinary prescribed-family wording.

## 2. Exact input and immutable source provenance

- Filename: `prescribed-family-continuum-remainder-lean.zip`.
- Exact size: **1,875,200 bytes**.
- Archive SHA-256:
  `b8fb480b8888321b864cf3c58a81cad3dfc223cc837071b940be58a93cca0e51`.
- Source-freeze SHA-256:
  `48841d7974245af1cf7de677580ecec934ed6310bbbb21f2456cbe6b77081e71`.
- Submitted manifest SHA-256:
  `521428348fb113864c6af3d010156ca18f91d97bdc9fac4bdadaf6da2af01fa4`.
- FinalProof.lean SHA-256:
  `f54bc7886852aaf0a36a537556bbe92d193eb49944863f36f87bcd05c122f912`.
- Specification.lean SHA-256:
  `0a98b8858428b1cd7c34263358c67a769121d049ae964008bd91abcd1382102e`.

The exact received archive bytes were verified before extraction. Archive extraction rejected absolute,
traversing, and symlink entries. All 228 manifest entries match; the 229-file
extracted inventory is exact. All 18 new frozen sources match. All 45 inherited
geometric modules are byte-identical to the independently audited version-3
archive, SHA-256
`747386b02dbd12ae6f7b763d79fdb1e9bd70ca1e195e1b84d943cb0bcff82cb5`.
No submitted file was edited. The input archive digest and original submitted manifest are retained in this public package.

## 3. Independent clean rebuilds and dependency boundaries

Official Lean **4.34.1**, commit
`5045d0056413266e57c625dcd7c365b10e377c52`; executable SHA-256
`e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
Mathlib is pinned to `d13f23b723b8a846827a245b89c10fc7d3f11612`.
All nine package revisions match the lockfile and tracked source trees are
clean. Package pins are recorded in `audit/independent/pins.json`.

All **65 owned modules** were rebuilt from source into initially empty
independent output directories, once under normal Python and once under
Python `-O`. This includes all 45 geometric modules, all 18 new remainder
modules, and both aggregate import modules. All **65 resulting olean files**
and **65 compiler logs** are byte-identical across modes. No submitted or
previously built owned olean was used.

Pinned dependency caches were reused read-only. All **43,783 dependency
symlink targets** were resolved and checked. The one missing official Floor
module was compiled into this audit's own overlay. No multi-gigabyte dependency
copy, shared-cache write, or edit to the prior audit was performed. This does
not claim a source rebuild of all mathlib; actual stored proof terms in the
complete safe-owned dependency closure were independently kernel-rechecked.

## 4. Declaration ownership, graph, standard axioms, and actual replay

Ownership is determined by Lean's actual defining-module index, not a
namespace-prefix filter. The resulting inventory contains **1,454 owned
declarations**:

- 1,114 theorem/helper declarations;
- 320 definitions;
- 6 inductives, 8 constructors, and 6 recursors.

The independently parsed public source inventory contains **568 theorems**,
including all 114 new public theorems. Every public theorem's printed axiom
list is checked, including the five with no axioms at all. It agrees with the
module-owned collector and raw graph traversal. The only possible axiom
dependencies are `propext`, `Classical.choice`, and `Quot.sound`.

Twenty-five private/generated names outside the visible project namespace
prefixes remain included by module ownership. An isolated deliberately
injected global target axiom is rejected by the **actual production guard**
after only adding its module to the imports and owned-module list. The adversary
never enters the proof build.

There are nine inherited compiler-generated partial `*_unsafe_rec` helpers.
No source `unsafe` or `partial` declaration occurs. None of those nine helpers
appears in the stored type/value closure of **any** of the **1,445 safe owned
declarations**. They are recorded explicitly rather than hidden or silently
ignored. No `sorryAx`, new axiom, `native_decide`, custom elaborator, or other
source proof escape was found.

The complete safe-owned graph has **35,620 declarations** and **1,322 actual
defining modules**. Each node records separate type/value/all-constant edges
and defining module. Source and loaded olean/private/server artifact hashes
are recorded for each defining module. Independent Lean/Python traversals and
printed/collected/raw axiom checks agree.

The main theorem alone has **34,919 declarations** in its proof closure,
including **897 owned declarations** and 388 public source theorem roots.
It is literally a theorem with empty universe-parameter list and exact type
`ContinuumPowerTarget`, with no context parameters or construction premises.

Two actual independent replay probes go beyond import checking:

1. `audit/checks/ReplayClosure.lean` gathers the main, compact, and unconditional blocker
   roots together, adds required inductive companions, creates
   `mkEmptyEnvironment 0`, and replays all **34,923 declarations** through the
   official kernel. It verifies that all three endpoint types and universe
   parameters remain unchanged. **PASS**.
2. `audit/checks/ReplayAllSafeOwned.lean` selects **all 1,445 safe roots by defining-module
   ownership**, gathers their full closure, and performs the same fresh empty
   trust-level-zero replay for **all 35,620 declarations**. **PASS**.

These actual replay programs and logs are separate from the preserved
import-only author file. An initial audit-only generated-name quotation
fixture error in the optional all-safe probe was corrected by selecting actual
`Name` objects directly from the environment; no submitted source was changed.
The final all-safe probe compiles and replays cleanly.

## 5. Semantic construction review

`audit/independent/SEMANTIC_REVIEW.md` gives a detailed independent review with
precise source line references. All 18 new modules, totaling 2,780 lines, the
written proof, and the relevant inherited interfaces were read.

The critical connections are genuinely proved:

- Logarithmic syndeticity selects actual positive inputs in `A`, with controlled
  real logarithmic gaps and convergence to zero. Arbitrarily late open output
  windows have enough active inputs uniformly on compact real exponent ranges.
- Both activation endpoints are strict. Finite candidates retain absolute
  position factors. Exact keys, boundary strata and sign representatives give
  matching local readouts for every table assignment.
- Fixed-parameter own-bit freedom, distinct terminal addresses, and the finite
  joint law feed the actual continuum miss bound. Shared auxiliary reads and
  zero-mass atoms do not cause illicit independence or division assumptions.
- The schedule chooses structural parameters before the late position, retains
  the absolute-position entropy factor, and pays the actual `4*N*r` buffer cost
  with `N=2^(U+T+2)` and a strictly positive radius.
- Two open buffers absorb errors satisfying the **closed** bound `|error|<=r`,
  including equality. Closed missed-center projections and finite averaging
  select one actual outcome. The exceptional-center cover plus convergence of
  the **full perturbed sequence** repairs every real center.
- The unconditional blocker proof closes every intermediate construction
  specification. Countable exhaustion enumerates only family/compact-range/
  magnitude/tail bounds `(l,N,j,k,q,h)`, never real exponents, arbitrary functions,
  translations, or error families. Reflection covers negative coefficients.
- The common open union has a strict summable measure budget. Its closed
  complement is periodic with empty interior and the required shifted-unit
  density. The nonzero leading coefficient keeps sufficiently small image
  values different from the center while forcing convergence toward it, which
  yields infinitely many distinct missed values in every input tail.

The written theorem's “sufficiently small rho” wording and the formal total-map
“every rho>0” wording agree through tail inclusion; the independent partial-map
probe confirms the fully explicit domain formulation. Positive exponent,
positive remainder rate, nonzero coefficient, fixed countable family, bounded
log gaps, and strict measure slack remain real hypotheses.

## 6. Controls and nonvacuity

All **28 submitted positive probes** compile: 21 frozen-base probes and 7 new
probes including the expanded target. All **28 submitted deliberately false
controls** fail for the intended mathematical diagnostic: 22 base controls and
6 new controls. Normal and Python `-O` reports and log hashes are identical.
No unknown-import, unknown-identifier, or syntax failure is counted as a
mathematical rejection.

Independent semantic probes construct a concrete discrete dyadic configuration
with `G=J=1`, a nonempty Unit-indexed family, and a positive-measure result.
They also prove the genuinely partial/eventual-domain target described above.

Additional independent controls in `audit/controls/independent/`:

- instantiate the full final theorem with `f(a)=7-2*a^(1/2)+a^(5/6)`, using a
  negative coefficient, fractional real powers, positive alpha=1/3, and a
  nonzero remainder; also instantiate the compact corollary;
- prove actual constant-function counterexamples when `c!=0`, `alpha>0`, or
  `s>0` is dropped, using the genuine `PowerRemainderOn` and output-value sets;
- test empty/finite configurations, inactive equality endpoints, exact dyadic
  half-open bins, doubled open buffers, and prerequisites for error domination;
- prove in Lean that **every positive-measure E admits a positive logarithmically
  syndetic adaptive configuration that defeats its avoidance property**.
  The proof uses the standard Lebesgue density theorem, shows every sufficiently
  small right dyadic shell is occupied, and uses `f(a)=y+a` with image contained
  in E. Consequently reversing family-before-E quantifiers is mathematically
  impossible, including for large closed nowhere-dense periodic E.

The hostile review adds **33 independently proved theorems in 4 positive
modules**, **6 deliberately false fixtures**, and **15 exact Fraction
regressions**. Both Python modes give byte-identical reports and all 10 logs.
Its own report records exact fixtures, counts, logs, and hashes. These are independent checks rather than
substitutes for the universal theorem.

## 7. Scope and release boundary

An accurately scoped claim is:

> The prescribed-countable-family, all-real leading-power, power-controlled
> nonlinear-remainder avoidance theorem is proved by a closed Lean theorem,
> independently rebuilt, checked by complete safe-owned empty-kernel replay,
> and subjected to an independent model-based semantic and hostile audit.

The assertion is an existence theorem; enormous finite constructions and
classical choices do not provide a practical numerical realization of E.
This audit does not certify arbitrary slow remainders, all C1/flat germs,
merely positive upper Banach logarithmic density, or one E for all possible
configuration families. Novelty, priority, and human peer review are separate.

Mathematical blockers: **none**.
Public-copy evidence correction: **implemented**, as described in the root README and PROVENANCE.md.
This describes the independent audit stage. Publication is a separate action.
