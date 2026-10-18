# Effective synthesis boundary

The committed theorem `finiteLibrary_extraction` proves mathematical existence
of literal finite-library/CNOT words, their gate counts, their operator error
up to global phase, and the fidelity of the same local-discard output. It
does not prove a classical algorithm or classical bit complexity.

The source manuscript's `prop:pure-circuit` explicitly assumes a fixed
**efficiently computable** inverse-closed universal one-qubit library. That
condition is stronger than the assumptions of the current Lean existence
theorem, which only requires finite inverse closure and subgroup density in
SU(2). A library satisfying those weaker mathematical conditions can contain
noncomputable matrix entries. The Lean theorem must therefore not be read as
a uniform effective algorithm for every library in its statement. Conversely,
the weaker assumptions of that theorem do not refute the manuscript's
stronger effective-library statement.

The unknown pure state is never an input to the synthesis algorithm. The
desired inputs are the integer copy count k, a dyadic error request, and the
fixed library description below. The occupation coefficients and the circuit
depend on k, not on unknown state amplitudes.

## Required concrete interfaces

1. **Bit model and precision request.** Use a deterministic Turing bit-cost
   model, with k in binary and an integer precision p in unary, requesting
   operator error at most 2^-p. A polynomial bound in k and p allows the
   output itself to have the proved polynomial size. Arithmetic operation
   counts on exact real numbers are not bit-cost bounds. An arbitrary real
   delta is a specification parameter; an algorithm must receive a finite
   request such as p, rather than exact-real equality or a real comparison
   oracle.
2. **Fixed gate library.** Supply a finite label table, an explicit inverse
   label table, and, for each matrix entry and integer b, a dyadic complex
   approximation with certified absolute error at most 2^-b, computable in
   polynomial time in b. The exact library gates remain unitary and inverse
   closed; dyadic matrices used by the classical algorithm need not be
   exactly unitary. A U(2) library needs a stated projective phase convention,
   or may be specified in SU(2) as in the present theorem. No exact equality
   test on arbitrary real entries is an allowed primitive.
3. **Input target description.** For generic SU(2) synthesis, give a certified
   entry-approximation oracle for the target and account for its cost. For
   this extraction task, replace that oracle by a proved evaluator for the
   actual one-qubit instructions of an explicit occupation compiler. An
   arbitrary matrix U with no effective presentation cannot be an algorithm
   input. The current universal quantifier over all SU(2) targets is an
   existence specification, not such an encoding.
4. **Occupation labels and permutations.** Give a concrete rank/unrank map
   for quadruples of nonnegative integers with sum j, and a deterministic
   complement-matching rule for the active-register permutation. Prove their
   bit costs and agreement with a parametrically specified extraction
   circuit. Current uses of `Fintype.equivFin`, `Finset.toList` under classical
   instances, and `embeddingPermutation` establish finite objects and their
   action, but do not supply a certified uniform evaluator with a cost.
   No algorithm should enumerate all 2^(2k) original basis strings: only the
   proved active-register dimension O(j^3) is available for that claim.
5. **Base net with slack.** For each fixed effective library, store a fixed
   finite table of instruction words and certified approximations of their
   matrices. Prove coverage at a radius strictly smaller than the base error
   budget. The positive slack permits selection by bounded-precision
   approximate distances without exact ties. Compactness currently proves
   that a finite net exists; `Classical.choose` does not implement the
   selector, certify its table, or bound the required numerical precision.
   A fixed precomputed table may be treated as a library-dependent constant,
   but that convention and its validity must be stated explicitly.
6. **Stable balanced decomposition.** Implement an approximate SU(2)
   commutator decomposition using rational threshold branches and prove its
   residual error and near-identity factor bounds. The present exact proof
   branches on U=V-adjoint and on a complex entry being zero, and normalizes
   a merely nonzero quaternion. That normalization can have an arbitrarily
   small denominator. Its proof of exact existence therefore does not give
   a uniform bit-cost bound. A numerical refinement must use conditioned
   alternative charts or certified tolerance branches; it must account for
   target rounding and propagate residual error through the actual SK word.
7. **Phase and elementary functions.** Specify certified dyadic sqrt,
   trigonometric/argument evaluation, and phase normalization routines with
   their precision and costs. The current U(2) phase representative uses a
   chosen complex square root, and `circleAngle` uses principal argument.
   Principal argument has a branch discontinuity, though the required
   rotation matrix is continuous in its circle coordinates. An evaluator
   may work directly with those coordinates or use a documented branch
   convention and a matrix-error guarantee.
8. **Whole recursion and output.** Prove a finite-precision recursive word
   algorithm, its termination, internal precision schedule, and total bit
   cost, including word copying/output, all matrix operations, net lookup,
   decomposition and target evaluation. Then relate its actual emitted word
   to the existing final circuit error/discard theorems. Replacing these
   obligations by a premise that directly supplies the final compiler and
   its claimed polynomial running time would leave the main claim open.

## Present arithmetic support and remaining claims

Actual occupation masses are integer counts divided by j. Every occupied
mass is at least 1/j, and accumulated nonempty masses are sums of those
integer counts over the same denominator. Thus an explicit occupation
compiler can decide zero branches from integers, and its Givens coefficients
are square roots of rational ratios of such integer sums. This structure
supports an effective refinement, but a bound for that refinement is not
the same as a completed finite-precision SK implementation.

The `noncomputable` keyword by itself does not prove mathematical
noncomputability: many current uses merely reflect the representation of
real or complex numbers in Lean. The missing obligation is an explicit
refinement to finite descriptions with a proved cost, including the actual
choices and numerical branches listed above.

The primary SK reference discussed in `SOURCE_REVIEW.md` excludes
finite-precision arithmetic costs from its stated classical analysis. The
present proof independently establishes conservative logarithmic exponent
5 for **gate count**. It does not establish a corresponding classical
bit-complexity exponent. The safe manuscript endpoint is the proved finite
gate count and error, with classical bit complexity explicitly left open
unless these additional obligations are completed.

`RationalSelection.lean` now supplies one small constructive component: a
finite rational argmin without classical choice, together with the error
bound rho+2*eta when the score errors are at most eta and a table entry is
within rho. This removes a need for exact real tie tests in the selector.
It neither constructs the fixed net nor evaluates matrix distances, and
does not discharge those interfaces or the full bit-complexity claim.

Further constructive components are now proved. `ConditionedConjugacy.lean`
replaces an unconditioned conjugacy choice by four explicit quaternion
charts with a quantitative denominator bound after rational score selection.
The scalar oracle arithmetic and integer-square-root routines are explicit
finite rational programs with proved error schedules. The half-angle
programs compute the actual occupation merge-angle circle coordinates after
dyadic scaling, with no target-state oracle, exactly n+1 integer-square-root
calls, 2*n rational arithmetic nodes, bounded dyadic output numerators, and
maximum requested precision polynomial in the actual active dimension and p.
They avoid using an exact-real `arg` operation as a computational primitive.

The full numerical SK recursion has not yet been implemented with composed
entry oracles, stopping thresholds, fixed-net score evaluation and stable
factor-oracle propagation. The angle routines have also not yet been
attached to every instruction of an explicit rank/unrank extraction
compiler. Counting rational arithmetic nodes and integer-square-root calls
does not bound their Turing bit cost without bit-size and machine-algorithm
analysis. These remain separate obligations.
