# Operational finite-stack bridge for concrete list backends

Four new mathematical modules implement concrete programs in the pinned
Mathlib Turing.TM2 model and prove runs of its official step function.
They do not just attach another numerical fee field to the source evaluator.

The append machine uses three stacks, two program labels and an optional
alphabet symbol as local memory. It moves the left input onto the work
stack, then moves the work stack onto the right input. Each label contains
at most four TM2 statement constructors on any branch. For an alphabet of
size a, there are exactly 2*(a+1) non-halting label/local-memory combinations.
There are no Nat registers, arithmetic operations or runtime fuel values
in these programs. The Nat index of the iteration theorem is external time.

Theorem/definition endpoints in namespace CircuitRecursion.ListAssemblyMachine:

- appendRun is StateTransition.EvalsToInTime of the official TM2.step with
  exactly 2*left.length+2 transitions, a proved terminal state, and right
  output equal to the existing actual listAppendProgram result.
- reverseRun implements reverse-map into an accumulator in exactly
  left.length+1 TM2 transitions. instructionInverseRun specializes to the
  fixed finite inverse-label table on Fin m, m>0.
- Their transition counts are at most twice, respectively once, the
  previously proved source list-spine fees. Correctness, stopping and the
  time bounds are derived internally for all input lists.
- evalsTo_reaches and evalsTo_terminal_mem_eval connect these proved bounded
  iterations to official StateTransition.Reaches and StateTransition.eval.
  append_mem_eval and reverse_mem_eval establish the actual final results.
- program_supports/reverseProgram_supports prove finite label support;
  stack/label/control cardinality and static statement-depth theorems make
  the finite-state restrictions explicit.

The semantic proofs are alphabet-polymorphic; the physical finite-machine
claim requires a finite alphabet. Bool and the actual fixed instruction
alphabet Fin m meet that condition. An arbitrary structured AST, packet or
trace object cannot be counted as one finite alphabet symbol. Their encoded
representations, payload movement and allocation need separate simulation.
The reverse-map callback is a fixed finite transition table in this machine,
not an unbounded external provider procedure charged as one operation.

This is an operational implementation of concrete backends, not a completed
lowering of assembledInputCachedRun or the entire compiler. A full machine
bound still needs composition/control-stack and AST/closure encodings, all
Nat/precision/index/fuel paths, actual provider and cache construction,
structured payload allocation, and annotation-erasure or execution costs.
No whole-compiler338 TM2 or Turing-time theorem is claimed. In particular,
no existing source-size bound is silently identified with machine runtime.

The official StackTuringMachine dependencies were first built through the
standard worker_build.py global-lock/storage guard. The first author target
failed on local deriving/reserved-name issues; that original log is kept.
The corrected new modules have separate OWNED feedback. A later independent
scope must still fresh-build and replay these new sources; earlier frozen
core/resource scopes do not cover them automatically. All prior numerical
and b288 circuit sources remain byte exact.
