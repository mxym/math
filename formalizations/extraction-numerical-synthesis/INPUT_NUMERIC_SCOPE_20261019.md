# Numerical execution and cache reads of one input-reference program

Three new modules bound the actual numerical Boolean trace retained by
inputCachedRun, the same program that retains each concrete gate/precision
list-cache access. Each scalar evaluation is internally related to its
resolved native evaluation. Tuple values and selector scores are stored
once, only the chosen branches execute, and actual minimum/comparison
records have bounds derived from the represented operands. The proof-side
nativeView only projects retained records; it is not program re-execution.

The program's expression budget and operation count are internally derived
through the existing structural refinement. No output-word equality is used
to infer an execution bound. No final budget, final correctness, query count
or polynomial charge certificate is assumed as a new external hypothesis.

Let Q=p+1, m be the fixed number of gate labels, n+1 the fixed table size,
and L bound its word lengths. If every gate and target provider packet at
the finitely requested cache precisions has decoded integer height at most
A*Q^9, define

C = 1000000000002*(n+1)*(8*A+10)*(L+1)*traceRGrowth,
O = 1020*(n+1)*(2*L+1)*offsetGrowth.

The actual numerical Boolean fee is bounded by
40000*(40*C+4)^2*(20*O)*Q^338. The actual online cache list-spine fee was
already bounded by 80*(m+51200000*(L+1)+5)*O*Q^73. Their sum for this one
actual retained execution is bounded by the sum of those two coefficients
times Q^338. Finite provider output-height hypotheses are data-size bounds,
not provider running-time hypotheses. Canonical binary input packets are
consumed directly: no Nat.bits or rational decode/re-encoding runs in the
value evaluator. Resolution/interpretation are proof semantics only.

The existing final-word, length and approximation theorems for this same
inputCachedRun remain the semantic endpoint. This partial source-cost model
charges numerical Boolean primitives and the actual traversed cache list
spines. Provider execution and eager cache construction, AST and other list
construction/allocation, general precision/control/index/counter arithmetic,
and evaluation of the cost annotations are separate. This is not a proof
of full compiler machine bit-time.

All previous committed numerical files and the frozen b288 circuit prefix
remain byte exact. OWNED feedback and standard guarded aggregate checks are
not independent fresh/trust-zero evidence; prior scopes do not cover these
successors automatically.
