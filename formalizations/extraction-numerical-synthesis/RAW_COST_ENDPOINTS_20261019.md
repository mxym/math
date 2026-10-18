# Raw packet AST operations and partial root-charge interface

Two modules extend checkpoint `830929eb37b66c06965d7389161a037040c06b12`.
Every earlier source, root list, check and report is preserved byte for byte.

Raw packet embedding has 20 AST operations, whereas literal packet input has
1. `RawOperationRecursion` rederives the full word and two-correction AST
operation recurrence with this actual raw input bound. Word evaluation costs
at most `68*wordLength+1`. `RawOperationGrowth` proves its offset is bounded
by the earlier recurrence with `2*L`; consequently the depth-clog actual raw
trace has at most
`1020*(n+1)*(2*L+1)*offsetGrowth*(p+1)^64` AST operations.
The raw-provider convenience theorem applies directly to
`rawPacketExpressionOracle` inputs and the memoized `costedTracedPairWord`.

`costedTracedPairWord_twenty_rootCharge` combines this actual raw AST bound,
the explicit flat raw input integer budget, and the previously proved
memoized evaluator bridge. It derives the resulting partial root charge;
no final polynomial-cost or correctness certificate is a caller assumption.
The sibling actual extraction compiler owns its raw cached providers and
the internally derived degree137 budget, so it can specialize these generic
interfaces without adding opaque provider-height premises.

The degree64 theorem here concerns AST operations. The root charge is an
annotation for the underlying value evaluation in the new memoized program.
Computing the annotation itself is not charged: in particular the older
root-charge helper recomputes a division to determine its square-root fuel.
Thus the entire value-plus-counter program is not claimed to have this total
execution count. A stronger implementation can share the quotient and return
value/charge together; that is a separate successor obligation.

Full machine bit time remains open. Ordinary integer arithmetic, automatic
fuel, AST construction, list/vector allocation and indexing, cache creation,
gate description work, and target/library provider execution still need
explicit accounting. Correct dyadic outputs and bounded bit lengths do not
imply a polynomial-time provider. An eventual total cost theorem must retain
an explicit fixed-library provider execution-cost contract or prove its
specified algorithm efficient. No specific algebraic universal library or
general Turing-machine simulator is introduced by this extension.
