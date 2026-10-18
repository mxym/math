# Share actual Pauli mask metadata across every stage

Only new successor files are added. The standard native/Boolean checkpoint and
all earlier sealed mathematical/configuration/audit inputs remain unchanged.

`preparePauliPlan` stores a mask's target, sorted parity wire list, CNOT prefix,
and inverse CNOT suffix. Nonempty masks compute their target/controls once,
construct the prefix once, and reverse/invert that stored prefix once. The
empty mask receives its exact distinct phase behavior. `preparedMaskTable`
prepares the entire finite table once. `preparedSelectedCode` computes the
half-angle once and visits stored plans, reading stored parity coordinates;
it never rebuilds masks, mask minima, control sorts, or the CNOT words.

The Pauli, selected phase, adjacent swap/rotation, Gray move/swap/rotation,
raw-gate and raw-word compilers are each proved literally word-equal to their
preceding versions. `preparedNativeOccupationRun` constructs one actual table
per active stage, shares it with all native branch compilation and all packed
swap-stack alignment, and constructs one native occupation table for both.
No interpreted Sym value is computed on this generation path.

The actual native stage/compression/descriptor programs preserve their entire
returned word/rank-work records. `preparedNativeBooleanExtractionRun` preserves
the complete preceding final result record: finite-label word, rank-event
fields and the separate online Boolean/provider-root fields. Thus the same
all-input original-register fidelity and degree338/degree18 partial numeric
annotation bounds hold internally.

A literal storage-cell metric on the prepared records counts stored CNOT-list
cells, parity-coordinate cells, one target and one flag per mask. This is at
most `(3*n+2)*2^n`. At actual active width `n=2+codeWires k`, it is at most
`352*(k+3)^4`; the sum of all stage context payloads is at most
`352*k*(k+3)^4`. These are actual stored metadata list sizes, not bit-size,
peak-space or constructor-runtime statements. Gate payload sharing/allocator
behavior is not inferred from them.

Remaining source costs: constructing/ranging/filtering/sorting these masks,
Nat bits and finite index data, endpoint lookups and function-update chains,
parity-fold/list-get fees, otherWires sorting, Gray differing-wire selection,
append/reverse/map/prefix/shift/cast operations, raw command and output-list
construction, annotation/control/cache costs, literal adapters and whole
provider/library evaluation. Previous event/Boolean/root models stay distinct.
This checkpoint reduces actual repeated work and proves a context-size bound;
it does not turn gate count or storage size into a whole runtime theorem.

Validation uses the standard worker runner on a new explicit full-root check.
The check also prints the actual sharing definitions and executes only tiny
n=2 table-length/payload and n=1 swap examples. No old umbrella is changed.
Independent successor-scope reconstruction remains separate.
