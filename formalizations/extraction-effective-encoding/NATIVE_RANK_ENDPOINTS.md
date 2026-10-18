# Native occupation generation: runtime data and exact word transport

This checkpoint adds new files only. Its runtime occupation representation is
`NativeOccupation k = {t : Nat*Nat*Nat // total t <= k}`: three native integers
and an erased proof. `nativeOccupationValue` is a semantic interpretation,
which occurs in correctness statements and erased subtype/type/proof positions.
No runtime generation path below constructs the interpreted Sym/Multiset value.

Actual call graph and evaluation strategy:

1. `nativeOccupationTable` runs `triplesBuild` once, and maps its retained valid
   triples to native records. There is no literal multiset construction.
2. `nativeMass` dispatches on a Fin4 letter and reads one retained coordinate or
   `k-total triple`. `nativeSelected` filters Fin4.univ by these native positivity
   checks. `nativeOccupiedPivot` takes that finite set's minimum.
3. `nativeBranchRun` explicitly supplies `nativeOccupiedFintype` to the indexed
   branch compiler. Its actual `elems` field is the native selected set's attach
   mapped to subtype values with erased proofs. It does not use the default
   occupied-subtype instance, semantic membership tests, or a semantic literal.
   Linear order/equality are inherited from the native Fin4 underlying values.
4. `nativeBranchEndpoint` adjusts the stored triple by one coordinate subtraction
   and passes it directly to `carriedEncodedEndpoint` / `carriedTripleRankProgram`.
   The semantic erase is proof-only. `nativeNextEndpoint` passes the retained
   triple unchanged. Rank builds/scans the finite integer triple table, stores
   its actual returned record, then constructs its finite binary vector.
5. Branch pivot/other endpoint and mass records are stored once by the indexed
   compiler. `nativeAlignmentRun` uses one source/target record per step and an
   explicit finite packed swap stack. Both traversals share the native stage
   table. Recursive compression stores previous/stage records once.
6. `nativeRankExtractionRun` consumes the stored descriptor word, computes its
   precision, and runs the existing actual charged raw target provider plus
   shared integer online compiler to form finite labels. It preserves the actual
   returned rank annotations from the same descriptor generation run.

Internal exact correctness:

- native selected set equals the old semantic occupation's toFinset;
- native pivot equals the old pivot;
- explicit native Fintype contents are complete, and instance uniqueness is used
  only to prove compatibility with the old sorted branch compiler;
- branch, alignment, stages, compression, descriptors and the final compiler
  preserve entire preceding result records, including word and rank annotations;
- the finite-label word is exactly the preceding complete word and inherits its
  all-input original-register Bell/discard fidelity theorem.

The same returned rank-event bounds hold: construction/filter/Nat-equality
annotations are at most 168/6/18 times `k*(k+2)^6`. This version removes runtime
literal occupation construction, Multiset membership/count/erase, and repeated
conversion from literal occupations to rank triples. It does not charge the
remaining operations by replacing them with opaque input fees.

Remaining boundary: explicit native selector/filter/map/min/sort and Nat costs,
triples and other list construction outside the inherited annotations, rank
binary coordinate access, packed vector construction/equality, Gray/swap and
word-list compilation, prefix/shift/cast wiring, recursion/control, annotations'
own arithmetic/storage, provider conversions/cache structure, serialization and
fixed-library provider execution still need their appropriate operational costs.
The partial provider/root and rank-event models are not full primitive time or
Turing bit time. The library provider remains an explicit input contract.

Validation is author OWNED-only, pending standard aggregate/independent replay.
All four mathematical modules and every new theorem/model root are checked.
`NativeSelectionEvaluation.lean` additionally prints the actual bodies (including
explicit native Fintype argument) and executes only tiny selector/pivot/table and
single-letter branch examples. This is a source/evaluation sanity check, not a
large extraction runtime experiment or an independent proof audit.
