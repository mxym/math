import EffectiveEncoding.PackedZipperMove
import EffectiveEncoding.ZipperMoveEvaluation

open Lean Elab Command
namespace EffectiveEncodingZipperMoveVerification

def checkKinds (theorems models : List Name) : CommandElabM Unit := do
  let env ← getEnv
  for n in theorems do
    let some ci := env.find? n | throwError "Missing theorem {n}"
    unless ci.isTheorem do throwError "Expected theorem declaration {n}"
  for n in models do
    let some ci := env.find? n | throwError "Missing model {n}"
    match ci with
    | .defnInfo _ => pure ()
    | .inductInfo _ => pure ()
    | _ => throwError "Expected definition or inductive {n}"
  logInfo m!"OWNED_KIND_CHECK_PASS {theorems.length} theorems; {models.length} models"

end EffectiveEncodingZipperMoveVerification

run_cmd (EffectiveEncodingZipperMoveVerification.checkKinds [
  ``EffectiveEncoding.zipperPackedUpdateProgram_bits,
  ``EffectiveEncoding.zipperPackedUpdateProgram_set,
  ``EffectiveEncoding.zipperPackedUpdateProgram_unpack,
  ``EffectiveEncoding.zipperPackedUpdateProgram_actions,
  ``EffectiveEncoding.skipFirstMoveSpecification_seen,
  ``EffectiveEncoding.skipFirstMoveSpecification_scan,
  ``EffectiveEncoding.skipFirstMoveSpecification_packed,
  ``EffectiveEncoding.zipperPackedAssemblyProgram_bits,
  ``EffectiveEncoding.zipperPackedAssemblyProgram_actions,
  ``EffectiveEncoding.finishZipperMoveProgram_actions,
  ``EffectiveEncoding.zipperPreparedMoveProgram_actions,
  ``EffectiveEncoding.packedZipper_head_value,
  ``EffectiveEncoding.zipperPreparedMoveProgram_word,
  ``EffectiveEncoding.finRange_values_range',
  ``EffectiveEncoding.retainedPackedZipperMoveProgram_word,
  ``EffectiveEncoding.retainedPackedZipperMoveProgram_actions
] [
  ``EffectiveEncoding.ZipperPackedUpdateResult,
  ``EffectiveEncoding.zipperPackedUpdateProgram,
  ``EffectiveEncoding.ZipperPackedUpdateResult.actions,
  ``EffectiveEncoding.skipFirstMoveSpecification,
  ``EffectiveEncoding.zipperPackedAssemblyProgram,
  ``EffectiveEncoding.ZipperMoveTrace,
  ``EffectiveEncoding.ZipperMoveTrace.actions,
  ``EffectiveEncoding.ZipperMoveResult,
  ``EffectiveEncoding.finishZipperMoveProgram,
  ``EffectiveEncoding.zipperPreparedMoveProgram,
  ``EffectiveEncoding.ZipperMoveResult.actions,
  ``EffectiveEncoding.PackedZipperMoveResult,
  ``EffectiveEncoding.retainedPackedZipperMoveProgram
])

#check EffectiveEncoding.zipperPackedUpdateProgram_bits
#print axioms EffectiveEncoding.zipperPackedUpdateProgram_bits
#check EffectiveEncoding.zipperPackedUpdateProgram_set
#print axioms EffectiveEncoding.zipperPackedUpdateProgram_set
#check EffectiveEncoding.zipperPackedUpdateProgram_unpack
#print axioms EffectiveEncoding.zipperPackedUpdateProgram_unpack
#check EffectiveEncoding.zipperPackedUpdateProgram_actions
#print axioms EffectiveEncoding.zipperPackedUpdateProgram_actions
#check EffectiveEncoding.skipFirstMoveSpecification_seen
#print axioms EffectiveEncoding.skipFirstMoveSpecification_seen
#check EffectiveEncoding.skipFirstMoveSpecification_scan
#print axioms EffectiveEncoding.skipFirstMoveSpecification_scan
#check EffectiveEncoding.skipFirstMoveSpecification_packed
#print axioms EffectiveEncoding.skipFirstMoveSpecification_packed
#check EffectiveEncoding.zipperPackedAssemblyProgram_bits
#print axioms EffectiveEncoding.zipperPackedAssemblyProgram_bits
#check EffectiveEncoding.zipperPackedAssemblyProgram_actions
#print axioms EffectiveEncoding.zipperPackedAssemblyProgram_actions
#check EffectiveEncoding.finishZipperMoveProgram_actions
#print axioms EffectiveEncoding.finishZipperMoveProgram_actions
#check EffectiveEncoding.zipperPreparedMoveProgram_actions
#print axioms EffectiveEncoding.zipperPreparedMoveProgram_actions
#check EffectiveEncoding.packedZipper_head_value
#print axioms EffectiveEncoding.packedZipper_head_value
#check EffectiveEncoding.zipperPreparedMoveProgram_word
#print axioms EffectiveEncoding.zipperPreparedMoveProgram_word
#check EffectiveEncoding.finRange_values_range'
#print axioms EffectiveEncoding.finRange_values_range'
#check EffectiveEncoding.retainedPackedZipperMoveProgram_word
#print axioms EffectiveEncoding.retainedPackedZipperMoveProgram_word
#check EffectiveEncoding.retainedPackedZipperMoveProgram_actions
#print axioms EffectiveEncoding.retainedPackedZipperMoveProgram_actions
#check EffectiveEncoding.ZipperPackedUpdateResult
#print axioms EffectiveEncoding.ZipperPackedUpdateResult
#check EffectiveEncoding.zipperPackedUpdateProgram
#print axioms EffectiveEncoding.zipperPackedUpdateProgram
#check EffectiveEncoding.ZipperPackedUpdateResult.actions
#print axioms EffectiveEncoding.ZipperPackedUpdateResult.actions
#check EffectiveEncoding.skipFirstMoveSpecification
#print axioms EffectiveEncoding.skipFirstMoveSpecification
#check EffectiveEncoding.zipperPackedAssemblyProgram
#print axioms EffectiveEncoding.zipperPackedAssemblyProgram
#check EffectiveEncoding.ZipperMoveTrace
#print axioms EffectiveEncoding.ZipperMoveTrace
#check EffectiveEncoding.ZipperMoveTrace.actions
#print axioms EffectiveEncoding.ZipperMoveTrace.actions
#check EffectiveEncoding.ZipperMoveResult
#print axioms EffectiveEncoding.ZipperMoveResult
#check EffectiveEncoding.finishZipperMoveProgram
#print axioms EffectiveEncoding.finishZipperMoveProgram
#check EffectiveEncoding.zipperPreparedMoveProgram
#print axioms EffectiveEncoding.zipperPreparedMoveProgram
#check EffectiveEncoding.ZipperMoveResult.actions
#print axioms EffectiveEncoding.ZipperMoveResult.actions
#check EffectiveEncoding.PackedZipperMoveResult
#print axioms EffectiveEncoding.PackedZipperMoveResult
#check EffectiveEncoding.retainedPackedZipperMoveProgram
#print axioms EffectiveEncoding.retainedPackedZipperMoveProgram
