import EffectiveEncoding.CountedDescriptorFields

open Lean Elab Command
namespace EffectiveEncodingCountedFieldsVerification

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

end EffectiveEncodingCountedFieldsVerification

run_cmd (EffectiveEncodingCountedFieldsVerification.checkKinds [
  ``EffectiveEncoding.countedAngleFields_erase,
  ``EffectiveEncoding.countedSingleFields_erase,
  ``EffectiveEncoding.countedGateFields_erase,
  ``EffectiveEncoding.countedWordFields_erase,
  ``EffectiveEncoding.countedProgramFields_erase,
  ``EffectiveEncoding.countedAngleFields_steps,
  ``EffectiveEncoding.countedSingleFields_steps,
  ``EffectiveEncoding.countedGateFields_steps,
  ``EffectiveEncoding.countedWordFields_steps,
  ``EffectiveEncoding.extractionCode_countedFields_roundtrip,
  ``EffectiveEncoding.extractionCode_countedFields_steps,
  ``EffectiveEncoding.extractionCode_countedFields_steps_polynomial
] [
  ``EffectiveEncoding.FieldRun,
  ``EffectiveEncoding.FieldRun.empty,
  ``EffectiveEncoding.FieldRun.emit,
  ``EffectiveEncoding.FieldRun.append,
  ``EffectiveEncoding.countedAngleFields,
  ``EffectiveEncoding.countedSingleFields,
  ``EffectiveEncoding.countedGateFields,
  ``EffectiveEncoding.countedWordFields,
  ``EffectiveEncoding.countedProgramFields
])

#check EffectiveEncoding.countedAngleFields_erase
#print axioms EffectiveEncoding.countedAngleFields_erase
#check EffectiveEncoding.countedSingleFields_erase
#print axioms EffectiveEncoding.countedSingleFields_erase
#check EffectiveEncoding.countedGateFields_erase
#print axioms EffectiveEncoding.countedGateFields_erase
#check EffectiveEncoding.countedWordFields_erase
#print axioms EffectiveEncoding.countedWordFields_erase
#check EffectiveEncoding.countedProgramFields_erase
#print axioms EffectiveEncoding.countedProgramFields_erase
#check EffectiveEncoding.countedAngleFields_steps
#print axioms EffectiveEncoding.countedAngleFields_steps
#check EffectiveEncoding.countedSingleFields_steps
#print axioms EffectiveEncoding.countedSingleFields_steps
#check EffectiveEncoding.countedGateFields_steps
#print axioms EffectiveEncoding.countedGateFields_steps
#check EffectiveEncoding.countedWordFields_steps
#print axioms EffectiveEncoding.countedWordFields_steps
#check EffectiveEncoding.extractionCode_countedFields_roundtrip
#print axioms EffectiveEncoding.extractionCode_countedFields_roundtrip
#check EffectiveEncoding.extractionCode_countedFields_steps
#print axioms EffectiveEncoding.extractionCode_countedFields_steps
#check EffectiveEncoding.extractionCode_countedFields_steps_polynomial
#print axioms EffectiveEncoding.extractionCode_countedFields_steps_polynomial
#check EffectiveEncoding.FieldRun
#print axioms EffectiveEncoding.FieldRun
#check EffectiveEncoding.FieldRun.empty
#print axioms EffectiveEncoding.FieldRun.empty
#check EffectiveEncoding.FieldRun.emit
#print axioms EffectiveEncoding.FieldRun.emit
#check EffectiveEncoding.FieldRun.append
#print axioms EffectiveEncoding.FieldRun.append
#check EffectiveEncoding.countedAngleFields
#print axioms EffectiveEncoding.countedAngleFields
#check EffectiveEncoding.countedSingleFields
#print axioms EffectiveEncoding.countedSingleFields
#check EffectiveEncoding.countedGateFields
#print axioms EffectiveEncoding.countedGateFields
#check EffectiveEncoding.countedWordFields
#print axioms EffectiveEncoding.countedWordFields
#check EffectiveEncoding.countedProgramFields
#print axioms EffectiveEncoding.countedProgramFields
