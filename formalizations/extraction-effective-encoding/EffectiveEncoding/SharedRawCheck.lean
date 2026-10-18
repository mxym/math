import EffectiveEncoding.SharedRawCompiler

open Lean Elab Command
namespace EffectiveEncodingSharedRawVerification

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

end EffectiveEncodingSharedRawVerification

run_cmd (EffectiveEncodingSharedRawVerification.checkKinds [
  ``EffectiveEncoding.sharedRawCachedRun_eq,
  ``EffectiveEncoding.sharedRawDescriptorRun_eq,
  ``EffectiveEncoding.sharedRawExtractionCode_eq,
  ``EffectiveEncoding.sharedRawExtractionCode_length,
  ``EffectiveEncoding.sharedRawExtractionCode_error,
  ``EffectiveEncoding.sharedRawExtractionCode_fidelity,
  ``EffectiveEncoding.sharedRawDescriptorRun_rootCharge,
  ``EffectiveEncoding.sharedRawDescriptorRun_integerBitBudget,
  ``EffectiveEncoding.extractionSharedRawRootCharge_eq,
  ``EffectiveEncoding.extractionSharedRawRootCharge_bound
] [
  ``EffectiveEncoding.sharedRawCachedRun,
  ``EffectiveEncoding.sharedRawDescriptorRun,
  ``EffectiveEncoding.sharedRawExtractionCode,
  ``EffectiveEncoding.gateSharedRawRootCharge,
  ``EffectiveEncoding.extractionSharedRawRootCharge
])

#check EffectiveEncoding.sharedRawCachedRun_eq
#print axioms EffectiveEncoding.sharedRawCachedRun_eq
#check EffectiveEncoding.sharedRawDescriptorRun_eq
#print axioms EffectiveEncoding.sharedRawDescriptorRun_eq
#check EffectiveEncoding.sharedRawExtractionCode_eq
#print axioms EffectiveEncoding.sharedRawExtractionCode_eq
#check EffectiveEncoding.sharedRawExtractionCode_length
#print axioms EffectiveEncoding.sharedRawExtractionCode_length
#check EffectiveEncoding.sharedRawExtractionCode_error
#print axioms EffectiveEncoding.sharedRawExtractionCode_error
#check EffectiveEncoding.sharedRawExtractionCode_fidelity
#print axioms EffectiveEncoding.sharedRawExtractionCode_fidelity
#check EffectiveEncoding.sharedRawDescriptorRun_rootCharge
#print axioms EffectiveEncoding.sharedRawDescriptorRun_rootCharge
#check EffectiveEncoding.sharedRawDescriptorRun_integerBitBudget
#print axioms EffectiveEncoding.sharedRawDescriptorRun_integerBitBudget
#check EffectiveEncoding.extractionSharedRawRootCharge_eq
#print axioms EffectiveEncoding.extractionSharedRawRootCharge_eq
#check EffectiveEncoding.extractionSharedRawRootCharge_bound
#print axioms EffectiveEncoding.extractionSharedRawRootCharge_bound
#check EffectiveEncoding.sharedRawCachedRun
#print axioms EffectiveEncoding.sharedRawCachedRun
#check EffectiveEncoding.sharedRawDescriptorRun
#print axioms EffectiveEncoding.sharedRawDescriptorRun
#check EffectiveEncoding.sharedRawExtractionCode
#print axioms EffectiveEncoding.sharedRawExtractionCode
#check EffectiveEncoding.gateSharedRawRootCharge
#print axioms EffectiveEncoding.gateSharedRawRootCharge
#check EffectiveEncoding.extractionSharedRawRootCharge
#print axioms EffectiveEncoding.extractionSharedRawRootCharge
