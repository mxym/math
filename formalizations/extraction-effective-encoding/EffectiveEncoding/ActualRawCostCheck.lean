import EffectiveEncoding.ActualRawRootCharge

open Lean Elab Command
namespace EffectiveEncodingActualRawCostVerification

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

end EffectiveEncodingActualRawCostVerification

run_cmd (EffectiveEncodingActualRawCostVerification.checkKinds [
  ``EffectiveEncoding.costedRawCachedRun_operations,
  ``EffectiveEncoding.costedRawDescriptorRun_rootCharge_polynomial,
  ``EffectiveEncoding.costedRawDescriptorRun_rootCharge_logarithmic,
  ``EffectiveEncoding.extractionRawRootCharge_bound,
  ``EffectiveEncoding.extractionRawRootCharge_polynomial
] [
  ``EffectiveEncoding.actualRawRootCoefficient,
  ``EffectiveEncoding.gateRawRootCharge,
  ``EffectiveEncoding.extractionRawRootCharge
])

#check EffectiveEncoding.costedRawCachedRun_operations
#print axioms EffectiveEncoding.costedRawCachedRun_operations
#check EffectiveEncoding.costedRawDescriptorRun_rootCharge_polynomial
#print axioms EffectiveEncoding.costedRawDescriptorRun_rootCharge_polynomial
#check EffectiveEncoding.costedRawDescriptorRun_rootCharge_logarithmic
#print axioms EffectiveEncoding.costedRawDescriptorRun_rootCharge_logarithmic
#check EffectiveEncoding.extractionRawRootCharge_bound
#print axioms EffectiveEncoding.extractionRawRootCharge_bound
#check EffectiveEncoding.extractionRawRootCharge_polynomial
#print axioms EffectiveEncoding.extractionRawRootCharge_polynomial
#check EffectiveEncoding.actualRawRootCoefficient
#print axioms EffectiveEncoding.actualRawRootCoefficient
#check EffectiveEncoding.gateRawRootCharge
#print axioms EffectiveEncoding.gateRawRootCharge
#check EffectiveEncoding.extractionRawRootCharge
#print axioms EffectiveEncoding.extractionRawRootCharge
