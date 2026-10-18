import EffectiveEncoding.NativeBooleanExtraction

open Lean Elab Command
namespace EffectiveEncodingActualBooleanVerification

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

end EffectiveEncodingActualBooleanVerification

run_cmd (EffectiveEncodingActualBooleanVerification.checkKinds [
  ``EffectiveEncoding.booleanRawCachedRun_result,
  ``EffectiveEncoding.booleanRawCachedRun_actions_power,
  ``EffectiveEncoding.booleanRawDescriptorRun_result,
  ``EffectiveEncoding.booleanTargetDescriptorRun_online,
  ``EffectiveEncoding.booleanTargetDescriptorRun_result,
  ``EffectiveEncoding.booleanTargetDescriptorRun_providerRootCharge,
  ``EffectiveEncoding.booleanRawDescriptorRun_actions,
  ``EffectiveEncoding.booleanTargetDescriptorRun_actions,
  ``EffectiveEncoding.booleanTargetDescriptorRun_providerRootCharge_bound,
  ``EffectiveEncoding.nativeDescriptorRun_actualWord,
  ``EffectiveEncoding.booleanCompileWord_word,
  ``EffectiveEncoding.booleanCompileWord_work,
  ``EffectiveEncoding.nativeBooleanExtractionRun_word,
  ``EffectiveEncoding.nativeBooleanExtractionRun_rankWork,
  ``EffectiveEncoding.nativeBooleanExtractionRun_onlineActions,
  ``EffectiveEncoding.nativeBooleanExtractionRun_providerRootCharge,
  ``EffectiveEncoding.nativeBooleanExtractionRun_fidelity
] [
  ``EffectiveEncoding.booleanRawCachedRun,
  ``EffectiveEncoding.booleanRawDescriptorRun,
  ``EffectiveEncoding.BooleanProviderResult,
  ``EffectiveEncoding.booleanTargetDescriptorRun,
  ``EffectiveEncoding.actualBooleanDescriptorCoefficient,
  ``EffectiveEncoding.BooleanCompilationWork,
  ``EffectiveEncoding.BooleanLabelRun,
  ``EffectiveEncoding.booleanCompileGate,
  ``EffectiveEncoding.booleanCompileWord,
  ``EffectiveEncoding.NativeBooleanResult,
  ``EffectiveEncoding.nativeBooleanExtractionRun
])

#check EffectiveEncoding.booleanRawCachedRun_result
#print axioms EffectiveEncoding.booleanRawCachedRun_result
#check EffectiveEncoding.booleanRawCachedRun_actions_power
#print axioms EffectiveEncoding.booleanRawCachedRun_actions_power
#check EffectiveEncoding.booleanRawDescriptorRun_result
#print axioms EffectiveEncoding.booleanRawDescriptorRun_result
#check EffectiveEncoding.booleanTargetDescriptorRun_online
#print axioms EffectiveEncoding.booleanTargetDescriptorRun_online
#check EffectiveEncoding.booleanTargetDescriptorRun_result
#print axioms EffectiveEncoding.booleanTargetDescriptorRun_result
#check EffectiveEncoding.booleanTargetDescriptorRun_providerRootCharge
#print axioms EffectiveEncoding.booleanTargetDescriptorRun_providerRootCharge
#check EffectiveEncoding.booleanRawDescriptorRun_actions
#print axioms EffectiveEncoding.booleanRawDescriptorRun_actions
#check EffectiveEncoding.booleanTargetDescriptorRun_actions
#print axioms EffectiveEncoding.booleanTargetDescriptorRun_actions
#check EffectiveEncoding.booleanTargetDescriptorRun_providerRootCharge_bound
#print axioms EffectiveEncoding.booleanTargetDescriptorRun_providerRootCharge_bound
#check EffectiveEncoding.nativeDescriptorRun_actualWord
#print axioms EffectiveEncoding.nativeDescriptorRun_actualWord
#check EffectiveEncoding.booleanCompileWord_word
#print axioms EffectiveEncoding.booleanCompileWord_word
#check EffectiveEncoding.booleanCompileWord_work
#print axioms EffectiveEncoding.booleanCompileWord_work
#check EffectiveEncoding.nativeBooleanExtractionRun_word
#print axioms EffectiveEncoding.nativeBooleanExtractionRun_word
#check EffectiveEncoding.nativeBooleanExtractionRun_rankWork
#print axioms EffectiveEncoding.nativeBooleanExtractionRun_rankWork
#check EffectiveEncoding.nativeBooleanExtractionRun_onlineActions
#print axioms EffectiveEncoding.nativeBooleanExtractionRun_onlineActions
#check EffectiveEncoding.nativeBooleanExtractionRun_providerRootCharge
#print axioms EffectiveEncoding.nativeBooleanExtractionRun_providerRootCharge
#check EffectiveEncoding.nativeBooleanExtractionRun_fidelity
#print axioms EffectiveEncoding.nativeBooleanExtractionRun_fidelity
#check EffectiveEncoding.booleanRawCachedRun
#print axioms EffectiveEncoding.booleanRawCachedRun
#check EffectiveEncoding.booleanRawDescriptorRun
#print axioms EffectiveEncoding.booleanRawDescriptorRun
#check EffectiveEncoding.BooleanProviderResult
#print axioms EffectiveEncoding.BooleanProviderResult
#check EffectiveEncoding.booleanTargetDescriptorRun
#print axioms EffectiveEncoding.booleanTargetDescriptorRun
#check EffectiveEncoding.actualBooleanDescriptorCoefficient
#print axioms EffectiveEncoding.actualBooleanDescriptorCoefficient
#check EffectiveEncoding.BooleanCompilationWork
#print axioms EffectiveEncoding.BooleanCompilationWork
#check EffectiveEncoding.BooleanLabelRun
#print axioms EffectiveEncoding.BooleanLabelRun
#check EffectiveEncoding.booleanCompileGate
#print axioms EffectiveEncoding.booleanCompileGate
#check EffectiveEncoding.booleanCompileWord
#print axioms EffectiveEncoding.booleanCompileWord
#check EffectiveEncoding.NativeBooleanResult
#print axioms EffectiveEncoding.NativeBooleanResult
#check EffectiveEncoding.nativeBooleanExtractionRun
#print axioms EffectiveEncoding.nativeBooleanExtractionRun
