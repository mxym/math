import EffectiveEncoding.ActualNativeNumericalBudget

open Lean Elab Command
namespace EffectiveEncodingActualNativeBudgetVerification

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

end EffectiveEncodingActualNativeBudgetVerification

run_cmd (EffectiveEncodingActualNativeBudgetVerification.checkKinds [
  ``EffectiveEncoding.nativeTargetInputCoefficient_gate,
  ``EffectiveEncoding.nativeTargetInputCoefficient_target,
  ``EffectiveEncoding.nativeTargetDescriptorRun_booleanActions_actual,
  ``EffectiveEncoding.compileNativeWord_nativeActions,
  ``EffectiveEncoding.fullyNativeExtractionRun_numericalActions
] [
  ``EffectiveEncoding.nativeTargetInputCoefficient,
  ``EffectiveEncoding.actualNativeBooleanCoefficient,
  ``EffectiveEncoding.NativeCompiledLabelRun.nativeActions
])

#check EffectiveEncoding.nativeTargetInputCoefficient_gate
#print axioms EffectiveEncoding.nativeTargetInputCoefficient_gate
#check EffectiveEncoding.nativeTargetInputCoefficient_target
#print axioms EffectiveEncoding.nativeTargetInputCoefficient_target
#check EffectiveEncoding.nativeTargetDescriptorRun_booleanActions_actual
#print axioms EffectiveEncoding.nativeTargetDescriptorRun_booleanActions_actual
#check EffectiveEncoding.compileNativeWord_nativeActions
#print axioms EffectiveEncoding.compileNativeWord_nativeActions
#check EffectiveEncoding.fullyNativeExtractionRun_numericalActions
#print axioms EffectiveEncoding.fullyNativeExtractionRun_numericalActions
#check EffectiveEncoding.nativeTargetInputCoefficient
#print axioms EffectiveEncoding.nativeTargetInputCoefficient
#check EffectiveEncoding.actualNativeBooleanCoefficient
#print axioms EffectiveEncoding.actualNativeBooleanCoefficient
#check EffectiveEncoding.NativeCompiledLabelRun.nativeActions
#print axioms EffectiveEncoding.NativeCompiledLabelRun.nativeActions
