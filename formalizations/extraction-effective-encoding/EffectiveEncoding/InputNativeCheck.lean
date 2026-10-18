import EffectiveEncoding.FullyInputNativeExtraction
import EffectiveEncoding.InputNativeEvaluation

open Lean Elab Command
namespace EffectiveEncodingInputNativeVerification

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

end EffectiveEncodingInputNativeVerification

run_cmd (EffectiveEncodingInputNativeVerification.checkKinds [
  ``EffectiveEncoding.retainedInputTargetRun_cached,
  ``EffectiveEncoding.retainedInputTargetRun_cache,
  ``EffectiveEncoding.retainedInputTargetRun_word,
  ``EffectiveEncoding.retainedInputTargetRun_providerActions,
  ``EffectiveEncoding.retainedInputTargetRun_providerActions_polynomial,
  ``EffectiveEncoding.retainedInputTargetRun_onlineActions,
  ``EffectiveEncoding.compileInputWord_word,
  ``EffectiveEncoding.compileInputWord_sumCharge,
  ``EffectiveEncoding.retainedInputTargetRun_accountedActions,
  ``EffectiveEncoding.fullyInputNativeRun_word,
  ``EffectiveEncoding.fullyInputNativeRun_encodingActions,
  ``EffectiveEncoding.fullyInputNativeRun_accountedPrimitiveActions,
  ``EffectiveEncoding.fullyInputNativeRun_fidelity
] [
  ``EffectiveEncoding.RetainedInputTargetResult,
  ``EffectiveEncoding.retainedInputTargetRun,
  ``EffectiveEncoding.RetainedInputTargetResult.providerActions,
  ``EffectiveEncoding.actualInputOnlineCoefficient,
  ``EffectiveEncoding.InputCompiledLabelRun,
  ``EffectiveEncoding.compileInputGate,
  ``EffectiveEncoding.compileInputWord,
  ``EffectiveEncoding.InputCompiledLabelRun.sumCharge,
  ``EffectiveEncoding.InputCompiledLabelRun.preparationActions,
  ``EffectiveEncoding.InputCompiledLabelRun.providerActions,
  ``EffectiveEncoding.InputCompiledLabelRun.onlineActions,
  ``EffectiveEncoding.RetainedInputTargetResult.accountedActions,
  ``EffectiveEncoding.FullyInputNativeResult,
  ``EffectiveEncoding.fullyInputNativeRun,
  ``EffectiveEncoding.FullyInputNativeResult.accountedPrimitiveActions
])

#check EffectiveEncoding.retainedInputTargetRun_cached
#print axioms EffectiveEncoding.retainedInputTargetRun_cached
#check EffectiveEncoding.retainedInputTargetRun_cache
#print axioms EffectiveEncoding.retainedInputTargetRun_cache
#check EffectiveEncoding.retainedInputTargetRun_word
#print axioms EffectiveEncoding.retainedInputTargetRun_word
#check EffectiveEncoding.retainedInputTargetRun_providerActions
#print axioms EffectiveEncoding.retainedInputTargetRun_providerActions
#check EffectiveEncoding.retainedInputTargetRun_providerActions_polynomial
#print axioms EffectiveEncoding.retainedInputTargetRun_providerActions_polynomial
#check EffectiveEncoding.retainedInputTargetRun_onlineActions
#print axioms EffectiveEncoding.retainedInputTargetRun_onlineActions
#check EffectiveEncoding.compileInputWord_word
#print axioms EffectiveEncoding.compileInputWord_word
#check EffectiveEncoding.compileInputWord_sumCharge
#print axioms EffectiveEncoding.compileInputWord_sumCharge
#check EffectiveEncoding.retainedInputTargetRun_accountedActions
#print axioms EffectiveEncoding.retainedInputTargetRun_accountedActions
#check EffectiveEncoding.fullyInputNativeRun_word
#print axioms EffectiveEncoding.fullyInputNativeRun_word
#check EffectiveEncoding.fullyInputNativeRun_encodingActions
#print axioms EffectiveEncoding.fullyInputNativeRun_encodingActions
#check EffectiveEncoding.fullyInputNativeRun_accountedPrimitiveActions
#print axioms EffectiveEncoding.fullyInputNativeRun_accountedPrimitiveActions
#check EffectiveEncoding.fullyInputNativeRun_fidelity
#print axioms EffectiveEncoding.fullyInputNativeRun_fidelity
#check EffectiveEncoding.RetainedInputTargetResult
#print axioms EffectiveEncoding.RetainedInputTargetResult
#check EffectiveEncoding.retainedInputTargetRun
#print axioms EffectiveEncoding.retainedInputTargetRun
#check EffectiveEncoding.RetainedInputTargetResult.providerActions
#print axioms EffectiveEncoding.RetainedInputTargetResult.providerActions
#check EffectiveEncoding.actualInputOnlineCoefficient
#print axioms EffectiveEncoding.actualInputOnlineCoefficient
#check EffectiveEncoding.InputCompiledLabelRun
#print axioms EffectiveEncoding.InputCompiledLabelRun
#check EffectiveEncoding.compileInputGate
#print axioms EffectiveEncoding.compileInputGate
#check EffectiveEncoding.compileInputWord
#print axioms EffectiveEncoding.compileInputWord
#check EffectiveEncoding.InputCompiledLabelRun.sumCharge
#print axioms EffectiveEncoding.InputCompiledLabelRun.sumCharge
#check EffectiveEncoding.InputCompiledLabelRun.preparationActions
#print axioms EffectiveEncoding.InputCompiledLabelRun.preparationActions
#check EffectiveEncoding.InputCompiledLabelRun.providerActions
#print axioms EffectiveEncoding.InputCompiledLabelRun.providerActions
#check EffectiveEncoding.InputCompiledLabelRun.onlineActions
#print axioms EffectiveEncoding.InputCompiledLabelRun.onlineActions
#check EffectiveEncoding.RetainedInputTargetResult.accountedActions
#print axioms EffectiveEncoding.RetainedInputTargetResult.accountedActions
#check EffectiveEncoding.FullyInputNativeResult
#print axioms EffectiveEncoding.FullyInputNativeResult
#check EffectiveEncoding.fullyInputNativeRun
#print axioms EffectiveEncoding.fullyInputNativeRun
#check EffectiveEncoding.FullyInputNativeResult.accountedPrimitiveActions
#print axioms EffectiveEncoding.FullyInputNativeResult.accountedPrimitiveActions
