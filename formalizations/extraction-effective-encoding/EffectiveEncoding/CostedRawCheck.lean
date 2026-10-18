import EffectiveEncoding.CostedRawCompiler
import EffectiveEncoding.LogarithmicPrecision

open Lean Elab Command
namespace EffectiveEncodingCostedRawVerification

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

end EffectiveEncodingCostedRawVerification

run_cmd (EffectiveEncodingCostedRawVerification.checkKinds [
  ``EffectiveEncoding.costedRawCachedRun_result,
  ``EffectiveEncoding.costedRawCachedRun_rootCharge,
  ``EffectiveEncoding.costedRawDescriptorRun_result,
  ``EffectiveEncoding.costedRawExtractionCode_eq,
  ``EffectiveEncoding.costedRawExtractionCode_fidelity,
  ``EffectiveEncoding.costedRawDescriptorRun_integerBitBudget,
  ``EffectiveEncoding.costedRawDescriptorRun_binaryProgramOperandTrace_height,
  ``EffectiveEncoding.actualGatePolynomial_power_bound,
  ``EffectiveEncoding.extractionCode_length_power_bound,
  ``EffectiveEncoding.extractionPrecision_logarithmic,
  ``EffectiveEncoding.rawExtraction_integerBitBudget_logarithmic,
  ``EffectiveEncoding.rawTargetCache_height_logarithmic
] [
  ``EffectiveEncoding.costedRawCachedRun,
  ``EffectiveEncoding.costedRawDescriptorRun,
  ``EffectiveEncoding.costedRawExtractionCode,
  ``EffectiveEncoding.logarithmicPrecision,
  ``EffectiveEncoding.rawLogarithmicOperandBudget
])

#check EffectiveEncoding.costedRawCachedRun_result
#print axioms EffectiveEncoding.costedRawCachedRun_result
#check EffectiveEncoding.costedRawCachedRun_rootCharge
#print axioms EffectiveEncoding.costedRawCachedRun_rootCharge
#check EffectiveEncoding.costedRawDescriptorRun_result
#print axioms EffectiveEncoding.costedRawDescriptorRun_result
#check EffectiveEncoding.costedRawExtractionCode_eq
#print axioms EffectiveEncoding.costedRawExtractionCode_eq
#check EffectiveEncoding.costedRawExtractionCode_fidelity
#print axioms EffectiveEncoding.costedRawExtractionCode_fidelity
#check EffectiveEncoding.costedRawDescriptorRun_integerBitBudget
#print axioms EffectiveEncoding.costedRawDescriptorRun_integerBitBudget
#check EffectiveEncoding.costedRawDescriptorRun_binaryProgramOperandTrace_height
#print axioms EffectiveEncoding.costedRawDescriptorRun_binaryProgramOperandTrace_height
#check EffectiveEncoding.actualGatePolynomial_power_bound
#print axioms EffectiveEncoding.actualGatePolynomial_power_bound
#check EffectiveEncoding.extractionCode_length_power_bound
#print axioms EffectiveEncoding.extractionCode_length_power_bound
#check EffectiveEncoding.extractionPrecision_logarithmic
#print axioms EffectiveEncoding.extractionPrecision_logarithmic
#check EffectiveEncoding.rawExtraction_integerBitBudget_logarithmic
#print axioms EffectiveEncoding.rawExtraction_integerBitBudget_logarithmic
#check EffectiveEncoding.rawTargetCache_height_logarithmic
#print axioms EffectiveEncoding.rawTargetCache_height_logarithmic
#check EffectiveEncoding.costedRawCachedRun
#print axioms EffectiveEncoding.costedRawCachedRun
#check EffectiveEncoding.costedRawDescriptorRun
#print axioms EffectiveEncoding.costedRawDescriptorRun
#check EffectiveEncoding.costedRawExtractionCode
#print axioms EffectiveEncoding.costedRawExtractionCode
#check EffectiveEncoding.logarithmicPrecision
#print axioms EffectiveEncoding.logarithmicPrecision
#check EffectiveEncoding.rawLogarithmicOperandBudget
#print axioms EffectiveEncoding.rawLogarithmicOperandBudget
