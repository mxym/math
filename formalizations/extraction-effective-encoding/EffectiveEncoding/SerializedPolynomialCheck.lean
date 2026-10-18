import EffectiveEncoding.SerializedPolynomialBudget

open Lean Elab Command
namespace EffectiveEncodingSerializedPolynomialVerification

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

end EffectiveEncodingSerializedPolynomialVerification

run_cmd (EffectiveEncodingSerializedPolynomialVerification.checkKinds [
  ``EffectiveEncoding.onlineCoefficientForm_mono,
  ``EffectiveEncoding.onlineCoefficientForm_dilation,
  ``EffectiveEncoding.actualInputOnlineCoefficient_form,
  ``EffectiveEncoding.actualInputOnlineCoefficient_polynomial,
  ``EffectiveEncoding.labelFieldWidth_polynomial,
  ``EffectiveEncoding.preparationCoefficient_polynomial,
  ``EffectiveEncoding.serializedMonomial_le,
  ``EffectiveEncoding.serializedPrimitiveBudget_polynomial,
  ``EffectiveEncoding.serializedInputRun_accountedPrimitiveActions_polynomial
] [
  ``EffectiveEncoding.onlineCoefficientForm,
  ``EffectiveEncoding.serializedPolynomialConstant
])

#check EffectiveEncoding.onlineCoefficientForm_mono
#print axioms EffectiveEncoding.onlineCoefficientForm_mono
#check EffectiveEncoding.onlineCoefficientForm_dilation
#print axioms EffectiveEncoding.onlineCoefficientForm_dilation
#check EffectiveEncoding.actualInputOnlineCoefficient_form
#print axioms EffectiveEncoding.actualInputOnlineCoefficient_form
#check EffectiveEncoding.actualInputOnlineCoefficient_polynomial
#print axioms EffectiveEncoding.actualInputOnlineCoefficient_polynomial
#check EffectiveEncoding.labelFieldWidth_polynomial
#print axioms EffectiveEncoding.labelFieldWidth_polynomial
#check EffectiveEncoding.preparationCoefficient_polynomial
#print axioms EffectiveEncoding.preparationCoefficient_polynomial
#check EffectiveEncoding.serializedMonomial_le
#print axioms EffectiveEncoding.serializedMonomial_le
#check EffectiveEncoding.serializedPrimitiveBudget_polynomial
#print axioms EffectiveEncoding.serializedPrimitiveBudget_polynomial
#check EffectiveEncoding.serializedInputRun_accountedPrimitiveActions_polynomial
#print axioms EffectiveEncoding.serializedInputRun_accountedPrimitiveActions_polynomial
#check EffectiveEncoding.onlineCoefficientForm
#print axioms EffectiveEncoding.onlineCoefficientForm
#check EffectiveEncoding.serializedPolynomialConstant
#print axioms EffectiveEncoding.serializedPolynomialConstant
