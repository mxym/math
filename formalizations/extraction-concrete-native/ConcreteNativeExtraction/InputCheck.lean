import ConcreteNativeExtraction.InputProgram
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for name in [``ConcreteNativeExtraction.inputRun_word,
    ``ConcreteNativeExtraction.inputRun_word_eq_run,
    ``ConcreteNativeExtraction.inputRun_uses_finite_library,
    ``ConcreteNativeExtraction.inputRun_length, ``ConcreteNativeExtraction.inputRun_fidelity,
    ``ConcreteNativeExtraction.inputRun_accounted_actions,
    ``ConcreteNativeExtraction.concrete_input_compiler_exists] do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Expected theorem {name}"
  for name in [``ConcreteNativeExtraction.inputRun,
    ``ConcreteNativeExtraction.inputPrimitiveBound] do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Expected definition {name}"
  logInfo "CONCRETE_NATIVE_INPUT_ENDPOINT_DECLARATION_KINDS_CHECK_PASS"

#check ConcreteNativeExtraction.inputRun_word
#print axioms ConcreteNativeExtraction.inputRun_word
#check ConcreteNativeExtraction.inputRun_word_eq_run
#print axioms ConcreteNativeExtraction.inputRun_word_eq_run
#check ConcreteNativeExtraction.inputRun_uses_finite_library
#print axioms ConcreteNativeExtraction.inputRun_uses_finite_library
#check ConcreteNativeExtraction.inputRun_length
#print axioms ConcreteNativeExtraction.inputRun_length
#check ConcreteNativeExtraction.inputRun_fidelity
#print axioms ConcreteNativeExtraction.inputRun_fidelity
#check ConcreteNativeExtraction.inputRun_accounted_actions
#print axioms ConcreteNativeExtraction.inputRun_accounted_actions
#check ConcreteNativeExtraction.concrete_input_compiler_exists
#print axioms ConcreteNativeExtraction.concrete_input_compiler_exists
#check ConcreteNativeExtraction.inputRun
#print axioms ConcreteNativeExtraction.inputRun
#check ConcreteNativeExtraction.inputPrimitiveBound
#print axioms ConcreteNativeExtraction.inputPrimitiveBound
