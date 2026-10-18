import ConcreteNativeExtraction.AssembledProgram
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for name in [``ConcreteNativeExtraction.assembledRun_word,
    ``ConcreteNativeExtraction.assembledRun_erase,
    ``ConcreteNativeExtraction.assembledRun_word_eq_inputRun,
    ``ConcreteNativeExtraction.assembledRun_uses_finite_library,
    ``ConcreteNativeExtraction.assembledRun_length,
    ``ConcreteNativeExtraction.assembledRun_fidelity,
    ``ConcreteNativeExtraction.assembledRun_accounted_actions,
    ``ConcreteNativeExtraction.assembledRun_inverse_calls,
    ``ConcreteNativeExtraction.concrete_assembled_compiler_exists] do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Unexpected declaration kind {name}"
  for name in [``ConcreteNativeExtraction.assembledRun,
    ``ConcreteNativeExtraction.assembledPrimitiveBound] do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Unexpected declaration kind {name}"
  logInfo "CONCRETE_ASSEMBLED_ENDPOINT_DECLARATION_KINDS_CHECK_PASS"

#check ConcreteNativeExtraction.assembledRun_word
#print axioms ConcreteNativeExtraction.assembledRun_word
#check ConcreteNativeExtraction.assembledRun_erase
#print axioms ConcreteNativeExtraction.assembledRun_erase
#check ConcreteNativeExtraction.assembledRun_word_eq_inputRun
#print axioms ConcreteNativeExtraction.assembledRun_word_eq_inputRun
#check ConcreteNativeExtraction.assembledRun_uses_finite_library
#print axioms ConcreteNativeExtraction.assembledRun_uses_finite_library
#check ConcreteNativeExtraction.assembledRun_length
#print axioms ConcreteNativeExtraction.assembledRun_length
#check ConcreteNativeExtraction.assembledRun_fidelity
#print axioms ConcreteNativeExtraction.assembledRun_fidelity
#check ConcreteNativeExtraction.assembledRun_accounted_actions
#print axioms ConcreteNativeExtraction.assembledRun_accounted_actions
#check ConcreteNativeExtraction.assembledRun_inverse_calls
#print axioms ConcreteNativeExtraction.assembledRun_inverse_calls
#check ConcreteNativeExtraction.concrete_assembled_compiler_exists
#print axioms ConcreteNativeExtraction.concrete_assembled_compiler_exists
#check ConcreteNativeExtraction.assembledRun
#print axioms ConcreteNativeExtraction.assembledRun
#check ConcreteNativeExtraction.assembledPrimitiveBound
#print axioms ConcreteNativeExtraction.assembledPrimitiveBound
