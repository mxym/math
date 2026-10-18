import ConcreteNativeExtraction.Resources
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for name in [``ConcreteNativeExtraction.offlineNet_exists,
    ``ConcreteNativeExtraction.run_word, ``ConcreteNativeExtraction.run_fidelity,
    ``ConcreteNativeExtraction.run_length, ``ConcreteNativeExtraction.run_uses_finite_library,
    ``ConcreteNativeExtraction.queried_gate_height,
    ``ConcreteNativeExtraction.run_accounted_actions,
    ``ConcreteNativeExtraction.concrete_compiler_exists] do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Expected theorem {name}"
  for name in [``ConcreteNativeExtraction.run,
    ``ConcreteNativeExtraction.gateHeightCoefficient,
    ``ConcreteNativeExtraction.primitiveBound] do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Expected definition {name}"
  logInfo "CONCRETE_NATIVE_ENDPOINT_DECLARATION_KINDS_CHECK_PASS"

#check ConcreteNativeExtraction.offlineNet_exists
#print axioms ConcreteNativeExtraction.offlineNet_exists
#check ConcreteNativeExtraction.run_word
#print axioms ConcreteNativeExtraction.run_word
#check ConcreteNativeExtraction.run_fidelity
#print axioms ConcreteNativeExtraction.run_fidelity
#check ConcreteNativeExtraction.run_length
#print axioms ConcreteNativeExtraction.run_length
#check ConcreteNativeExtraction.run_uses_finite_library
#print axioms ConcreteNativeExtraction.run_uses_finite_library
#check ConcreteNativeExtraction.queried_gate_height
#print axioms ConcreteNativeExtraction.queried_gate_height
#check ConcreteNativeExtraction.run_accounted_actions
#print axioms ConcreteNativeExtraction.run_accounted_actions
#check ConcreteNativeExtraction.concrete_compiler_exists
#print axioms ConcreteNativeExtraction.concrete_compiler_exists
#check ConcreteNativeExtraction.run
#print axioms ConcreteNativeExtraction.run
#check ConcreteNativeExtraction.gateHeightCoefficient
#print axioms ConcreteNativeExtraction.gateHeightCoefficient
#check ConcreteNativeExtraction.primitiveBound
#print axioms ConcreteNativeExtraction.primitiveBound
