import EffectiveEncoding.FullyMaterializedInputExtraction
import EffectiveEncoding.MaterializedInputEvaluation

open Lean Elab Command
namespace EffectiveEncodingMaterializedInputVerification

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

end EffectiveEncodingMaterializedInputVerification

run_cmd (EffectiveEncodingMaterializedInputVerification.checkKinds [
  ``EffectiveEncoding.wireLabelProgram_word,
  ``EffectiveEncoding.wireLabelProgram_actions,
  ``EffectiveEncoding.materializeGate_value,
  ``EffectiveEncoding.materializeWord_value,
  ``EffectiveEncoding.materializeGate_headActions,
  ``EffectiveEncoding.materializeWord_actions,
  ``EffectiveEncoding.retainedAssembledTargetRun_word_length,
  ``EffectiveEncoding.fullyMaterializedInputRun_erase,
  ``EffectiveEncoding.fullyMaterializedInputRun_word,
  ``EffectiveEncoding.fullyMaterializedInputRun_outerActions,
  ``EffectiveEncoding.fullyMaterializedInputRun_accountedPrimitiveActions,
  ``EffectiveEncoding.fullyMaterializedInputRun_fidelity
] [
  ``EffectiveEncoding.WireLabelTrace,
  ``EffectiveEncoding.WireLabelResult,
  ``EffectiveEncoding.wireLabelProgram,
  ``EffectiveEncoding.WireLabelTrace.actions,
  ``EffectiveEncoding.OuterLabelTrace,
  ``EffectiveEncoding.OuterLabelTrace.actions,
  ``EffectiveEncoding.MaterializedLabelRun,
  ``EffectiveEncoding.materializeGate,
  ``EffectiveEncoding.materializeWord,
  ``EffectiveEncoding.FullyMaterializedInputResult,
  ``EffectiveEncoding.FullyMaterializedInputResult.erase,
  ``EffectiveEncoding.fullyMaterializedInputRun,
  ``EffectiveEncoding.FullyMaterializedInputResult.accountedPrimitiveActions
])

#check EffectiveEncoding.wireLabelProgram_word
#print axioms EffectiveEncoding.wireLabelProgram_word
#check EffectiveEncoding.wireLabelProgram_actions
#print axioms EffectiveEncoding.wireLabelProgram_actions
#check EffectiveEncoding.materializeGate_value
#print axioms EffectiveEncoding.materializeGate_value
#check EffectiveEncoding.materializeWord_value
#print axioms EffectiveEncoding.materializeWord_value
#check EffectiveEncoding.materializeGate_headActions
#print axioms EffectiveEncoding.materializeGate_headActions
#check EffectiveEncoding.materializeWord_actions
#print axioms EffectiveEncoding.materializeWord_actions
#check EffectiveEncoding.retainedAssembledTargetRun_word_length
#print axioms EffectiveEncoding.retainedAssembledTargetRun_word_length
#check EffectiveEncoding.fullyMaterializedInputRun_erase
#print axioms EffectiveEncoding.fullyMaterializedInputRun_erase
#check EffectiveEncoding.fullyMaterializedInputRun_word
#print axioms EffectiveEncoding.fullyMaterializedInputRun_word
#check EffectiveEncoding.fullyMaterializedInputRun_outerActions
#print axioms EffectiveEncoding.fullyMaterializedInputRun_outerActions
#check EffectiveEncoding.fullyMaterializedInputRun_accountedPrimitiveActions
#print axioms EffectiveEncoding.fullyMaterializedInputRun_accountedPrimitiveActions
#check EffectiveEncoding.fullyMaterializedInputRun_fidelity
#print axioms EffectiveEncoding.fullyMaterializedInputRun_fidelity
#check EffectiveEncoding.WireLabelTrace
#print axioms EffectiveEncoding.WireLabelTrace
#check EffectiveEncoding.WireLabelResult
#print axioms EffectiveEncoding.WireLabelResult
#check EffectiveEncoding.wireLabelProgram
#print axioms EffectiveEncoding.wireLabelProgram
#check EffectiveEncoding.WireLabelTrace.actions
#print axioms EffectiveEncoding.WireLabelTrace.actions
#check EffectiveEncoding.OuterLabelTrace
#print axioms EffectiveEncoding.OuterLabelTrace
#check EffectiveEncoding.OuterLabelTrace.actions
#print axioms EffectiveEncoding.OuterLabelTrace.actions
#check EffectiveEncoding.MaterializedLabelRun
#print axioms EffectiveEncoding.MaterializedLabelRun
#check EffectiveEncoding.materializeGate
#print axioms EffectiveEncoding.materializeGate
#check EffectiveEncoding.materializeWord
#print axioms EffectiveEncoding.materializeWord
#check EffectiveEncoding.FullyMaterializedInputResult
#print axioms EffectiveEncoding.FullyMaterializedInputResult
#check EffectiveEncoding.FullyMaterializedInputResult.erase
#print axioms EffectiveEncoding.FullyMaterializedInputResult.erase
#check EffectiveEncoding.fullyMaterializedInputRun
#print axioms EffectiveEncoding.fullyMaterializedInputRun
#check EffectiveEncoding.FullyMaterializedInputResult.accountedPrimitiveActions
#print axioms EffectiveEncoding.FullyMaterializedInputResult.accountedPrimitiveActions
