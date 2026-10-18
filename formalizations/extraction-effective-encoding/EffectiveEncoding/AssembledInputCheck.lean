import EffectiveEncoding.FullyAssembledInputExtraction
import EffectiveEncoding.AssembledInputEvaluation

open Lean Elab Command
namespace EffectiveEncodingAssembledInputVerification

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

end EffectiveEncodingAssembledInputVerification

run_cmd (EffectiveEncodingAssembledInputVerification.checkKinds [
  ``EffectiveEncoding.retainedAssembledTargetRun_erase,
  ``EffectiveEncoding.retainedAssembledTargetRun_cached,
  ``EffectiveEncoding.retainedAssembledTargetRun_assemblyActions,
  ``EffectiveEncoding.retainedAssembledTargetRun_inverseCalls,
  ``EffectiveEncoding.compileAssembledGate_erase,
  ``EffectiveEncoding.compileAssembledWord_erase,
  ``EffectiveEncoding.compileAssembledWord_sumTrace,
  ``EffectiveEncoding.AssembledCompiledLabelRun.inverseCalls_le_assemblyActions,
  ``EffectiveEncoding.fullyAssembledInputRun_erase,
  ``EffectiveEncoding.fullyAssembledInputRun_word,
  ``EffectiveEncoding.fullyAssembledInputRun_assemblyActions,
  ``EffectiveEncoding.fullyAssembledInputRun_inverseCalls,
  ``EffectiveEncoding.fullyAssembledInputRun_accountedPrimitiveActions,
  ``EffectiveEncoding.fullyAssembledInputRun_fidelity
] [
  ``EffectiveEncoding.RetainedAssembledTargetResult,
  ``EffectiveEncoding.retainedAssembledTargetRun,
  ``EffectiveEncoding.RetainedAssembledTargetResult.erase,
  ``EffectiveEncoding.RetainedAssembledTargetResult.assemblyActions,
  ``EffectiveEncoding.RetainedAssembledTargetResult.inverseCalls,
  ``EffectiveEncoding.AssembledCompiledLabelRun,
  ``EffectiveEncoding.AssembledCompiledLabelRun.erase,
  ``EffectiveEncoding.compileAssembledGate,
  ``EffectiveEncoding.compileAssembledWord,
  ``EffectiveEncoding.AssembledCompiledLabelRun.sumTrace,
  ``EffectiveEncoding.AssembledCompiledLabelRun.assemblyActions,
  ``EffectiveEncoding.AssembledCompiledLabelRun.inverseCalls,
  ``EffectiveEncoding.FullyAssembledInputResult,
  ``EffectiveEncoding.FullyAssembledInputResult.erase,
  ``EffectiveEncoding.fullyAssembledInputRun,
  ``EffectiveEncoding.FullyAssembledInputResult.accountedPrimitiveActions
])

#check EffectiveEncoding.retainedAssembledTargetRun_erase
#print axioms EffectiveEncoding.retainedAssembledTargetRun_erase
#check EffectiveEncoding.retainedAssembledTargetRun_cached
#print axioms EffectiveEncoding.retainedAssembledTargetRun_cached
#check EffectiveEncoding.retainedAssembledTargetRun_assemblyActions
#print axioms EffectiveEncoding.retainedAssembledTargetRun_assemblyActions
#check EffectiveEncoding.retainedAssembledTargetRun_inverseCalls
#print axioms EffectiveEncoding.retainedAssembledTargetRun_inverseCalls
#check EffectiveEncoding.compileAssembledGate_erase
#print axioms EffectiveEncoding.compileAssembledGate_erase
#check EffectiveEncoding.compileAssembledWord_erase
#print axioms EffectiveEncoding.compileAssembledWord_erase
#check EffectiveEncoding.compileAssembledWord_sumTrace
#print axioms EffectiveEncoding.compileAssembledWord_sumTrace
#check EffectiveEncoding.AssembledCompiledLabelRun.inverseCalls_le_assemblyActions
#print axioms EffectiveEncoding.AssembledCompiledLabelRun.inverseCalls_le_assemblyActions
#check EffectiveEncoding.fullyAssembledInputRun_erase
#print axioms EffectiveEncoding.fullyAssembledInputRun_erase
#check EffectiveEncoding.fullyAssembledInputRun_word
#print axioms EffectiveEncoding.fullyAssembledInputRun_word
#check EffectiveEncoding.fullyAssembledInputRun_assemblyActions
#print axioms EffectiveEncoding.fullyAssembledInputRun_assemblyActions
#check EffectiveEncoding.fullyAssembledInputRun_inverseCalls
#print axioms EffectiveEncoding.fullyAssembledInputRun_inverseCalls
#check EffectiveEncoding.fullyAssembledInputRun_accountedPrimitiveActions
#print axioms EffectiveEncoding.fullyAssembledInputRun_accountedPrimitiveActions
#check EffectiveEncoding.fullyAssembledInputRun_fidelity
#print axioms EffectiveEncoding.fullyAssembledInputRun_fidelity
#check EffectiveEncoding.RetainedAssembledTargetResult
#print axioms EffectiveEncoding.RetainedAssembledTargetResult
#check EffectiveEncoding.retainedAssembledTargetRun
#print axioms EffectiveEncoding.retainedAssembledTargetRun
#check EffectiveEncoding.RetainedAssembledTargetResult.erase
#print axioms EffectiveEncoding.RetainedAssembledTargetResult.erase
#check EffectiveEncoding.RetainedAssembledTargetResult.assemblyActions
#print axioms EffectiveEncoding.RetainedAssembledTargetResult.assemblyActions
#check EffectiveEncoding.RetainedAssembledTargetResult.inverseCalls
#print axioms EffectiveEncoding.RetainedAssembledTargetResult.inverseCalls
#check EffectiveEncoding.AssembledCompiledLabelRun
#print axioms EffectiveEncoding.AssembledCompiledLabelRun
#check EffectiveEncoding.AssembledCompiledLabelRun.erase
#print axioms EffectiveEncoding.AssembledCompiledLabelRun.erase
#check EffectiveEncoding.compileAssembledGate
#print axioms EffectiveEncoding.compileAssembledGate
#check EffectiveEncoding.compileAssembledWord
#print axioms EffectiveEncoding.compileAssembledWord
#check EffectiveEncoding.AssembledCompiledLabelRun.sumTrace
#print axioms EffectiveEncoding.AssembledCompiledLabelRun.sumTrace
#check EffectiveEncoding.AssembledCompiledLabelRun.assemblyActions
#print axioms EffectiveEncoding.AssembledCompiledLabelRun.assemblyActions
#check EffectiveEncoding.AssembledCompiledLabelRun.inverseCalls
#print axioms EffectiveEncoding.AssembledCompiledLabelRun.inverseCalls
#check EffectiveEncoding.FullyAssembledInputResult
#print axioms EffectiveEncoding.FullyAssembledInputResult
#check EffectiveEncoding.FullyAssembledInputResult.erase
#print axioms EffectiveEncoding.FullyAssembledInputResult.erase
#check EffectiveEncoding.fullyAssembledInputRun
#print axioms EffectiveEncoding.fullyAssembledInputRun
#check EffectiveEncoding.FullyAssembledInputResult.accountedPrimitiveActions
#print axioms EffectiveEncoding.FullyAssembledInputResult.accountedPrimitiveActions
