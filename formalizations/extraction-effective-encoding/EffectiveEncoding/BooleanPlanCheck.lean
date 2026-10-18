import EffectiveEncoding.BooleanMaskContextProgram
import EffectiveEncoding.BooleanPlanEvaluation

open Lean Elab Command
namespace EffectiveEncodingBooleanPlanVerification

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

end EffectiveEncodingBooleanPlanVerification

run_cmd (EffectiveEncodingBooleanPlanVerification.checkKinds [
  ``EffectiveEncoding.maskCoordinateSelectProgram_map,
  ``EffectiveEncoding.maskCoordinateSelectProgram_actions,
  ``EffectiveEncoding.packedMask_finRange_map,
  ``EffectiveEncoding.booleanMaskCoordinates_items,
  ``EffectiveEncoding.booleanMaskCoordinates_sortedMask,
  ``EffectiveEncoding.booleanMaskCoordinates_nodup,
  ``EffectiveEncoding.booleanMaskCoordinates_actions,
  ``EffectiveEncoding.cnotListProgram_word,
  ``EffectiveEncoding.cnotListProgram_length,
  ``EffectiveEncoding.cnotListProgram_actions,
  ``EffectiveEncoding.sortedList_head_min,
  ``EffectiveEncoding.sortedList_head_erase,
  ``EffectiveEncoding.listPauliPlanProgram_plan,
  ``EffectiveEncoding.listPauliPlanProgram_actions,
  ``EffectiveEncoding.booleanPauliPlanProgram_plan,
  ``EffectiveEncoding.booleanPauliPlanProgram_actions,
  ``EffectiveEncoding.booleanPlanTableProgram_plans,
  ``EffectiveEncoding.booleanPlanTableProgram_programs,
  ``EffectiveEncoding.booleanPlanTableProgram_traceActions,
  ``EffectiveEncoding.booleanPlanTableProgram_actions,
  ``EffectiveEncoding.booleanMaskContextProgram_common,
  ``EffectiveEncoding.booleanMaskContextProgram_plans,
  ``EffectiveEncoding.booleanMaskContextProgram_planActions,
  ``EffectiveEncoding.booleanMaskContextProgram_active_planActions,
  ``EffectiveEncoding.booleanMaskContextProgram_active_actions
] [
  ``EffectiveEncoding.MaskCoordinateTrace,
  ``EffectiveEncoding.MaskCoordinateTrace.actions,
  ``EffectiveEncoding.MaskCoordinateResult,
  ``EffectiveEncoding.maskCoordinateSelectProgram,
  ``EffectiveEncoding.booleanMaskCoordinates,
  ``EffectiveEncoding.CnotListTrace,
  ``EffectiveEncoding.CnotListTrace.actions,
  ``EffectiveEncoding.CnotListResult,
  ``EffectiveEncoding.cnotListProgram,
  ``EffectiveEncoding.ListPauliPlanResult,
  ``EffectiveEncoding.listPauliPlanProgram,
  ``EffectiveEncoding.ListPauliPlanResult.actions,
  ``EffectiveEncoding.BooleanPauliPlanResult,
  ``EffectiveEncoding.booleanPauliPlanProgram,
  ``EffectiveEncoding.BooleanPauliPlanResult.actions,
  ``EffectiveEncoding.BooleanPlanTableTrace,
  ``EffectiveEncoding.BooleanPlanTableTrace.actions,
  ``EffectiveEncoding.BooleanPlanTableResult,
  ``EffectiveEncoding.booleanPlanTableProgram,
  ``EffectiveEncoding.BooleanPlanTableResult.actions,
  ``EffectiveEncoding.BooleanMaskContextResult,
  ``EffectiveEncoding.booleanMaskContextProgram,
  ``EffectiveEncoding.BooleanMaskContextResult.planActions,
  ``EffectiveEncoding.BooleanMaskContextResult.actions
])

#check EffectiveEncoding.maskCoordinateSelectProgram_map
#print axioms EffectiveEncoding.maskCoordinateSelectProgram_map
#check EffectiveEncoding.maskCoordinateSelectProgram_actions
#print axioms EffectiveEncoding.maskCoordinateSelectProgram_actions
#check EffectiveEncoding.packedMask_finRange_map
#print axioms EffectiveEncoding.packedMask_finRange_map
#check EffectiveEncoding.booleanMaskCoordinates_items
#print axioms EffectiveEncoding.booleanMaskCoordinates_items
#check EffectiveEncoding.booleanMaskCoordinates_sortedMask
#print axioms EffectiveEncoding.booleanMaskCoordinates_sortedMask
#check EffectiveEncoding.booleanMaskCoordinates_nodup
#print axioms EffectiveEncoding.booleanMaskCoordinates_nodup
#check EffectiveEncoding.booleanMaskCoordinates_actions
#print axioms EffectiveEncoding.booleanMaskCoordinates_actions
#check EffectiveEncoding.cnotListProgram_word
#print axioms EffectiveEncoding.cnotListProgram_word
#check EffectiveEncoding.cnotListProgram_length
#print axioms EffectiveEncoding.cnotListProgram_length
#check EffectiveEncoding.cnotListProgram_actions
#print axioms EffectiveEncoding.cnotListProgram_actions
#check EffectiveEncoding.sortedList_head_min
#print axioms EffectiveEncoding.sortedList_head_min
#check EffectiveEncoding.sortedList_head_erase
#print axioms EffectiveEncoding.sortedList_head_erase
#check EffectiveEncoding.listPauliPlanProgram_plan
#print axioms EffectiveEncoding.listPauliPlanProgram_plan
#check EffectiveEncoding.listPauliPlanProgram_actions
#print axioms EffectiveEncoding.listPauliPlanProgram_actions
#check EffectiveEncoding.booleanPauliPlanProgram_plan
#print axioms EffectiveEncoding.booleanPauliPlanProgram_plan
#check EffectiveEncoding.booleanPauliPlanProgram_actions
#print axioms EffectiveEncoding.booleanPauliPlanProgram_actions
#check EffectiveEncoding.booleanPlanTableProgram_plans
#print axioms EffectiveEncoding.booleanPlanTableProgram_plans
#check EffectiveEncoding.booleanPlanTableProgram_programs
#print axioms EffectiveEncoding.booleanPlanTableProgram_programs
#check EffectiveEncoding.booleanPlanTableProgram_traceActions
#print axioms EffectiveEncoding.booleanPlanTableProgram_traceActions
#check EffectiveEncoding.booleanPlanTableProgram_actions
#print axioms EffectiveEncoding.booleanPlanTableProgram_actions
#check EffectiveEncoding.booleanMaskContextProgram_common
#print axioms EffectiveEncoding.booleanMaskContextProgram_common
#check EffectiveEncoding.booleanMaskContextProgram_plans
#print axioms EffectiveEncoding.booleanMaskContextProgram_plans
#check EffectiveEncoding.booleanMaskContextProgram_planActions
#print axioms EffectiveEncoding.booleanMaskContextProgram_planActions
#check EffectiveEncoding.booleanMaskContextProgram_active_planActions
#print axioms EffectiveEncoding.booleanMaskContextProgram_active_planActions
#check EffectiveEncoding.booleanMaskContextProgram_active_actions
#print axioms EffectiveEncoding.booleanMaskContextProgram_active_actions
#check EffectiveEncoding.MaskCoordinateTrace
#print axioms EffectiveEncoding.MaskCoordinateTrace
#check EffectiveEncoding.MaskCoordinateTrace.actions
#print axioms EffectiveEncoding.MaskCoordinateTrace.actions
#check EffectiveEncoding.MaskCoordinateResult
#print axioms EffectiveEncoding.MaskCoordinateResult
#check EffectiveEncoding.maskCoordinateSelectProgram
#print axioms EffectiveEncoding.maskCoordinateSelectProgram
#check EffectiveEncoding.booleanMaskCoordinates
#print axioms EffectiveEncoding.booleanMaskCoordinates
#check EffectiveEncoding.CnotListTrace
#print axioms EffectiveEncoding.CnotListTrace
#check EffectiveEncoding.CnotListTrace.actions
#print axioms EffectiveEncoding.CnotListTrace.actions
#check EffectiveEncoding.CnotListResult
#print axioms EffectiveEncoding.CnotListResult
#check EffectiveEncoding.cnotListProgram
#print axioms EffectiveEncoding.cnotListProgram
#check EffectiveEncoding.ListPauliPlanResult
#print axioms EffectiveEncoding.ListPauliPlanResult
#check EffectiveEncoding.listPauliPlanProgram
#print axioms EffectiveEncoding.listPauliPlanProgram
#check EffectiveEncoding.ListPauliPlanResult.actions
#print axioms EffectiveEncoding.ListPauliPlanResult.actions
#check EffectiveEncoding.BooleanPauliPlanResult
#print axioms EffectiveEncoding.BooleanPauliPlanResult
#check EffectiveEncoding.booleanPauliPlanProgram
#print axioms EffectiveEncoding.booleanPauliPlanProgram
#check EffectiveEncoding.BooleanPauliPlanResult.actions
#print axioms EffectiveEncoding.BooleanPauliPlanResult.actions
#check EffectiveEncoding.BooleanPlanTableTrace
#print axioms EffectiveEncoding.BooleanPlanTableTrace
#check EffectiveEncoding.BooleanPlanTableTrace.actions
#print axioms EffectiveEncoding.BooleanPlanTableTrace.actions
#check EffectiveEncoding.BooleanPlanTableResult
#print axioms EffectiveEncoding.BooleanPlanTableResult
#check EffectiveEncoding.booleanPlanTableProgram
#print axioms EffectiveEncoding.booleanPlanTableProgram
#check EffectiveEncoding.BooleanPlanTableResult.actions
#print axioms EffectiveEncoding.BooleanPlanTableResult.actions
#check EffectiveEncoding.BooleanMaskContextResult
#print axioms EffectiveEncoding.BooleanMaskContextResult
#check EffectiveEncoding.booleanMaskContextProgram
#print axioms EffectiveEncoding.booleanMaskContextProgram
#check EffectiveEncoding.BooleanMaskContextResult.planActions
#print axioms EffectiveEncoding.BooleanMaskContextResult.planActions
#check EffectiveEncoding.BooleanMaskContextResult.actions
#print axioms EffectiveEncoding.BooleanMaskContextResult.actions
