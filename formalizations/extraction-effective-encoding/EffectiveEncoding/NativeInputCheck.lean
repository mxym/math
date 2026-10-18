import EffectiveEncoding.PreparedNativeInputs
import EffectiveEncoding.NativeInputEvaluation

open Lean Elab Command
namespace EffectiveEncodingNativeInputVerification

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

end EffectiveEncodingNativeInputVerification

run_cmd (EffectiveEncodingNativeInputVerification.checkKinds [
  ``EffectiveEncoding.unaryWordEncoding_value,
  ``EffectiveEncoding.unaryWordEncoding_canonical,
  ``EffectiveEncoding.unaryWordEncoding_length,
  ``EffectiveEncoding.unaryWordEncoding_incrementCount,
  ``EffectiveEncoding.unaryWordEncoding_incrementTrimActions,
  ``EffectiveEncoding.unaryWordEncoding_width,
  ``EffectiveEncoding.nativeMergeInputProgram_cosine_decode,
  ``EffectiveEncoding.nativeMergeInputProgram_sine_decode,
  ``EffectiveEncoding.nativeMergeInputProgram_actions,
  ``EffectiveEncoding.nativeMergeInputProgram_incrementCount,
  ``EffectiveEncoding.nativeMergeInputProgram_cosine_height,
  ``EffectiveEncoding.nativeMergeInputProgram_sine_height,
  ``EffectiveEncoding.prepareNativeAngleInput_actions,
  ``EffectiveEncoding.prepareNativeSingleInput_actions,
  ``EffectiveEncoding.extractionCode_nativeInput_preparationActions,
  ``EffectiveEncoding.preparedNativeCode_input_preparationActions
] [
  ``EffectiveEncoding.UnaryWordTrace,
  ``EffectiveEncoding.UnaryWordEncodingResult,
  ``EffectiveEncoding.unaryWordEncoding,
  ``EffectiveEncoding.UnaryWordTrace.incrementCount,
  ``EffectiveEncoding.UnaryWordTrace.incrementTrimActions,
  ``EffectiveEncoding.NativeMergeInputResult,
  ``EffectiveEncoding.nativeMergeInputProgram,
  ``EffectiveEncoding.NativeMergeInputResult.incrementTrimActions,
  ``EffectiveEncoding.NativeAtomInput,
  ``EffectiveEncoding.prepareNativeAtomInput,
  ``EffectiveEncoding.NativeAtomInput.preparationActions,
  ``EffectiveEncoding.NativeAngleInput,
  ``EffectiveEncoding.prepareNativeAngleInput,
  ``EffectiveEncoding.NativeSingleInput,
  ``EffectiveEncoding.prepareNativeSingleInput,
  ``EffectiveEncoding.NativeSingleInput.preparationActions
])

#check EffectiveEncoding.unaryWordEncoding_value
#print axioms EffectiveEncoding.unaryWordEncoding_value
#check EffectiveEncoding.unaryWordEncoding_canonical
#print axioms EffectiveEncoding.unaryWordEncoding_canonical
#check EffectiveEncoding.unaryWordEncoding_length
#print axioms EffectiveEncoding.unaryWordEncoding_length
#check EffectiveEncoding.unaryWordEncoding_incrementCount
#print axioms EffectiveEncoding.unaryWordEncoding_incrementCount
#check EffectiveEncoding.unaryWordEncoding_incrementTrimActions
#print axioms EffectiveEncoding.unaryWordEncoding_incrementTrimActions
#check EffectiveEncoding.unaryWordEncoding_width
#print axioms EffectiveEncoding.unaryWordEncoding_width
#check EffectiveEncoding.nativeMergeInputProgram_cosine_decode
#print axioms EffectiveEncoding.nativeMergeInputProgram_cosine_decode
#check EffectiveEncoding.nativeMergeInputProgram_sine_decode
#print axioms EffectiveEncoding.nativeMergeInputProgram_sine_decode
#check EffectiveEncoding.nativeMergeInputProgram_actions
#print axioms EffectiveEncoding.nativeMergeInputProgram_actions
#check EffectiveEncoding.nativeMergeInputProgram_incrementCount
#print axioms EffectiveEncoding.nativeMergeInputProgram_incrementCount
#check EffectiveEncoding.nativeMergeInputProgram_cosine_height
#print axioms EffectiveEncoding.nativeMergeInputProgram_cosine_height
#check EffectiveEncoding.nativeMergeInputProgram_sine_height
#print axioms EffectiveEncoding.nativeMergeInputProgram_sine_height
#check EffectiveEncoding.prepareNativeAngleInput_actions
#print axioms EffectiveEncoding.prepareNativeAngleInput_actions
#check EffectiveEncoding.prepareNativeSingleInput_actions
#print axioms EffectiveEncoding.prepareNativeSingleInput_actions
#check EffectiveEncoding.extractionCode_nativeInput_preparationActions
#print axioms EffectiveEncoding.extractionCode_nativeInput_preparationActions
#check EffectiveEncoding.preparedNativeCode_input_preparationActions
#print axioms EffectiveEncoding.preparedNativeCode_input_preparationActions
#check EffectiveEncoding.UnaryWordTrace
#print axioms EffectiveEncoding.UnaryWordTrace
#check EffectiveEncoding.UnaryWordEncodingResult
#print axioms EffectiveEncoding.UnaryWordEncodingResult
#check EffectiveEncoding.unaryWordEncoding
#print axioms EffectiveEncoding.unaryWordEncoding
#check EffectiveEncoding.UnaryWordTrace.incrementCount
#print axioms EffectiveEncoding.UnaryWordTrace.incrementCount
#check EffectiveEncoding.UnaryWordTrace.incrementTrimActions
#print axioms EffectiveEncoding.UnaryWordTrace.incrementTrimActions
#check EffectiveEncoding.NativeMergeInputResult
#print axioms EffectiveEncoding.NativeMergeInputResult
#check EffectiveEncoding.nativeMergeInputProgram
#print axioms EffectiveEncoding.nativeMergeInputProgram
#check EffectiveEncoding.NativeMergeInputResult.incrementTrimActions
#print axioms EffectiveEncoding.NativeMergeInputResult.incrementTrimActions
#check EffectiveEncoding.NativeAtomInput
#print axioms EffectiveEncoding.NativeAtomInput
#check EffectiveEncoding.prepareNativeAtomInput
#print axioms EffectiveEncoding.prepareNativeAtomInput
#check EffectiveEncoding.NativeAtomInput.preparationActions
#print axioms EffectiveEncoding.NativeAtomInput.preparationActions
#check EffectiveEncoding.NativeAngleInput
#print axioms EffectiveEncoding.NativeAngleInput
#check EffectiveEncoding.prepareNativeAngleInput
#print axioms EffectiveEncoding.prepareNativeAngleInput
#check EffectiveEncoding.NativeSingleInput
#print axioms EffectiveEncoding.NativeSingleInput
#check EffectiveEncoding.prepareNativeSingleInput
#print axioms EffectiveEncoding.prepareNativeSingleInput
#check EffectiveEncoding.NativeSingleInput.preparationActions
#print axioms EffectiveEncoding.NativeSingleInput.preparationActions
