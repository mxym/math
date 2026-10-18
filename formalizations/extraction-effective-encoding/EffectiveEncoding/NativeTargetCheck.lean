import EffectiveEncoding.FullyNativeExtraction
import EffectiveEncoding.NativeTargetEvaluation

open Lean Elab Command
namespace EffectiveEncodingNativeTargetVerification

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

end EffectiveEncodingNativeTargetVerification

run_cmd (EffectiveEncodingNativeTargetVerification.checkKinds [
  ``EffectiveEncoding.nativeWordMinusOne_decode,
  ``EffectiveEncoding.nativeWordZero_decode,
  ``EffectiveEncoding.prepareNativeAtomInput_cos_decode,
  ``EffectiveEncoding.prepareNativeAtomInput_sin_decode,
  ``EffectiveEncoding.nativeInputHalfCos_decode,
  ``EffectiveEncoding.nativeInputHalfSin_decode,
  ``EffectiveEncoding.prepareNativeAngleInput_cos_decode,
  ``EffectiveEncoding.prepareNativeAngleInput_sin_decode,
  ``EffectiveEncoding.prepareNativeAngleInput_half,
  ``EffectiveEncoding.nativePhaseCosExpression_decode,
  ``EffectiveEncoding.nativePhaseSinExpression_decode,
  ``EffectiveEncoding.prepareNativeSingleInput_packet_decode,
  ``EffectiveEncoding.prepareNativeSingleInput_packet_height,
  ``EffectiveEncoding.nativePreparedTargetOracle_eq,
  ``EffectiveEncoding.nativeTargetDescriptorRun_word,
  ``EffectiveEncoding.nativePreparedTarget_cache_height,
  ``EffectiveEncoding.compileNativeWord_word,
  ``EffectiveEncoding.compileNativeWord_programs_length,
  ``EffectiveEncoding.compileNativeWord_preparationActions,
  ``EffectiveEncoding.fullyNativeExtractionRun_precision,
  ``EffectiveEncoding.fullyNativeExtractionRun_word,
  ``EffectiveEncoding.fullyNativeExtractionRun_preparationActions,
  ``EffectiveEncoding.fullyNativeExtractionRun_rankWork,
  ``EffectiveEncoding.fullyNativeExtractionRun_programCount,
  ``EffectiveEncoding.fullyNativeExtractionRun_fidelity
] [
  ``EffectiveEncoding.nativeWordMinusOne,
  ``EffectiveEncoding.NativeAtomInput.cosExpression,
  ``EffectiveEncoding.NativeAtomInput.sinExpression,
  ``EffectiveEncoding.nativeInputHalfCos,
  ``EffectiveEncoding.nativeInputHalfSin,
  ``EffectiveEncoding.NativeAngleInput.cosExpression,
  ``EffectiveEncoding.NativeAngleInput.sinExpression,
  ``EffectiveEncoding.NativeAngleInput.half,
  ``EffectiveEncoding.nativePhaseCosExpression,
  ``EffectiveEncoding.nativePhaseSinExpression,
  ``EffectiveEncoding.NativeSingleInput.packetExpression,
  ``EffectiveEncoding.NativeSingleInput.packetProgram,
  ``EffectiveEncoding.NativeSingleInput.packetDataOracle,
  ``EffectiveEncoding.NativeTargetResult,
  ``EffectiveEncoding.nativeTargetDescriptorRun,
  ``EffectiveEncoding.actualNativeTargetHeightCoefficient,
  ``EffectiveEncoding.NativeCompiledLabelRun,
  ``EffectiveEncoding.compileNativeGate,
  ``EffectiveEncoding.compileNativeWord,
  ``EffectiveEncoding.NativeCompiledLabelRun.preparationActions,
  ``EffectiveEncoding.FullyNativeExtractionResult,
  ``EffectiveEncoding.fullyNativeExtractionRun
])

#check EffectiveEncoding.nativeWordMinusOne_decode
#print axioms EffectiveEncoding.nativeWordMinusOne_decode
#check EffectiveEncoding.nativeWordZero_decode
#print axioms EffectiveEncoding.nativeWordZero_decode
#check EffectiveEncoding.prepareNativeAtomInput_cos_decode
#print axioms EffectiveEncoding.prepareNativeAtomInput_cos_decode
#check EffectiveEncoding.prepareNativeAtomInput_sin_decode
#print axioms EffectiveEncoding.prepareNativeAtomInput_sin_decode
#check EffectiveEncoding.nativeInputHalfCos_decode
#print axioms EffectiveEncoding.nativeInputHalfCos_decode
#check EffectiveEncoding.nativeInputHalfSin_decode
#print axioms EffectiveEncoding.nativeInputHalfSin_decode
#check EffectiveEncoding.prepareNativeAngleInput_cos_decode
#print axioms EffectiveEncoding.prepareNativeAngleInput_cos_decode
#check EffectiveEncoding.prepareNativeAngleInput_sin_decode
#print axioms EffectiveEncoding.prepareNativeAngleInput_sin_decode
#check EffectiveEncoding.prepareNativeAngleInput_half
#print axioms EffectiveEncoding.prepareNativeAngleInput_half
#check EffectiveEncoding.nativePhaseCosExpression_decode
#print axioms EffectiveEncoding.nativePhaseCosExpression_decode
#check EffectiveEncoding.nativePhaseSinExpression_decode
#print axioms EffectiveEncoding.nativePhaseSinExpression_decode
#check EffectiveEncoding.prepareNativeSingleInput_packet_decode
#print axioms EffectiveEncoding.prepareNativeSingleInput_packet_decode
#check EffectiveEncoding.prepareNativeSingleInput_packet_height
#print axioms EffectiveEncoding.prepareNativeSingleInput_packet_height
#check EffectiveEncoding.nativePreparedTargetOracle_eq
#print axioms EffectiveEncoding.nativePreparedTargetOracle_eq
#check EffectiveEncoding.nativeTargetDescriptorRun_word
#print axioms EffectiveEncoding.nativeTargetDescriptorRun_word
#check EffectiveEncoding.nativePreparedTarget_cache_height
#print axioms EffectiveEncoding.nativePreparedTarget_cache_height
#check EffectiveEncoding.compileNativeWord_word
#print axioms EffectiveEncoding.compileNativeWord_word
#check EffectiveEncoding.compileNativeWord_programs_length
#print axioms EffectiveEncoding.compileNativeWord_programs_length
#check EffectiveEncoding.compileNativeWord_preparationActions
#print axioms EffectiveEncoding.compileNativeWord_preparationActions
#check EffectiveEncoding.fullyNativeExtractionRun_precision
#print axioms EffectiveEncoding.fullyNativeExtractionRun_precision
#check EffectiveEncoding.fullyNativeExtractionRun_word
#print axioms EffectiveEncoding.fullyNativeExtractionRun_word
#check EffectiveEncoding.fullyNativeExtractionRun_preparationActions
#print axioms EffectiveEncoding.fullyNativeExtractionRun_preparationActions
#check EffectiveEncoding.fullyNativeExtractionRun_rankWork
#print axioms EffectiveEncoding.fullyNativeExtractionRun_rankWork
#check EffectiveEncoding.fullyNativeExtractionRun_programCount
#print axioms EffectiveEncoding.fullyNativeExtractionRun_programCount
#check EffectiveEncoding.fullyNativeExtractionRun_fidelity
#print axioms EffectiveEncoding.fullyNativeExtractionRun_fidelity
#check EffectiveEncoding.nativeWordMinusOne
#print axioms EffectiveEncoding.nativeWordMinusOne
#check EffectiveEncoding.NativeAtomInput.cosExpression
#print axioms EffectiveEncoding.NativeAtomInput.cosExpression
#check EffectiveEncoding.NativeAtomInput.sinExpression
#print axioms EffectiveEncoding.NativeAtomInput.sinExpression
#check EffectiveEncoding.nativeInputHalfCos
#print axioms EffectiveEncoding.nativeInputHalfCos
#check EffectiveEncoding.nativeInputHalfSin
#print axioms EffectiveEncoding.nativeInputHalfSin
#check EffectiveEncoding.NativeAngleInput.cosExpression
#print axioms EffectiveEncoding.NativeAngleInput.cosExpression
#check EffectiveEncoding.NativeAngleInput.sinExpression
#print axioms EffectiveEncoding.NativeAngleInput.sinExpression
#check EffectiveEncoding.NativeAngleInput.half
#print axioms EffectiveEncoding.NativeAngleInput.half
#check EffectiveEncoding.nativePhaseCosExpression
#print axioms EffectiveEncoding.nativePhaseCosExpression
#check EffectiveEncoding.nativePhaseSinExpression
#print axioms EffectiveEncoding.nativePhaseSinExpression
#check EffectiveEncoding.NativeSingleInput.packetExpression
#print axioms EffectiveEncoding.NativeSingleInput.packetExpression
#check EffectiveEncoding.NativeSingleInput.packetProgram
#print axioms EffectiveEncoding.NativeSingleInput.packetProgram
#check EffectiveEncoding.NativeSingleInput.packetDataOracle
#print axioms EffectiveEncoding.NativeSingleInput.packetDataOracle
#check EffectiveEncoding.NativeTargetResult
#print axioms EffectiveEncoding.NativeTargetResult
#check EffectiveEncoding.nativeTargetDescriptorRun
#print axioms EffectiveEncoding.nativeTargetDescriptorRun
#check EffectiveEncoding.actualNativeTargetHeightCoefficient
#print axioms EffectiveEncoding.actualNativeTargetHeightCoefficient
#check EffectiveEncoding.NativeCompiledLabelRun
#print axioms EffectiveEncoding.NativeCompiledLabelRun
#check EffectiveEncoding.compileNativeGate
#print axioms EffectiveEncoding.compileNativeGate
#check EffectiveEncoding.compileNativeWord
#print axioms EffectiveEncoding.compileNativeWord
#check EffectiveEncoding.NativeCompiledLabelRun.preparationActions
#print axioms EffectiveEncoding.NativeCompiledLabelRun.preparationActions
#check EffectiveEncoding.FullyNativeExtractionResult
#print axioms EffectiveEncoding.FullyNativeExtractionResult
#check EffectiveEncoding.fullyNativeExtractionRun
#print axioms EffectiveEncoding.fullyNativeExtractionRun
