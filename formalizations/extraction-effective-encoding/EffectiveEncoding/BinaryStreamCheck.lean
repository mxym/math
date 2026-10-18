import EffectiveEncoding.SerializedInputExtraction
import EffectiveEncoding.BinaryStreamEvaluation

open Lean Elab Command
namespace EffectiveEncodingBinaryStreamVerification

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

end EffectiveEncodingBinaryStreamVerification

run_cmd (EffectiveEncodingBinaryStreamVerification.checkKinds [
  ``EffectiveEncoding.vectorBool_getD,
  ``EffectiveEncoding.endpointBitsProgram_value,
  ``EffectiveEncoding.binaryFieldProgram_length,
  ``EffectiveEncoding.binaryFieldProgram_value,
  ``EffectiveEncoding.binaryFieldProgram_actions,
  ``EffectiveEncoding.takeBoolField_append,
  ``EffectiveEncoding.takeBoolField_binaryField,
  ``EffectiveEncoding.readBinaryLabel_roundtrip,
  ``EffectiveEncoding.binaryLabelProgram_length,
  ``EffectiveEncoding.binaryLabelProgram_actions,
  ``EffectiveEncoding.readBinaryLabelStreamFuel_roundtrip,
  ``EffectiveEncoding.binaryLabelStream_length,
  ``EffectiveEncoding.readBinaryLabelStream_roundtrip,
  ``EffectiveEncoding.deserializeLabelStream_roundtrip,
  ``EffectiveEncoding.binaryLabelStream_actions,
  ``EffectiveEncoding.compileAssembledWord_outputLength,
  ``EffectiveEncoding.fullyMaterializedInputRun_outputLength,
  ``EffectiveEncoding.serializedInputRun_roundtrip,
  ``EffectiveEncoding.serializedInputRun_suffix_roundtrip,
  ``EffectiveEncoding.serializedInputRun_bitLength,
  ``EffectiveEncoding.serializedInputRun_streamActions,
  ``EffectiveEncoding.serializedInputRun_accountedPrimitiveActions,
  ``EffectiveEncoding.serializedInputRun_fidelity
] [
  ``EffectiveEncoding.BinaryFieldResult,
  ``EffectiveEncoding.binaryFieldProgram,
  ``EffectiveEncoding.BinaryFieldResult.actions,
  ``EffectiveEncoding.takeBoolField,
  ``EffectiveEncoding.labelFieldWidth,
  ``EffectiveEncoding.BinaryLabelResult,
  ``EffectiveEncoding.binaryLabelProgram,
  ``EffectiveEncoding.readBinaryLabel,
  ``EffectiveEncoding.BinaryLabelResult.actions,
  ``EffectiveEncoding.BinaryStreamTrace,
  ``EffectiveEncoding.BinaryStreamResult,
  ``EffectiveEncoding.binaryLabelStream,
  ``EffectiveEncoding.readBinaryLabelStreamFuel,
  ``EffectiveEncoding.readBinaryLabelStream,
  ``EffectiveEncoding.deserializeLabelStream,
  ``EffectiveEncoding.BinaryStreamTrace.actions,
  ``EffectiveEncoding.outputLabelBudget,
  ``EffectiveEncoding.SerializedInputResult,
  ``EffectiveEncoding.serializedInputRun,
  ``EffectiveEncoding.SerializedInputResult.decoded,
  ``EffectiveEncoding.SerializedInputResult.accountedPrimitiveActions,
  ``EffectiveEncoding.serializedPrimitiveBudget
])

#check EffectiveEncoding.vectorBool_getD
#print axioms EffectiveEncoding.vectorBool_getD
#check EffectiveEncoding.endpointBitsProgram_value
#print axioms EffectiveEncoding.endpointBitsProgram_value
#check EffectiveEncoding.binaryFieldProgram_length
#print axioms EffectiveEncoding.binaryFieldProgram_length
#check EffectiveEncoding.binaryFieldProgram_value
#print axioms EffectiveEncoding.binaryFieldProgram_value
#check EffectiveEncoding.binaryFieldProgram_actions
#print axioms EffectiveEncoding.binaryFieldProgram_actions
#check EffectiveEncoding.takeBoolField_append
#print axioms EffectiveEncoding.takeBoolField_append
#check EffectiveEncoding.takeBoolField_binaryField
#print axioms EffectiveEncoding.takeBoolField_binaryField
#check EffectiveEncoding.readBinaryLabel_roundtrip
#print axioms EffectiveEncoding.readBinaryLabel_roundtrip
#check EffectiveEncoding.binaryLabelProgram_length
#print axioms EffectiveEncoding.binaryLabelProgram_length
#check EffectiveEncoding.binaryLabelProgram_actions
#print axioms EffectiveEncoding.binaryLabelProgram_actions
#check EffectiveEncoding.readBinaryLabelStreamFuel_roundtrip
#print axioms EffectiveEncoding.readBinaryLabelStreamFuel_roundtrip
#check EffectiveEncoding.binaryLabelStream_length
#print axioms EffectiveEncoding.binaryLabelStream_length
#check EffectiveEncoding.readBinaryLabelStream_roundtrip
#print axioms EffectiveEncoding.readBinaryLabelStream_roundtrip
#check EffectiveEncoding.deserializeLabelStream_roundtrip
#print axioms EffectiveEncoding.deserializeLabelStream_roundtrip
#check EffectiveEncoding.binaryLabelStream_actions
#print axioms EffectiveEncoding.binaryLabelStream_actions
#check EffectiveEncoding.compileAssembledWord_outputLength
#print axioms EffectiveEncoding.compileAssembledWord_outputLength
#check EffectiveEncoding.fullyMaterializedInputRun_outputLength
#print axioms EffectiveEncoding.fullyMaterializedInputRun_outputLength
#check EffectiveEncoding.serializedInputRun_roundtrip
#print axioms EffectiveEncoding.serializedInputRun_roundtrip
#check EffectiveEncoding.serializedInputRun_suffix_roundtrip
#print axioms EffectiveEncoding.serializedInputRun_suffix_roundtrip
#check EffectiveEncoding.serializedInputRun_bitLength
#print axioms EffectiveEncoding.serializedInputRun_bitLength
#check EffectiveEncoding.serializedInputRun_streamActions
#print axioms EffectiveEncoding.serializedInputRun_streamActions
#check EffectiveEncoding.serializedInputRun_accountedPrimitiveActions
#print axioms EffectiveEncoding.serializedInputRun_accountedPrimitiveActions
#check EffectiveEncoding.serializedInputRun_fidelity
#print axioms EffectiveEncoding.serializedInputRun_fidelity
#check EffectiveEncoding.BinaryFieldResult
#print axioms EffectiveEncoding.BinaryFieldResult
#check EffectiveEncoding.binaryFieldProgram
#print axioms EffectiveEncoding.binaryFieldProgram
#check EffectiveEncoding.BinaryFieldResult.actions
#print axioms EffectiveEncoding.BinaryFieldResult.actions
#check EffectiveEncoding.takeBoolField
#print axioms EffectiveEncoding.takeBoolField
#check EffectiveEncoding.labelFieldWidth
#print axioms EffectiveEncoding.labelFieldWidth
#check EffectiveEncoding.BinaryLabelResult
#print axioms EffectiveEncoding.BinaryLabelResult
#check EffectiveEncoding.binaryLabelProgram
#print axioms EffectiveEncoding.binaryLabelProgram
#check EffectiveEncoding.readBinaryLabel
#print axioms EffectiveEncoding.readBinaryLabel
#check EffectiveEncoding.BinaryLabelResult.actions
#print axioms EffectiveEncoding.BinaryLabelResult.actions
#check EffectiveEncoding.BinaryStreamTrace
#print axioms EffectiveEncoding.BinaryStreamTrace
#check EffectiveEncoding.BinaryStreamResult
#print axioms EffectiveEncoding.BinaryStreamResult
#check EffectiveEncoding.binaryLabelStream
#print axioms EffectiveEncoding.binaryLabelStream
#check EffectiveEncoding.readBinaryLabelStreamFuel
#print axioms EffectiveEncoding.readBinaryLabelStreamFuel
#check EffectiveEncoding.readBinaryLabelStream
#print axioms EffectiveEncoding.readBinaryLabelStream
#check EffectiveEncoding.deserializeLabelStream
#print axioms EffectiveEncoding.deserializeLabelStream
#check EffectiveEncoding.BinaryStreamTrace.actions
#print axioms EffectiveEncoding.BinaryStreamTrace.actions
#check EffectiveEncoding.outputLabelBudget
#print axioms EffectiveEncoding.outputLabelBudget
#check EffectiveEncoding.SerializedInputResult
#print axioms EffectiveEncoding.SerializedInputResult
#check EffectiveEncoding.serializedInputRun
#print axioms EffectiveEncoding.serializedInputRun
#check EffectiveEncoding.SerializedInputResult.decoded
#print axioms EffectiveEncoding.SerializedInputResult.decoded
#check EffectiveEncoding.SerializedInputResult.accountedPrimitiveActions
#print axioms EffectiveEncoding.SerializedInputResult.accountedPrimitiveActions
#check EffectiveEncoding.serializedPrimitiveBudget
#print axioms EffectiveEncoding.serializedPrimitiveBudget
