import EffectiveEncoding.NativeBinaryRankEndpoints
import EffectiveEncoding.BinaryRankEndpointEvaluation

open Lean Elab Command
namespace EffectiveEncodingBinaryRankEndpointVerification

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

end EffectiveEncodingBinaryRankEndpointVerification

run_cmd (EffectiveEncodingBinaryRankEndpointVerification.checkKinds [
  ``EffectiveEncoding.endpointBitsProgram_get,
  ``EffectiveEncoding.binaryWordValue_testBit_getD,
  ``EffectiveEncoding.endpointBitsProgram_listActions,
  ``EffectiveEncoding.nativeBinaryRankProgram_erase,
  ``EffectiveEncoding.nativeBinaryRankProgram_encodingActions,
  ``EffectiveEncoding.nativeBinaryRankProgram_encodingActions_polynomial
] [
  ``EffectiveEncoding.EndpointBitTrace,
  ``EffectiveEncoding.EndpointBitsResult,
  ``EffectiveEncoding.endpointBitsProgram,
  ``EffectiveEncoding.EndpointBitTrace.listActions,
  ``EffectiveEncoding.NativeBinaryRankResult,
  ``EffectiveEncoding.nativeBinaryRankProgram,
  ``EffectiveEncoding.NativeBinaryRankResult.erase,
  ``EffectiveEncoding.NativeBinaryRankResult.encodingActions
])

#check EffectiveEncoding.endpointBitsProgram_get
#print axioms EffectiveEncoding.endpointBitsProgram_get
#check EffectiveEncoding.binaryWordValue_testBit_getD
#print axioms EffectiveEncoding.binaryWordValue_testBit_getD
#check EffectiveEncoding.endpointBitsProgram_listActions
#print axioms EffectiveEncoding.endpointBitsProgram_listActions
#check EffectiveEncoding.nativeBinaryRankProgram_erase
#print axioms EffectiveEncoding.nativeBinaryRankProgram_erase
#check EffectiveEncoding.nativeBinaryRankProgram_encodingActions
#print axioms EffectiveEncoding.nativeBinaryRankProgram_encodingActions
#check EffectiveEncoding.nativeBinaryRankProgram_encodingActions_polynomial
#print axioms EffectiveEncoding.nativeBinaryRankProgram_encodingActions_polynomial
#check EffectiveEncoding.EndpointBitTrace
#print axioms EffectiveEncoding.EndpointBitTrace
#check EffectiveEncoding.EndpointBitsResult
#print axioms EffectiveEncoding.EndpointBitsResult
#check EffectiveEncoding.endpointBitsProgram
#print axioms EffectiveEncoding.endpointBitsProgram
#check EffectiveEncoding.EndpointBitTrace.listActions
#print axioms EffectiveEncoding.EndpointBitTrace.listActions
#check EffectiveEncoding.NativeBinaryRankResult
#print axioms EffectiveEncoding.NativeBinaryRankResult
#check EffectiveEncoding.nativeBinaryRankProgram
#print axioms EffectiveEncoding.nativeBinaryRankProgram
#check EffectiveEncoding.NativeBinaryRankResult.erase
#print axioms EffectiveEncoding.NativeBinaryRankResult.erase
#check EffectiveEncoding.NativeBinaryRankResult.encodingActions
#print axioms EffectiveEncoding.NativeBinaryRankResult.encodingActions
