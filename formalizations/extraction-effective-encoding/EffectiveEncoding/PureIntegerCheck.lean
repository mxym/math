import EffectiveEncoding.PureIntegerBudgets

open Lean Elab Command
namespace EffectiveEncodingPureIntegerVerification

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

end EffectiveEncodingPureIntegerVerification

run_cmd (EffectiveEncodingPureIntegerVerification.checkKinds [
  ``EffectiveEncoding.integerScalar_ext_value,
  ``EffectiveEncoding.integerLiteral_zero,
  ``EffectiveEncoding.integerLiteral_one,
  ``EffectiveEncoding.integerLiteral_half,
  ``EffectiveEncoding.integerLiteral_halfInv,
  ``EffectiveEncoding.integerRoot_congr_value,
  ``EffectiveEncoding.rawAtomCos_eq,
  ``EffectiveEncoding.rawAtomSin_eq,
  ``EffectiveEncoding.rawHalfCos_eq,
  ``EffectiveEncoding.rawHalfSin_eq,
  ``EffectiveEncoding.AngleCode.rawCos_eq,
  ``EffectiveEncoding.AngleCode.rawSin_eq,
  ``EffectiveEncoding.rawPhaseCos_eq,
  ``EffectiveEncoding.rawPhaseSin_eq,
  ``EffectiveEncoding.SingleCode.rawPacket_eq,
  ``EffectiveEncoding.SingleCode.rawPacket_value,
  ``EffectiveEncoding.extractionCode_rawPacket_height,
  ``EffectiveEncoding.rawPacketCache_value,
  ``EffectiveEncoding.rawPacketCache_expression_value,
  ``EffectiveEncoding.rawCachedIntegerRun_word,
  ``EffectiveEncoding.rawDescriptorRun_word,
  ``EffectiveEncoding.rawExtractionCode_eq,
  ``EffectiveEncoding.rawExtractionCode_uses,
  ``EffectiveEncoding.rawExtractionCode_length,
  ``EffectiveEncoding.rawExtractionCode_error,
  ``EffectiveEncoding.rawExtractionCode_fidelity,
  ``EffectiveEncoding.rawPacketCache_height,
  ``EffectiveEncoding.rawCachedIntegerRun_integerBitBudget,
  ``EffectiveEncoding.rawBudget_double,
  ``EffectiveEncoding.rawDescriptorRun_integerBitBudget,
  ``EffectiveEncoding.rawDescriptorRun_polynomial,
  ``EffectiveEncoding.rawExtraction_expression_budget,
  ``EffectiveEncoding.rawExtraction_expression_subtreeBound,
  ``EffectiveEncoding.rawExtraction_integerProgramRun_height
] [
  ``EffectiveEncoding.integerFraction,
  ``EffectiveEncoding.integerHalf,
  ``EffectiveEncoding.rawAtomCos,
  ``EffectiveEncoding.rawAtomSin,
  ``EffectiveEncoding.RawScalarOracle,
  ``EffectiveEncoding.rawHalfCos,
  ``EffectiveEncoding.rawHalfSin,
  ``EffectiveEncoding.AngleCode.rawCos,
  ``EffectiveEncoding.AngleCode.rawSin,
  ``EffectiveEncoding.rawPhaseCos,
  ``EffectiveEncoding.rawPhaseSin,
  ``EffectiveEncoding.SingleCode.rawPacket,
  ``EffectiveEncoding.buildRawPacketCache,
  ``EffectiveEncoding.readRawPacketCache,
  ``EffectiveEncoding.rawCachedIntegerRun,
  ``EffectiveEncoding.rawDescriptorRun,
  ``EffectiveEncoding.rawExtractionCode
])

#check EffectiveEncoding.integerScalar_ext_value
#print axioms EffectiveEncoding.integerScalar_ext_value
#check EffectiveEncoding.integerLiteral_zero
#print axioms EffectiveEncoding.integerLiteral_zero
#check EffectiveEncoding.integerLiteral_one
#print axioms EffectiveEncoding.integerLiteral_one
#check EffectiveEncoding.integerLiteral_half
#print axioms EffectiveEncoding.integerLiteral_half
#check EffectiveEncoding.integerLiteral_halfInv
#print axioms EffectiveEncoding.integerLiteral_halfInv
#check EffectiveEncoding.integerRoot_congr_value
#print axioms EffectiveEncoding.integerRoot_congr_value
#check EffectiveEncoding.rawAtomCos_eq
#print axioms EffectiveEncoding.rawAtomCos_eq
#check EffectiveEncoding.rawAtomSin_eq
#print axioms EffectiveEncoding.rawAtomSin_eq
#check EffectiveEncoding.rawHalfCos_eq
#print axioms EffectiveEncoding.rawHalfCos_eq
#check EffectiveEncoding.rawHalfSin_eq
#print axioms EffectiveEncoding.rawHalfSin_eq
#check EffectiveEncoding.AngleCode.rawCos_eq
#print axioms EffectiveEncoding.AngleCode.rawCos_eq
#check EffectiveEncoding.AngleCode.rawSin_eq
#print axioms EffectiveEncoding.AngleCode.rawSin_eq
#check EffectiveEncoding.rawPhaseCos_eq
#print axioms EffectiveEncoding.rawPhaseCos_eq
#check EffectiveEncoding.rawPhaseSin_eq
#print axioms EffectiveEncoding.rawPhaseSin_eq
#check EffectiveEncoding.SingleCode.rawPacket_eq
#print axioms EffectiveEncoding.SingleCode.rawPacket_eq
#check EffectiveEncoding.SingleCode.rawPacket_value
#print axioms EffectiveEncoding.SingleCode.rawPacket_value
#check EffectiveEncoding.extractionCode_rawPacket_height
#print axioms EffectiveEncoding.extractionCode_rawPacket_height
#check EffectiveEncoding.rawPacketCache_value
#print axioms EffectiveEncoding.rawPacketCache_value
#check EffectiveEncoding.rawPacketCache_expression_value
#print axioms EffectiveEncoding.rawPacketCache_expression_value
#check EffectiveEncoding.rawCachedIntegerRun_word
#print axioms EffectiveEncoding.rawCachedIntegerRun_word
#check EffectiveEncoding.rawDescriptorRun_word
#print axioms EffectiveEncoding.rawDescriptorRun_word
#check EffectiveEncoding.rawExtractionCode_eq
#print axioms EffectiveEncoding.rawExtractionCode_eq
#check EffectiveEncoding.rawExtractionCode_uses
#print axioms EffectiveEncoding.rawExtractionCode_uses
#check EffectiveEncoding.rawExtractionCode_length
#print axioms EffectiveEncoding.rawExtractionCode_length
#check EffectiveEncoding.rawExtractionCode_error
#print axioms EffectiveEncoding.rawExtractionCode_error
#check EffectiveEncoding.rawExtractionCode_fidelity
#print axioms EffectiveEncoding.rawExtractionCode_fidelity
#check EffectiveEncoding.rawPacketCache_height
#print axioms EffectiveEncoding.rawPacketCache_height
#check EffectiveEncoding.rawCachedIntegerRun_integerBitBudget
#print axioms EffectiveEncoding.rawCachedIntegerRun_integerBitBudget
#check EffectiveEncoding.rawBudget_double
#print axioms EffectiveEncoding.rawBudget_double
#check EffectiveEncoding.rawDescriptorRun_integerBitBudget
#print axioms EffectiveEncoding.rawDescriptorRun_integerBitBudget
#check EffectiveEncoding.rawDescriptorRun_polynomial
#print axioms EffectiveEncoding.rawDescriptorRun_polynomial
#check EffectiveEncoding.rawExtraction_expression_budget
#print axioms EffectiveEncoding.rawExtraction_expression_budget
#check EffectiveEncoding.rawExtraction_expression_subtreeBound
#print axioms EffectiveEncoding.rawExtraction_expression_subtreeBound
#check EffectiveEncoding.rawExtraction_integerProgramRun_height
#print axioms EffectiveEncoding.rawExtraction_integerProgramRun_height
#check EffectiveEncoding.integerFraction
#print axioms EffectiveEncoding.integerFraction
#check EffectiveEncoding.integerHalf
#print axioms EffectiveEncoding.integerHalf
#check EffectiveEncoding.rawAtomCos
#print axioms EffectiveEncoding.rawAtomCos
#check EffectiveEncoding.rawAtomSin
#print axioms EffectiveEncoding.rawAtomSin
#check EffectiveEncoding.RawScalarOracle
#print axioms EffectiveEncoding.RawScalarOracle
#check EffectiveEncoding.rawHalfCos
#print axioms EffectiveEncoding.rawHalfCos
#check EffectiveEncoding.rawHalfSin
#print axioms EffectiveEncoding.rawHalfSin
#check EffectiveEncoding.AngleCode.rawCos
#print axioms EffectiveEncoding.AngleCode.rawCos
#check EffectiveEncoding.AngleCode.rawSin
#print axioms EffectiveEncoding.AngleCode.rawSin
#check EffectiveEncoding.rawPhaseCos
#print axioms EffectiveEncoding.rawPhaseCos
#check EffectiveEncoding.rawPhaseSin
#print axioms EffectiveEncoding.rawPhaseSin
#check EffectiveEncoding.SingleCode.rawPacket
#print axioms EffectiveEncoding.SingleCode.rawPacket
#check EffectiveEncoding.buildRawPacketCache
#print axioms EffectiveEncoding.buildRawPacketCache
#check EffectiveEncoding.readRawPacketCache
#print axioms EffectiveEncoding.readRawPacketCache
#check EffectiveEncoding.rawCachedIntegerRun
#print axioms EffectiveEncoding.rawCachedIntegerRun
#check EffectiveEncoding.rawDescriptorRun
#print axioms EffectiveEncoding.rawDescriptorRun
#check EffectiveEncoding.rawExtractionCode
#print axioms EffectiveEncoding.rawExtractionCode
