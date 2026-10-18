import EffectiveEncoding
import Lean

open Lean Elab Command
namespace EffectiveEncodingVerification

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

end EffectiveEncodingVerification

run_cmd (EffectiveEncodingVerification.checkKinds [
  ``EffectiveEncoding.mergeAngle_degenerate,
  ``EffectiveEncoding.AngleAtom.cosOracle_correct,
  ``EffectiveEncoding.AngleAtom.sinOracle_correct,
  ``EffectiveEncoding.AngleAtom.value_bounds,
  ``EffectiveEncoding.AngleCode.cosOracle_correct,
  ``EffectiveEncoding.AngleCode.sinOracle_correct,
  ``EffectiveEncoding.AngleCode.evaluation,
  ``EffectiveEncoding.interpret_flatMap,
  ``EffectiveEncoding.allBranchCode_action,
  ``EffectiveEncoding.allBranchCode_length,
  ``EffectiveEncoding.occupationStepCode_action,
  ``EffectiveEncoding.occupationStepCode_length,
  ``EffectiveEncoding.prefixCode_length,
  ``EffectiveEncoding.interpret_prefix,
  ``EffectiveEncoding.shiftCode_length,
  ``EffectiveEncoding.interpret_shift,
  ``EffectiveEncoding.stageCircuit_action,
  ``EffectiveEncoding.compressionCircuit_succ,
  ``EffectiveEncoding.bitOccupation_zero,
  ``EffectiveEncoding.compressionCircuit_action,
  ``EffectiveEncoding.stageCode_length,
  ``EffectiveEncoding.compressionCode_length,
  ``EffectiveEncoding.compressionCircuit_matrix,
  ``EffectiveEncoding.compressionCircuit_coherent,
  ``EffectiveEncoding.compressionCircuit_purePower,
  ``EffectiveEncoding.AngleCode.neg_value,
  ``EffectiveEncoding.AngleCode.half_value,
  ``EffectiveEncoding.piCode_value,
  ``EffectiveEncoding.GateCode.inverse_value,
  ``EffectiveEncoding.interpret_length,
  ``EffectiveEncoding.interpret_append,
  ``EffectiveEncoding.interpret_reverse,
  ``EffectiveEncoding.reverseCode_length,
  ``EffectiveEncoding.maskOfBits_injective,
  ``EffectiveEncoding.maskIndex_injective,
  ``EffectiveEncoding.masks_nodup,
  ``EffectiveEncoding.mem_masks,
  ``EffectiveEncoding.masks_length,
  ``EffectiveEncoding.masks_perm,
  ``EffectiveEncoding.controls_length,
  ``EffectiveEncoding.controls_character,
  ``EffectiveEncoding.interpret_cnotCode,
  ``EffectiveEncoding.parityCode_action,
  ``EffectiveEncoding.parityCode_length,
  ``EffectiveEncoding.pauliCode_action,
  ``EffectiveEncoding.pauliCode_length,
  ``EffectiveEncoding.signedCode_value,
  ``EffectiveEncoding.maskParity_sign,
  ``EffectiveEncoding.run_pauliCodes,
  ``EffectiveEncoding.selectedCode_action,
  ``EffectiveEncoding.selectedCode_length,
  ``EffectiveEncoding.mem_triples,
  ``EffectiveEncoding.triples_nodup,
  ``EffectiveEncoding.fromTriple_count_zero,
  ``EffectiveEncoding.fromTriple_count_one,
  ``EffectiveEncoding.fromTriple_count_two,
  ``EffectiveEncoding.fromTriple_count_three,
  ``EffectiveEncoding.count_total,
  ``EffectiveEncoding.toTriple_le,
  ``EffectiveEncoding.toTriple_fromTriple,
  ``EffectiveEncoding.fromTriple_toTriple,
  ``EffectiveEncoding.occupations_nodup,
  ``EffectiveEncoding.mem_occupations,
  ``EffectiveEncoding.occupations_length,
  ``EffectiveEncoding.unrank_rank,
  ``EffectiveEncoding.rank_unrank,
  ``EffectiveEncoding.boundedBits_injective,
  ``EffectiveEncoding.rank_fits,
  ``EffectiveEncoding.find_unique,
  ``EffectiveEncoding.decode_encode,
  ``EffectiveEncoding.decode_some_iff,
  ``EffectiveEncoding.enumeration_candidate_bound,
  ``EffectiveEncoding.compactEncoding_testBit,
  ``EffectiveEncoding.originalEncoding_high_zero,
  ``EffectiveEncoding.interpret_cast,
  ``EffectiveEncoding.castCode_length,
  ``EffectiveEncoding.interpret_bellPreparationCode,
  ``EffectiveEncoding.interpret_bellPairsCode,
  ``EffectiveEncoding.extractionCircuit_eq,
  ``EffectiveEncoding.extractionCircuit_gate,
  ``EffectiveEncoding.extractionCircuit_coherent,
  ``EffectiveEncoding.extractionCircuit_purePower,
  ``EffectiveEncoding.extractionCode_length,
  ``EffectiveEncoding.extractionCode_polynomial_bound,
  ``EffectiveEncoding.extractionCircuit_polynomial_bound,
  ``EffectiveEncoding.extractionVector_readout,
  ``EffectiveEncoding.garbageVector_square,
  ``EffectiveEncoding.extractionOutput_coherent,
  ``EffectiveEncoding.extractionOutput_purePower,
  ``EffectiveEncoding.wireLabels_value,
  ``EffectiveEncoding.labelCircuit_flatMap,
  ``EffectiveEncoding.labelCircuit_uses,
  ``EffectiveEncoding.compileLabels_error,
  ``EffectiveEncoding.compileLabelWord_error,
  ``EffectiveEncoding.compileLabels_length,
  ``EffectiveEncoding.compileLabelWord_length,
  ``EffectiveEncoding.extractionOutput_fidelity_one,
  ``EffectiveEncoding.extractionOutput_robust,
  ``EffectiveEncoding.extractionOutput_robust_up_to_phase,
  ``EffectiveEncoding.finiteLabels_fidelity,
  ``EffectiveEncoding.selectedCode_run_eq,
  ``EffectiveEncoding.adjacentSwapCode_run_eq,
  ``EffectiveEncoding.adjacentSwapCode_length,
  ``EffectiveEncoding.adjacentRotationCode_run_eq,
  ``EffectiveEncoding.adjacentRotationCode_length,
  ``EffectiveEncoding.orientedRotationCode_run_eq,
  ``EffectiveEncoding.mem_otherWires,
  ``EffectiveEncoding.otherWires_length,
  ``EffectiveEncoding.differing_exists,
  ``EffectiveEncoding.differingWire_spec,
  ``EffectiveEncoding.clearBits_otherWires,
  ``EffectiveEncoding.moveCode_run_eq,
  ``EffectiveEncoding.moveCode_length,
  ``EffectiveEncoding.swapCode_action,
  ``EffectiveEncoding.swapCode_length,
  ``EffectiveEncoding.rotationCode_action,
  ``EffectiveEncoding.rotationCode_length,
  ``EffectiveEncoding.GateCode.globalPhase_norm,
  ``EffectiveEncoding.GateCode.representative_spec,
  ``EffectiveEncoding.wordPhase_norm,
  ``EffectiveEncoding.interpret_cons,
  ``EffectiveEncoding.representativeCircuit_cons,
  ``EffectiveEncoding.representativeCircuit_phase,
  ``EffectiveEncoding.descriptor_word_error,
  ``EffectiveEncoding.descriptor_word_uniform_error,
  ``EffectiveEncoding.descriptorSynthesis_spec,
  ``EffectiveEncoding.numericalExtractionCode_uses,
  ``EffectiveEncoding.numericalExtractionCode_error,
  ``EffectiveEncoding.numericalExtractionCode_length,
  ``EffectiveEncoding.numericalExtractionCode_fidelity,
  ``EffectiveEncoding.descriptorArithmeticOperations_bound,
  ``EffectiveEncoding.extractionArithmeticOperations_bound,
  ``EffectiveEncoding.numericalExtraction_from_universal,
  ``EffectiveEncoding.countProgram_length,
  ``EffectiveEncoding.countProgram_sparse,
  ``EffectiveEncoding.indexedCount_image,
  ``EffectiveEncoding.indexedCount_ratio,
  ``EffectiveEncoding.explicitOthers_perm,
  ``EffectiveEncoding.explicitOthers_nodup,
  ``EffectiveEncoding.explicitOthers_length,
  ``EffectiveEncoding.integerIndexedCode_raw,
  ``EffectiveEncoding.integerIndexedCode_action,
  ``EffectiveEncoding.integerIndexedCode_fixes_zero,
  ``EffectiveEncoding.integerIndexedCode_length,
  ``EffectiveEncoding.branchEmbedding_eq,
  ``EffectiveEncoding.branchCode_action,
  ``EffectiveEncoding.branchCode_fixes_other,
  ``EffectiveEncoding.branchCode_fixes_other_pivot,
  ``EffectiveEncoding.branchCode_length,
  ``EffectiveEncoding.swapCode_denote,
  ``EffectiveEncoding.rotationCode_denote_eq,
  ``EffectiveEncoding.mergeCode_value,
  ``EffectiveEncoding.RawCode.compile_denote,
  ``EffectiveEncoding.RawCode.compile_length,
  ``EffectiveEncoding.compileRaw_denote,
  ``EffectiveEncoding.compileRaw_length,
  ``EffectiveEncoding.alignmentPerm_complete,
  ``EffectiveEncoding.alignmentCode_action,
  ``EffectiveEncoding.alignmentCode_length,
  ``EffectiveEncoding.alignmentCode_on_embedding,
  ``EffectiveEncoding.star_complexPhase,
  ``EffectiveEncoding.phaseRepresentative_bool,
  ``EffectiveEncoding.su2ToBool_star,
  ``EffectiveEncoding.SingleCode.globalPhase_norm,
  ``EffectiveEncoding.SingleCode.representative_spec,
  ``EffectiveEncoding.quaternionCoordinates_star,
  ``EffectiveEncoding.sqrt_half_eq_invSqrtTwo,
  ``EffectiveEncoding.invSqrtTwoOracle_correct,
  ``EffectiveEncoding.phaseCosOracle_correct,
  ``EffectiveEncoding.phaseSinOracle_correct,
  ``EffectiveEncoding.quaternionStarOracle_correct,
  ``EffectiveEncoding.coordinatePacket_correct,
  ``EffectiveEncoding.hadRepresentative_coordinates,
  ``EffectiveEncoding.phaseRepresentative_coordinates,
  ``EffectiveEncoding.SingleCode.quaternionOracle_correct
] [
  ``EffectiveEncoding.AngleAtom.cosOracle,
  ``EffectiveEncoding.AngleAtom.sinOracle,
  ``EffectiveEncoding.AngleCode.cosOracle,
  ``EffectiveEncoding.AngleCode.sinOracle,
  ``EffectiveEncoding.allBranchCode,
  ``EffectiveEncoding.occupationStepCode,
  ``EffectiveEncoding.GateCode.extend,
  ``EffectiveEncoding.prefixCode,
  ``EffectiveEncoding.GateCode.shift,
  ``EffectiveEncoding.shiftCode,
  ``EffectiveEncoding.stageCode,
  ``EffectiveEncoding.stageCircuit,
  ``EffectiveEncoding.compressionCode,
  ``EffectiveEncoding.compressionCircuit,
  ``EffectiveEncoding.AngleAtom,
  ``EffectiveEncoding.AngleCode,
  ``EffectiveEncoding.AngleAtom.value,
  ``EffectiveEncoding.AngleCode.value,
  ``EffectiveEncoding.AngleCode.neg,
  ``EffectiveEncoding.AngleCode.half,
  ``EffectiveEncoding.piCode,
  ``EffectiveEncoding.SingleCode,
  ``EffectiveEncoding.SingleCode.value,
  ``EffectiveEncoding.GateCode,
  ``EffectiveEncoding.GateCode.value,
  ``EffectiveEncoding.GateCode.inverse,
  ``EffectiveEncoding.WordCode,
  ``EffectiveEncoding.interpret,
  ``EffectiveEncoding.reverseCode,
  ``EffectiveEncoding.maskOfBits,
  ``EffectiveEncoding.masks,
  ``EffectiveEncoding.controls,
  ``EffectiveEncoding.cnotCode,
  ``EffectiveEncoding.parityCode,
  ``EffectiveEncoding.pauliCode,
  ``EffectiveEncoding.signedCode,
  ``EffectiveEncoding.maskParity,
  ``EffectiveEncoding.selectedCode,
  ``EffectiveEncoding.Triple,
  ``EffectiveEncoding.total,
  ``EffectiveEncoding.triples,
  ``EffectiveEncoding.fromTriple,
  ``EffectiveEncoding.toTriple,
  ``EffectiveEncoding.occupations,
  ``EffectiveEncoding.rank,
  ``EffectiveEncoding.unrank,
  ``EffectiveEncoding.rankEquiv,
  ``EffectiveEncoding.boundedBits,
  ``EffectiveEncoding.compactEncoding,
  ``EffectiveEncoding.originalEncoding,
  ``EffectiveEncoding.nextEncoding,
  ``EffectiveEncoding.decode,
  ``EffectiveEncoding.castCode,
  ``EffectiveEncoding.bellPreparationCode,
  ``EffectiveEncoding.bellPairsCode,
  ``EffectiveEncoding.extractionCode,
  ``EffectiveEncoding.extractionCircuit,
  ``EffectiveEncoding.extractionVector,
  ``EffectiveEncoding.garbageVector,
  ``EffectiveEncoding.extractionOutput,
  ``EffectiveEncoding.LabelGate,
  ``EffectiveEncoding.LabelGate.value,
  ``EffectiveEncoding.labelCircuit,
  ``EffectiveEncoding.wireLabels,
  ``EffectiveEncoding.compileLabels,
  ``EffectiveEncoding.compileLabelWord,
  ``EffectiveEncoding.adjacentSwapCode,
  ``EffectiveEncoding.adjacentRotationCode,
  ``EffectiveEncoding.orientedRotationCode,
  ``EffectiveEncoding.otherWires,
  ``EffectiveEncoding.differingWire,
  ``EffectiveEncoding.moveCode,
  ``EffectiveEncoding.swapCode,
  ``EffectiveEncoding.rotationCode,
  ``EffectiveEncoding.GateCode.representative,
  ``EffectiveEncoding.GateCode.globalPhase,
  ``EffectiveEncoding.representativeCircuit,
  ``EffectiveEncoding.wordPhase,
  ``EffectiveEncoding.descriptorSynthesis,
  ``EffectiveEncoding.extractionPrecision,
  ``EffectiveEncoding.numericalExtractionCode,
  ``EffectiveEncoding.descriptorArithmeticOperations,
  ``EffectiveEncoding.gateArithmeticOperations,
  ``EffectiveEncoding.extractionArithmeticOperations,
  ``EffectiveEncoding.countProgram,
  ``EffectiveEncoding.indexedCount,
  ``EffectiveEncoding.explicitOthers,
  ``EffectiveEncoding.integerIndexedCode,
  ``EffectiveEncoding.occupiedPivot,
  ``EffectiveEncoding.branchEmbedding,
  ``EffectiveEncoding.pivotCoordinates,
  ``EffectiveEncoding.pivotEmbedding,
  ``EffectiveEncoding.branchCode,
  ``EffectiveEncoding.RawCode,
  ``EffectiveEncoding.mergeCode,
  ``EffectiveEncoding.RawCode.value,
  ``EffectiveEncoding.RawCode.compile,
  ``EffectiveEncoding.compileRaw,
  ``EffectiveEncoding.alignmentPerm,
  ``EffectiveEncoding.alignmentCode,
  ``EffectiveEncoding.hadRepresentative,
  ``EffectiveEncoding.yRepresentative,
  ``EffectiveEncoding.phaseRepresentative,
  ``EffectiveEncoding.SingleCode.representative,
  ``EffectiveEncoding.SingleCode.globalPhase,
  ``EffectiveEncoding.invSqrtTwoOracle,
  ``EffectiveEncoding.phaseCosOracle,
  ``EffectiveEncoding.phaseSinOracle,
  ``EffectiveEncoding.quaternionStarOracle,
  ``EffectiveEncoding.coordinatePacket,
  ``EffectiveEncoding.SingleCode.quaternionOracle
])

#check EffectiveEncoding.mergeAngle_degenerate
#print axioms EffectiveEncoding.mergeAngle_degenerate
#check EffectiveEncoding.AngleAtom.cosOracle_correct
#print axioms EffectiveEncoding.AngleAtom.cosOracle_correct
#check EffectiveEncoding.AngleAtom.sinOracle_correct
#print axioms EffectiveEncoding.AngleAtom.sinOracle_correct
#check EffectiveEncoding.AngleAtom.value_bounds
#print axioms EffectiveEncoding.AngleAtom.value_bounds
#check EffectiveEncoding.AngleCode.cosOracle_correct
#print axioms EffectiveEncoding.AngleCode.cosOracle_correct
#check EffectiveEncoding.AngleCode.sinOracle_correct
#print axioms EffectiveEncoding.AngleCode.sinOracle_correct
#check EffectiveEncoding.AngleCode.evaluation
#print axioms EffectiveEncoding.AngleCode.evaluation
#check EffectiveEncoding.interpret_flatMap
#print axioms EffectiveEncoding.interpret_flatMap
#check EffectiveEncoding.allBranchCode_action
#print axioms EffectiveEncoding.allBranchCode_action
#check EffectiveEncoding.allBranchCode_length
#print axioms EffectiveEncoding.allBranchCode_length
#check EffectiveEncoding.occupationStepCode_action
#print axioms EffectiveEncoding.occupationStepCode_action
#check EffectiveEncoding.occupationStepCode_length
#print axioms EffectiveEncoding.occupationStepCode_length
#check EffectiveEncoding.prefixCode_length
#print axioms EffectiveEncoding.prefixCode_length
#check EffectiveEncoding.interpret_prefix
#print axioms EffectiveEncoding.interpret_prefix
#check EffectiveEncoding.shiftCode_length
#print axioms EffectiveEncoding.shiftCode_length
#check EffectiveEncoding.interpret_shift
#print axioms EffectiveEncoding.interpret_shift
#check EffectiveEncoding.stageCircuit_action
#print axioms EffectiveEncoding.stageCircuit_action
#check EffectiveEncoding.compressionCircuit_succ
#print axioms EffectiveEncoding.compressionCircuit_succ
#check EffectiveEncoding.bitOccupation_zero
#print axioms EffectiveEncoding.bitOccupation_zero
#check EffectiveEncoding.compressionCircuit_action
#print axioms EffectiveEncoding.compressionCircuit_action
#check EffectiveEncoding.stageCode_length
#print axioms EffectiveEncoding.stageCode_length
#check EffectiveEncoding.compressionCode_length
#print axioms EffectiveEncoding.compressionCode_length
#check EffectiveEncoding.compressionCircuit_matrix
#print axioms EffectiveEncoding.compressionCircuit_matrix
#check EffectiveEncoding.compressionCircuit_coherent
#print axioms EffectiveEncoding.compressionCircuit_coherent
#check EffectiveEncoding.compressionCircuit_purePower
#print axioms EffectiveEncoding.compressionCircuit_purePower
#check EffectiveEncoding.AngleCode.neg_value
#print axioms EffectiveEncoding.AngleCode.neg_value
#check EffectiveEncoding.AngleCode.half_value
#print axioms EffectiveEncoding.AngleCode.half_value
#check EffectiveEncoding.piCode_value
#print axioms EffectiveEncoding.piCode_value
#check EffectiveEncoding.GateCode.inverse_value
#print axioms EffectiveEncoding.GateCode.inverse_value
#check EffectiveEncoding.interpret_length
#print axioms EffectiveEncoding.interpret_length
#check EffectiveEncoding.interpret_append
#print axioms EffectiveEncoding.interpret_append
#check EffectiveEncoding.interpret_reverse
#print axioms EffectiveEncoding.interpret_reverse
#check EffectiveEncoding.reverseCode_length
#print axioms EffectiveEncoding.reverseCode_length
#check EffectiveEncoding.maskOfBits_injective
#print axioms EffectiveEncoding.maskOfBits_injective
#check EffectiveEncoding.maskIndex_injective
#print axioms EffectiveEncoding.maskIndex_injective
#check EffectiveEncoding.masks_nodup
#print axioms EffectiveEncoding.masks_nodup
#check EffectiveEncoding.mem_masks
#print axioms EffectiveEncoding.mem_masks
#check EffectiveEncoding.masks_length
#print axioms EffectiveEncoding.masks_length
#check EffectiveEncoding.masks_perm
#print axioms EffectiveEncoding.masks_perm
#check EffectiveEncoding.controls_length
#print axioms EffectiveEncoding.controls_length
#check EffectiveEncoding.controls_character
#print axioms EffectiveEncoding.controls_character
#check EffectiveEncoding.interpret_cnotCode
#print axioms EffectiveEncoding.interpret_cnotCode
#check EffectiveEncoding.parityCode_action
#print axioms EffectiveEncoding.parityCode_action
#check EffectiveEncoding.parityCode_length
#print axioms EffectiveEncoding.parityCode_length
#check EffectiveEncoding.pauliCode_action
#print axioms EffectiveEncoding.pauliCode_action
#check EffectiveEncoding.pauliCode_length
#print axioms EffectiveEncoding.pauliCode_length
#check EffectiveEncoding.signedCode_value
#print axioms EffectiveEncoding.signedCode_value
#check EffectiveEncoding.maskParity_sign
#print axioms EffectiveEncoding.maskParity_sign
#check EffectiveEncoding.run_pauliCodes
#print axioms EffectiveEncoding.run_pauliCodes
#check EffectiveEncoding.selectedCode_action
#print axioms EffectiveEncoding.selectedCode_action
#check EffectiveEncoding.selectedCode_length
#print axioms EffectiveEncoding.selectedCode_length
#check EffectiveEncoding.mem_triples
#print axioms EffectiveEncoding.mem_triples
#check EffectiveEncoding.triples_nodup
#print axioms EffectiveEncoding.triples_nodup
#check EffectiveEncoding.fromTriple_count_zero
#print axioms EffectiveEncoding.fromTriple_count_zero
#check EffectiveEncoding.fromTriple_count_one
#print axioms EffectiveEncoding.fromTriple_count_one
#check EffectiveEncoding.fromTriple_count_two
#print axioms EffectiveEncoding.fromTriple_count_two
#check EffectiveEncoding.fromTriple_count_three
#print axioms EffectiveEncoding.fromTriple_count_three
#check EffectiveEncoding.count_total
#print axioms EffectiveEncoding.count_total
#check EffectiveEncoding.toTriple_le
#print axioms EffectiveEncoding.toTriple_le
#check EffectiveEncoding.toTriple_fromTriple
#print axioms EffectiveEncoding.toTriple_fromTriple
#check EffectiveEncoding.fromTriple_toTriple
#print axioms EffectiveEncoding.fromTriple_toTriple
#check EffectiveEncoding.occupations_nodup
#print axioms EffectiveEncoding.occupations_nodup
#check EffectiveEncoding.mem_occupations
#print axioms EffectiveEncoding.mem_occupations
#check EffectiveEncoding.occupations_length
#print axioms EffectiveEncoding.occupations_length
#check EffectiveEncoding.unrank_rank
#print axioms EffectiveEncoding.unrank_rank
#check EffectiveEncoding.rank_unrank
#print axioms EffectiveEncoding.rank_unrank
#check EffectiveEncoding.boundedBits_injective
#print axioms EffectiveEncoding.boundedBits_injective
#check EffectiveEncoding.rank_fits
#print axioms EffectiveEncoding.rank_fits
#check EffectiveEncoding.find_unique
#print axioms EffectiveEncoding.find_unique
#check EffectiveEncoding.decode_encode
#print axioms EffectiveEncoding.decode_encode
#check EffectiveEncoding.decode_some_iff
#print axioms EffectiveEncoding.decode_some_iff
#check EffectiveEncoding.enumeration_candidate_bound
#print axioms EffectiveEncoding.enumeration_candidate_bound
#check EffectiveEncoding.compactEncoding_testBit
#print axioms EffectiveEncoding.compactEncoding_testBit
#check EffectiveEncoding.originalEncoding_high_zero
#print axioms EffectiveEncoding.originalEncoding_high_zero
#check EffectiveEncoding.interpret_cast
#print axioms EffectiveEncoding.interpret_cast
#check EffectiveEncoding.castCode_length
#print axioms EffectiveEncoding.castCode_length
#check EffectiveEncoding.interpret_bellPreparationCode
#print axioms EffectiveEncoding.interpret_bellPreparationCode
#check EffectiveEncoding.interpret_bellPairsCode
#print axioms EffectiveEncoding.interpret_bellPairsCode
#check EffectiveEncoding.extractionCircuit_eq
#print axioms EffectiveEncoding.extractionCircuit_eq
#check EffectiveEncoding.extractionCircuit_gate
#print axioms EffectiveEncoding.extractionCircuit_gate
#check EffectiveEncoding.extractionCircuit_coherent
#print axioms EffectiveEncoding.extractionCircuit_coherent
#check EffectiveEncoding.extractionCircuit_purePower
#print axioms EffectiveEncoding.extractionCircuit_purePower
#check EffectiveEncoding.extractionCode_length
#print axioms EffectiveEncoding.extractionCode_length
#check EffectiveEncoding.extractionCode_polynomial_bound
#print axioms EffectiveEncoding.extractionCode_polynomial_bound
#check EffectiveEncoding.extractionCircuit_polynomial_bound
#print axioms EffectiveEncoding.extractionCircuit_polynomial_bound
#check EffectiveEncoding.extractionVector_readout
#print axioms EffectiveEncoding.extractionVector_readout
#check EffectiveEncoding.garbageVector_square
#print axioms EffectiveEncoding.garbageVector_square
#check EffectiveEncoding.extractionOutput_coherent
#print axioms EffectiveEncoding.extractionOutput_coherent
#check EffectiveEncoding.extractionOutput_purePower
#print axioms EffectiveEncoding.extractionOutput_purePower
#check EffectiveEncoding.wireLabels_value
#print axioms EffectiveEncoding.wireLabels_value
#check EffectiveEncoding.labelCircuit_flatMap
#print axioms EffectiveEncoding.labelCircuit_flatMap
#check EffectiveEncoding.labelCircuit_uses
#print axioms EffectiveEncoding.labelCircuit_uses
#check EffectiveEncoding.compileLabels_error
#print axioms EffectiveEncoding.compileLabels_error
#check EffectiveEncoding.compileLabelWord_error
#print axioms EffectiveEncoding.compileLabelWord_error
#check EffectiveEncoding.compileLabels_length
#print axioms EffectiveEncoding.compileLabels_length
#check EffectiveEncoding.compileLabelWord_length
#print axioms EffectiveEncoding.compileLabelWord_length
#check EffectiveEncoding.extractionOutput_fidelity_one
#print axioms EffectiveEncoding.extractionOutput_fidelity_one
#check EffectiveEncoding.extractionOutput_robust
#print axioms EffectiveEncoding.extractionOutput_robust
#check EffectiveEncoding.extractionOutput_robust_up_to_phase
#print axioms EffectiveEncoding.extractionOutput_robust_up_to_phase
#check EffectiveEncoding.finiteLabels_fidelity
#print axioms EffectiveEncoding.finiteLabels_fidelity
#check EffectiveEncoding.selectedCode_run_eq
#print axioms EffectiveEncoding.selectedCode_run_eq
#check EffectiveEncoding.adjacentSwapCode_run_eq
#print axioms EffectiveEncoding.adjacentSwapCode_run_eq
#check EffectiveEncoding.adjacentSwapCode_length
#print axioms EffectiveEncoding.adjacentSwapCode_length
#check EffectiveEncoding.adjacentRotationCode_run_eq
#print axioms EffectiveEncoding.adjacentRotationCode_run_eq
#check EffectiveEncoding.adjacentRotationCode_length
#print axioms EffectiveEncoding.adjacentRotationCode_length
#check EffectiveEncoding.orientedRotationCode_run_eq
#print axioms EffectiveEncoding.orientedRotationCode_run_eq
#check EffectiveEncoding.mem_otherWires
#print axioms EffectiveEncoding.mem_otherWires
#check EffectiveEncoding.otherWires_length
#print axioms EffectiveEncoding.otherWires_length
#check EffectiveEncoding.differing_exists
#print axioms EffectiveEncoding.differing_exists
#check EffectiveEncoding.differingWire_spec
#print axioms EffectiveEncoding.differingWire_spec
#check EffectiveEncoding.clearBits_otherWires
#print axioms EffectiveEncoding.clearBits_otherWires
#check EffectiveEncoding.moveCode_run_eq
#print axioms EffectiveEncoding.moveCode_run_eq
#check EffectiveEncoding.moveCode_length
#print axioms EffectiveEncoding.moveCode_length
#check EffectiveEncoding.swapCode_action
#print axioms EffectiveEncoding.swapCode_action
#check EffectiveEncoding.swapCode_length
#print axioms EffectiveEncoding.swapCode_length
#check EffectiveEncoding.rotationCode_action
#print axioms EffectiveEncoding.rotationCode_action
#check EffectiveEncoding.rotationCode_length
#print axioms EffectiveEncoding.rotationCode_length
#check EffectiveEncoding.GateCode.globalPhase_norm
#print axioms EffectiveEncoding.GateCode.globalPhase_norm
#check EffectiveEncoding.GateCode.representative_spec
#print axioms EffectiveEncoding.GateCode.representative_spec
#check EffectiveEncoding.wordPhase_norm
#print axioms EffectiveEncoding.wordPhase_norm
#check EffectiveEncoding.interpret_cons
#print axioms EffectiveEncoding.interpret_cons
#check EffectiveEncoding.representativeCircuit_cons
#print axioms EffectiveEncoding.representativeCircuit_cons
#check EffectiveEncoding.representativeCircuit_phase
#print axioms EffectiveEncoding.representativeCircuit_phase
#check EffectiveEncoding.descriptor_word_error
#print axioms EffectiveEncoding.descriptor_word_error
#check EffectiveEncoding.descriptor_word_uniform_error
#print axioms EffectiveEncoding.descriptor_word_uniform_error
#check EffectiveEncoding.descriptorSynthesis_spec
#print axioms EffectiveEncoding.descriptorSynthesis_spec
#check EffectiveEncoding.numericalExtractionCode_uses
#print axioms EffectiveEncoding.numericalExtractionCode_uses
#check EffectiveEncoding.numericalExtractionCode_error
#print axioms EffectiveEncoding.numericalExtractionCode_error
#check EffectiveEncoding.numericalExtractionCode_length
#print axioms EffectiveEncoding.numericalExtractionCode_length
#check EffectiveEncoding.numericalExtractionCode_fidelity
#print axioms EffectiveEncoding.numericalExtractionCode_fidelity
#check EffectiveEncoding.descriptorArithmeticOperations_bound
#print axioms EffectiveEncoding.descriptorArithmeticOperations_bound
#check EffectiveEncoding.extractionArithmeticOperations_bound
#print axioms EffectiveEncoding.extractionArithmeticOperations_bound
#check EffectiveEncoding.numericalExtraction_from_universal
#print axioms EffectiveEncoding.numericalExtraction_from_universal
#check EffectiveEncoding.countProgram_length
#print axioms EffectiveEncoding.countProgram_length
#check EffectiveEncoding.countProgram_sparse
#print axioms EffectiveEncoding.countProgram_sparse
#check EffectiveEncoding.indexedCount_image
#print axioms EffectiveEncoding.indexedCount_image
#check EffectiveEncoding.indexedCount_ratio
#print axioms EffectiveEncoding.indexedCount_ratio
#check EffectiveEncoding.explicitOthers_perm
#print axioms EffectiveEncoding.explicitOthers_perm
#check EffectiveEncoding.explicitOthers_nodup
#print axioms EffectiveEncoding.explicitOthers_nodup
#check EffectiveEncoding.explicitOthers_length
#print axioms EffectiveEncoding.explicitOthers_length
#check EffectiveEncoding.integerIndexedCode_raw
#print axioms EffectiveEncoding.integerIndexedCode_raw
#check EffectiveEncoding.integerIndexedCode_action
#print axioms EffectiveEncoding.integerIndexedCode_action
#check EffectiveEncoding.integerIndexedCode_fixes_zero
#print axioms EffectiveEncoding.integerIndexedCode_fixes_zero
#check EffectiveEncoding.integerIndexedCode_length
#print axioms EffectiveEncoding.integerIndexedCode_length
#check EffectiveEncoding.branchEmbedding_eq
#print axioms EffectiveEncoding.branchEmbedding_eq
#check EffectiveEncoding.branchCode_action
#print axioms EffectiveEncoding.branchCode_action
#check EffectiveEncoding.branchCode_fixes_other
#print axioms EffectiveEncoding.branchCode_fixes_other
#check EffectiveEncoding.branchCode_fixes_other_pivot
#print axioms EffectiveEncoding.branchCode_fixes_other_pivot
#check EffectiveEncoding.branchCode_length
#print axioms EffectiveEncoding.branchCode_length
#check EffectiveEncoding.swapCode_denote
#print axioms EffectiveEncoding.swapCode_denote
#check EffectiveEncoding.rotationCode_denote_eq
#print axioms EffectiveEncoding.rotationCode_denote_eq
#check EffectiveEncoding.mergeCode_value
#print axioms EffectiveEncoding.mergeCode_value
#check EffectiveEncoding.RawCode.compile_denote
#print axioms EffectiveEncoding.RawCode.compile_denote
#check EffectiveEncoding.RawCode.compile_length
#print axioms EffectiveEncoding.RawCode.compile_length
#check EffectiveEncoding.compileRaw_denote
#print axioms EffectiveEncoding.compileRaw_denote
#check EffectiveEncoding.compileRaw_length
#print axioms EffectiveEncoding.compileRaw_length
#check EffectiveEncoding.alignmentPerm_complete
#print axioms EffectiveEncoding.alignmentPerm_complete
#check EffectiveEncoding.alignmentCode_action
#print axioms EffectiveEncoding.alignmentCode_action
#check EffectiveEncoding.alignmentCode_length
#print axioms EffectiveEncoding.alignmentCode_length
#check EffectiveEncoding.alignmentCode_on_embedding
#print axioms EffectiveEncoding.alignmentCode_on_embedding
#check EffectiveEncoding.star_complexPhase
#print axioms EffectiveEncoding.star_complexPhase
#check EffectiveEncoding.phaseRepresentative_bool
#print axioms EffectiveEncoding.phaseRepresentative_bool
#check EffectiveEncoding.su2ToBool_star
#print axioms EffectiveEncoding.su2ToBool_star
#check EffectiveEncoding.SingleCode.globalPhase_norm
#print axioms EffectiveEncoding.SingleCode.globalPhase_norm
#check EffectiveEncoding.SingleCode.representative_spec
#print axioms EffectiveEncoding.SingleCode.representative_spec
#check EffectiveEncoding.quaternionCoordinates_star
#print axioms EffectiveEncoding.quaternionCoordinates_star
#check EffectiveEncoding.sqrt_half_eq_invSqrtTwo
#print axioms EffectiveEncoding.sqrt_half_eq_invSqrtTwo
#check EffectiveEncoding.invSqrtTwoOracle_correct
#print axioms EffectiveEncoding.invSqrtTwoOracle_correct
#check EffectiveEncoding.phaseCosOracle_correct
#print axioms EffectiveEncoding.phaseCosOracle_correct
#check EffectiveEncoding.phaseSinOracle_correct
#print axioms EffectiveEncoding.phaseSinOracle_correct
#check EffectiveEncoding.quaternionStarOracle_correct
#print axioms EffectiveEncoding.quaternionStarOracle_correct
#check EffectiveEncoding.coordinatePacket_correct
#print axioms EffectiveEncoding.coordinatePacket_correct
#check EffectiveEncoding.hadRepresentative_coordinates
#print axioms EffectiveEncoding.hadRepresentative_coordinates
#check EffectiveEncoding.phaseRepresentative_coordinates
#print axioms EffectiveEncoding.phaseRepresentative_coordinates
#check EffectiveEncoding.SingleCode.quaternionOracle_correct
#print axioms EffectiveEncoding.SingleCode.quaternionOracle_correct
#check EffectiveEncoding.AngleAtom.cosOracle
#print axioms EffectiveEncoding.AngleAtom.cosOracle
#check EffectiveEncoding.AngleAtom.sinOracle
#print axioms EffectiveEncoding.AngleAtom.sinOracle
#check EffectiveEncoding.AngleCode.cosOracle
#print axioms EffectiveEncoding.AngleCode.cosOracle
#check EffectiveEncoding.AngleCode.sinOracle
#print axioms EffectiveEncoding.AngleCode.sinOracle
#check EffectiveEncoding.allBranchCode
#print axioms EffectiveEncoding.allBranchCode
#check EffectiveEncoding.occupationStepCode
#print axioms EffectiveEncoding.occupationStepCode
#check EffectiveEncoding.GateCode.extend
#print axioms EffectiveEncoding.GateCode.extend
#check EffectiveEncoding.prefixCode
#print axioms EffectiveEncoding.prefixCode
#check EffectiveEncoding.GateCode.shift
#print axioms EffectiveEncoding.GateCode.shift
#check EffectiveEncoding.shiftCode
#print axioms EffectiveEncoding.shiftCode
#check EffectiveEncoding.stageCode
#print axioms EffectiveEncoding.stageCode
#check EffectiveEncoding.stageCircuit
#print axioms EffectiveEncoding.stageCircuit
#check EffectiveEncoding.compressionCode
#print axioms EffectiveEncoding.compressionCode
#check EffectiveEncoding.compressionCircuit
#print axioms EffectiveEncoding.compressionCircuit
#check EffectiveEncoding.AngleAtom
#print axioms EffectiveEncoding.AngleAtom
#check EffectiveEncoding.AngleCode
#print axioms EffectiveEncoding.AngleCode
#check EffectiveEncoding.AngleAtom.value
#print axioms EffectiveEncoding.AngleAtom.value
#check EffectiveEncoding.AngleCode.value
#print axioms EffectiveEncoding.AngleCode.value
#check EffectiveEncoding.AngleCode.neg
#print axioms EffectiveEncoding.AngleCode.neg
#check EffectiveEncoding.AngleCode.half
#print axioms EffectiveEncoding.AngleCode.half
#check EffectiveEncoding.piCode
#print axioms EffectiveEncoding.piCode
#check EffectiveEncoding.SingleCode
#print axioms EffectiveEncoding.SingleCode
#check EffectiveEncoding.SingleCode.value
#print axioms EffectiveEncoding.SingleCode.value
#check EffectiveEncoding.GateCode
#print axioms EffectiveEncoding.GateCode
#check EffectiveEncoding.GateCode.value
#print axioms EffectiveEncoding.GateCode.value
#check EffectiveEncoding.GateCode.inverse
#print axioms EffectiveEncoding.GateCode.inverse
#check EffectiveEncoding.WordCode
#print axioms EffectiveEncoding.WordCode
#check EffectiveEncoding.interpret
#print axioms EffectiveEncoding.interpret
#check EffectiveEncoding.reverseCode
#print axioms EffectiveEncoding.reverseCode
#check EffectiveEncoding.maskOfBits
#print axioms EffectiveEncoding.maskOfBits
#check EffectiveEncoding.masks
#print axioms EffectiveEncoding.masks
#check EffectiveEncoding.controls
#print axioms EffectiveEncoding.controls
#check EffectiveEncoding.cnotCode
#print axioms EffectiveEncoding.cnotCode
#check EffectiveEncoding.parityCode
#print axioms EffectiveEncoding.parityCode
#check EffectiveEncoding.pauliCode
#print axioms EffectiveEncoding.pauliCode
#check EffectiveEncoding.signedCode
#print axioms EffectiveEncoding.signedCode
#check EffectiveEncoding.maskParity
#print axioms EffectiveEncoding.maskParity
#check EffectiveEncoding.selectedCode
#print axioms EffectiveEncoding.selectedCode
#check EffectiveEncoding.Triple
#print axioms EffectiveEncoding.Triple
#check EffectiveEncoding.total
#print axioms EffectiveEncoding.total
#check EffectiveEncoding.triples
#print axioms EffectiveEncoding.triples
#check EffectiveEncoding.fromTriple
#print axioms EffectiveEncoding.fromTriple
#check EffectiveEncoding.toTriple
#print axioms EffectiveEncoding.toTriple
#check EffectiveEncoding.occupations
#print axioms EffectiveEncoding.occupations
#check EffectiveEncoding.rank
#print axioms EffectiveEncoding.rank
#check EffectiveEncoding.unrank
#print axioms EffectiveEncoding.unrank
#check EffectiveEncoding.rankEquiv
#print axioms EffectiveEncoding.rankEquiv
#check EffectiveEncoding.boundedBits
#print axioms EffectiveEncoding.boundedBits
#check EffectiveEncoding.compactEncoding
#print axioms EffectiveEncoding.compactEncoding
#check EffectiveEncoding.originalEncoding
#print axioms EffectiveEncoding.originalEncoding
#check EffectiveEncoding.nextEncoding
#print axioms EffectiveEncoding.nextEncoding
#check EffectiveEncoding.decode
#print axioms EffectiveEncoding.decode
#check EffectiveEncoding.castCode
#print axioms EffectiveEncoding.castCode
#check EffectiveEncoding.bellPreparationCode
#print axioms EffectiveEncoding.bellPreparationCode
#check EffectiveEncoding.bellPairsCode
#print axioms EffectiveEncoding.bellPairsCode
#check EffectiveEncoding.extractionCode
#print axioms EffectiveEncoding.extractionCode
#check EffectiveEncoding.extractionCircuit
#print axioms EffectiveEncoding.extractionCircuit
#check EffectiveEncoding.extractionVector
#print axioms EffectiveEncoding.extractionVector
#check EffectiveEncoding.garbageVector
#print axioms EffectiveEncoding.garbageVector
#check EffectiveEncoding.extractionOutput
#print axioms EffectiveEncoding.extractionOutput
#check EffectiveEncoding.LabelGate
#print axioms EffectiveEncoding.LabelGate
#check EffectiveEncoding.LabelGate.value
#print axioms EffectiveEncoding.LabelGate.value
#check EffectiveEncoding.labelCircuit
#print axioms EffectiveEncoding.labelCircuit
#check EffectiveEncoding.wireLabels
#print axioms EffectiveEncoding.wireLabels
#check EffectiveEncoding.compileLabels
#print axioms EffectiveEncoding.compileLabels
#check EffectiveEncoding.compileLabelWord
#print axioms EffectiveEncoding.compileLabelWord
#check EffectiveEncoding.adjacentSwapCode
#print axioms EffectiveEncoding.adjacentSwapCode
#check EffectiveEncoding.adjacentRotationCode
#print axioms EffectiveEncoding.adjacentRotationCode
#check EffectiveEncoding.orientedRotationCode
#print axioms EffectiveEncoding.orientedRotationCode
#check EffectiveEncoding.otherWires
#print axioms EffectiveEncoding.otherWires
#check EffectiveEncoding.differingWire
#print axioms EffectiveEncoding.differingWire
#check EffectiveEncoding.moveCode
#print axioms EffectiveEncoding.moveCode
#check EffectiveEncoding.swapCode
#print axioms EffectiveEncoding.swapCode
#check EffectiveEncoding.rotationCode
#print axioms EffectiveEncoding.rotationCode
#check EffectiveEncoding.GateCode.representative
#print axioms EffectiveEncoding.GateCode.representative
#check EffectiveEncoding.GateCode.globalPhase
#print axioms EffectiveEncoding.GateCode.globalPhase
#check EffectiveEncoding.representativeCircuit
#print axioms EffectiveEncoding.representativeCircuit
#check EffectiveEncoding.wordPhase
#print axioms EffectiveEncoding.wordPhase
#check EffectiveEncoding.descriptorSynthesis
#print axioms EffectiveEncoding.descriptorSynthesis
#check EffectiveEncoding.extractionPrecision
#print axioms EffectiveEncoding.extractionPrecision
#check EffectiveEncoding.numericalExtractionCode
#print axioms EffectiveEncoding.numericalExtractionCode
#check EffectiveEncoding.descriptorArithmeticOperations
#print axioms EffectiveEncoding.descriptorArithmeticOperations
#check EffectiveEncoding.gateArithmeticOperations
#print axioms EffectiveEncoding.gateArithmeticOperations
#check EffectiveEncoding.extractionArithmeticOperations
#print axioms EffectiveEncoding.extractionArithmeticOperations
#check EffectiveEncoding.countProgram
#print axioms EffectiveEncoding.countProgram
#check EffectiveEncoding.indexedCount
#print axioms EffectiveEncoding.indexedCount
#check EffectiveEncoding.explicitOthers
#print axioms EffectiveEncoding.explicitOthers
#check EffectiveEncoding.integerIndexedCode
#print axioms EffectiveEncoding.integerIndexedCode
#check EffectiveEncoding.occupiedPivot
#print axioms EffectiveEncoding.occupiedPivot
#check EffectiveEncoding.branchEmbedding
#print axioms EffectiveEncoding.branchEmbedding
#check EffectiveEncoding.pivotCoordinates
#print axioms EffectiveEncoding.pivotCoordinates
#check EffectiveEncoding.pivotEmbedding
#print axioms EffectiveEncoding.pivotEmbedding
#check EffectiveEncoding.branchCode
#print axioms EffectiveEncoding.branchCode
#check EffectiveEncoding.RawCode
#print axioms EffectiveEncoding.RawCode
#check EffectiveEncoding.mergeCode
#print axioms EffectiveEncoding.mergeCode
#check EffectiveEncoding.RawCode.value
#print axioms EffectiveEncoding.RawCode.value
#check EffectiveEncoding.RawCode.compile
#print axioms EffectiveEncoding.RawCode.compile
#check EffectiveEncoding.compileRaw
#print axioms EffectiveEncoding.compileRaw
#check EffectiveEncoding.alignmentPerm
#print axioms EffectiveEncoding.alignmentPerm
#check EffectiveEncoding.alignmentCode
#print axioms EffectiveEncoding.alignmentCode
#check EffectiveEncoding.hadRepresentative
#print axioms EffectiveEncoding.hadRepresentative
#check EffectiveEncoding.yRepresentative
#print axioms EffectiveEncoding.yRepresentative
#check EffectiveEncoding.phaseRepresentative
#print axioms EffectiveEncoding.phaseRepresentative
#check EffectiveEncoding.SingleCode.representative
#print axioms EffectiveEncoding.SingleCode.representative
#check EffectiveEncoding.SingleCode.globalPhase
#print axioms EffectiveEncoding.SingleCode.globalPhase
#check EffectiveEncoding.invSqrtTwoOracle
#print axioms EffectiveEncoding.invSqrtTwoOracle
#check EffectiveEncoding.phaseCosOracle
#print axioms EffectiveEncoding.phaseCosOracle
#check EffectiveEncoding.phaseSinOracle
#print axioms EffectiveEncoding.phaseSinOracle
#check EffectiveEncoding.quaternionStarOracle
#print axioms EffectiveEncoding.quaternionStarOracle
#check EffectiveEncoding.coordinatePacket
#print axioms EffectiveEncoding.coordinatePacket
#check EffectiveEncoding.SingleCode.quaternionOracle
#print axioms EffectiveEncoding.SingleCode.quaternionOracle
