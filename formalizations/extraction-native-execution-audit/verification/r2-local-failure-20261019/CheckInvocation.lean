import NativeExecutionAudit
import NativeExecutionVerification.ReplaySupport

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

run_cmd NativeExecutionVerification.checkKinds [
  ``ConcreteNativeExtraction.assembledRun_word,
  ``ConcreteNativeExtraction.assembledRun_erase,
  ``ConcreteNativeExtraction.assembledRun_word_eq_inputRun,
  ``ConcreteNativeExtraction.assembledRun_uses_finite_library,
  ``ConcreteNativeExtraction.assembledRun_length,
  ``ConcreteNativeExtraction.assembledRun_fidelity,
  ``ConcreteNativeExtraction.assembledRun_accounted_actions,
  ``ConcreteNativeExtraction.assembledRun_inverse_calls,
  ``ConcreteNativeExtraction.concrete_assembled_compiler_exists,
  ``ConcreteNativeExtraction.offlineNet_exists,
  ``ConcreteNativeExtraction.queried_gate_height,
  ``RationalGateBinary.nativeEntry_decode,
  ``RationalGateBinary.nativeEntry_correct,
  ``RationalGateBinary.nativeEntryProgram_normalization_actions,
  ``RationalGateInterface.rationalGate_inverse,
  ``RationalGateUniversality.rationalGate_dense,
  ``CircuitRecursion.inputCachedRun_onlineActions_degree338,
  ``CircuitRecursion.inputCachedRun_readActions_degree73,
  ``CircuitRecursion.assembledInputCachedRun_erase,
  ``CircuitRecursion.assembledInputCachedRun_onlineActions_degree338,
  ``CircuitRecursion.assembledInputCachedRun_actions_degree13,
  ``CircuitRecursion.assembledInputPairWord_program,
  ``EffectiveEncoding.nativeBooleanRankProgram_ranked,
  ``EffectiveEncoding.nativeBooleanRankProgram_booleanActions_polynomial,
  ``EffectiveEncoding.scannedNativeDescriptorRun_result,
  ``EffectiveEncoding.scannedNativeDescriptorRun_scanActions,
  ``EffectiveEncoding.retainedAssembledTargetRun_erase,
  ``EffectiveEncoding.retainedAssembledTargetRun_cached,
  ``EffectiveEncoding.fullyAssembledInputRun_erase,
  ``EffectiveEncoding.fullyAssembledInputRun_accountedPrimitiveActions,
  ``EffectiveEncoding.fullyAssembledInputRun_fidelity,
  ``EffectiveEncoding.retainedInputTargetRun_cached,
  ``EffectiveEncoding.retainedInputTargetRun_cache
] [
  ``ConcreteNativeExtraction.OfflineNet,
  ``ConcreteNativeExtraction.assembledRun,
  ``ConcreteNativeExtraction.assembledPrimitiveBound,
  ``ConcreteNativeExtraction.gateHeightCoefficient,
  ``RationalGateBinary.nativeEntryProgram,
  ``RationalGateBinary.nativeEntry,
  ``RationalGateInterface.rationalGate,
  ``CircuitRecursion.binaryPacketInputProgram,
  ``CircuitRecursion.BinaryPacketInputResult.actions,
  ``CircuitRecursion.binaryTrimProgram,
  ``CircuitRecursion.signedBinaryNormalizeProgram,
  ``CircuitRecursion.ListAssemblyTrace,
  ``CircuitRecursion.ListAssemblyTrace.actions,
  ``CircuitRecursion.ListAssemblyTrace.copies,
  ``CircuitRecursion.listAppendProgram,
  ``CircuitRecursion.listReverseMapIntoProgram,
  ``CircuitRecursion.instructionInverseProgram,
  ``CircuitRecursion.InputListAssemblyTrace,
  ``CircuitRecursion.InputListAssemblyTrace.actions,
  ``CircuitRecursion.InputListAssemblyTrace.inverseCalls,
  ``CircuitRecursion.assembleCorrectedInput,
  ``CircuitRecursion.assembledInputCorrection,
  ``CircuitRecursion.assembledInputPairWord,
  ``CircuitRecursion.AssembledInputWordResult.onlineActions,
  ``CircuitRecursion.assembledInputCachedRun,
  ``CircuitRecursion.inputCachedRun,
  ``CircuitRecursion.InputArithmeticWordResult.numericalActions,
  ``CircuitRecursion.InputArithmeticWordResult.readActions,
  ``CircuitRecursion.InputArithmeticWordResult.onlineActions,
  ``CircuitRecursion.nativeCacheInputRead,
  ``CircuitRecursion.nativeListLookup,
  ``CircuitRecursion.NativeListLookupTrace.actions,
  ``EffectiveEncoding.nativeBooleanRankProgram,
  ``EffectiveEncoding.NativeBooleanRankResult.booleanActions,
  ``EffectiveEncoding.nativeTripleScanProgram,
  ``EffectiveEncoding.NativeTripleComparison.actions,
  ``EffectiveEncoding.NativeTripleScanResult.comparisonActions,
  ``EffectiveEncoding.scannedRankWordProgram,
  ``EffectiveEncoding.scannedNativeDescriptorRun,
  ``EffectiveEncoding.ScannedGeneratedRun.scanActions,
  ``EffectiveEncoding.NativeBinaryRankResult.encodingActions,
  ``EffectiveEncoding.BinaryGeneratedRun.encodingActions,
  ``EffectiveEncoding.retainedAssembledTargetRun,
  ``EffectiveEncoding.RetainedAssembledTargetResult.erase,
  ``EffectiveEncoding.RetainedAssembledTargetResult.assemblyActions,
  ``EffectiveEncoding.compileAssembledWord,
  ``EffectiveEncoding.FullyAssembledInputResult.erase,
  ``EffectiveEncoding.FullyAssembledInputResult.accountedPrimitiveActions,
  ``EffectiveEncoding.fullyAssembledInputRun,
  ``EffectiveEncoding.RetainedInputTargetResult.accountedActions,
  ``EffectiveEncoding.RetainedInputTargetResult.providerActions,
  ``EffectiveEncoding.RetainedNativeTargetResult.providerActions,
  ``EffectiveEncoding.buildNativeTargetPrograms
]

#check ConcreteNativeExtraction.assembledRun_word
set_option pp.universes false in #print axioms ConcreteNativeExtraction.assembledRun_word
#check ConcreteNativeExtraction.assembledRun_erase
set_option pp.universes false in #print axioms ConcreteNativeExtraction.assembledRun_erase
#check ConcreteNativeExtraction.assembledRun_word_eq_inputRun
set_option pp.universes false in #print axioms ConcreteNativeExtraction.assembledRun_word_eq_inputRun
#check ConcreteNativeExtraction.assembledRun_uses_finite_library
set_option pp.universes false in #print axioms ConcreteNativeExtraction.assembledRun_uses_finite_library
#check ConcreteNativeExtraction.assembledRun_length
set_option pp.universes false in #print axioms ConcreteNativeExtraction.assembledRun_length
#check ConcreteNativeExtraction.assembledRun_fidelity
set_option pp.universes false in #print axioms ConcreteNativeExtraction.assembledRun_fidelity
#check ConcreteNativeExtraction.assembledRun_accounted_actions
set_option pp.universes false in #print axioms ConcreteNativeExtraction.assembledRun_accounted_actions
#check ConcreteNativeExtraction.assembledRun_inverse_calls
set_option pp.universes false in #print axioms ConcreteNativeExtraction.assembledRun_inverse_calls
#check ConcreteNativeExtraction.concrete_assembled_compiler_exists
set_option pp.universes false in #print axioms ConcreteNativeExtraction.concrete_assembled_compiler_exists
#check ConcreteNativeExtraction.offlineNet_exists
set_option pp.universes false in #print axioms ConcreteNativeExtraction.offlineNet_exists
#check ConcreteNativeExtraction.queried_gate_height
set_option pp.universes false in #print axioms ConcreteNativeExtraction.queried_gate_height
#check RationalGateBinary.nativeEntry_decode
set_option pp.universes false in #print axioms RationalGateBinary.nativeEntry_decode
#check RationalGateBinary.nativeEntry_correct
set_option pp.universes false in #print axioms RationalGateBinary.nativeEntry_correct
#check RationalGateBinary.nativeEntryProgram_normalization_actions
set_option pp.universes false in #print axioms RationalGateBinary.nativeEntryProgram_normalization_actions
#check RationalGateInterface.rationalGate_inverse
set_option pp.universes false in #print axioms RationalGateInterface.rationalGate_inverse
#check RationalGateUniversality.rationalGate_dense
set_option pp.universes false in #print axioms RationalGateUniversality.rationalGate_dense
#check CircuitRecursion.inputCachedRun_onlineActions_degree338
set_option pp.universes false in #print axioms CircuitRecursion.inputCachedRun_onlineActions_degree338
#check CircuitRecursion.inputCachedRun_readActions_degree73
set_option pp.universes false in #print axioms CircuitRecursion.inputCachedRun_readActions_degree73
#check CircuitRecursion.assembledInputCachedRun_erase
set_option pp.universes false in #print axioms CircuitRecursion.assembledInputCachedRun_erase
#check CircuitRecursion.assembledInputCachedRun_onlineActions_degree338
set_option pp.universes false in #print axioms CircuitRecursion.assembledInputCachedRun_onlineActions_degree338
#check CircuitRecursion.assembledInputCachedRun_actions_degree13
set_option pp.universes false in #print axioms CircuitRecursion.assembledInputCachedRun_actions_degree13
#check CircuitRecursion.assembledInputPairWord_program
set_option pp.universes false in #print axioms CircuitRecursion.assembledInputPairWord_program
#check EffectiveEncoding.nativeBooleanRankProgram_ranked
set_option pp.universes false in #print axioms EffectiveEncoding.nativeBooleanRankProgram_ranked
#check EffectiveEncoding.nativeBooleanRankProgram_booleanActions_polynomial
set_option pp.universes false in #print axioms EffectiveEncoding.nativeBooleanRankProgram_booleanActions_polynomial
#check EffectiveEncoding.scannedNativeDescriptorRun_result
set_option pp.universes false in #print axioms EffectiveEncoding.scannedNativeDescriptorRun_result
#check EffectiveEncoding.scannedNativeDescriptorRun_scanActions
set_option pp.universes false in #print axioms EffectiveEncoding.scannedNativeDescriptorRun_scanActions
#check EffectiveEncoding.retainedAssembledTargetRun_erase
set_option pp.universes false in #print axioms EffectiveEncoding.retainedAssembledTargetRun_erase
#check EffectiveEncoding.retainedAssembledTargetRun_cached
set_option pp.universes false in #print axioms EffectiveEncoding.retainedAssembledTargetRun_cached
#check EffectiveEncoding.fullyAssembledInputRun_erase
set_option pp.universes false in #print axioms EffectiveEncoding.fullyAssembledInputRun_erase
#check EffectiveEncoding.fullyAssembledInputRun_accountedPrimitiveActions
set_option pp.universes false in #print axioms EffectiveEncoding.fullyAssembledInputRun_accountedPrimitiveActions
#check EffectiveEncoding.fullyAssembledInputRun_fidelity
set_option pp.universes false in #print axioms EffectiveEncoding.fullyAssembledInputRun_fidelity
#check EffectiveEncoding.retainedInputTargetRun_cached
set_option pp.universes false in #print axioms EffectiveEncoding.retainedInputTargetRun_cached
#check EffectiveEncoding.retainedInputTargetRun_cache
set_option pp.universes false in #print axioms EffectiveEncoding.retainedInputTargetRun_cache
#check ConcreteNativeExtraction.OfflineNet
set_option pp.universes false in #print axioms ConcreteNativeExtraction.OfflineNet
#check ConcreteNativeExtraction.assembledRun
set_option pp.universes false in #print axioms ConcreteNativeExtraction.assembledRun
#check ConcreteNativeExtraction.assembledPrimitiveBound
set_option pp.universes false in #print axioms ConcreteNativeExtraction.assembledPrimitiveBound
#check ConcreteNativeExtraction.gateHeightCoefficient
set_option pp.universes false in #print axioms ConcreteNativeExtraction.gateHeightCoefficient
#check RationalGateBinary.nativeEntryProgram
set_option pp.universes false in #print axioms RationalGateBinary.nativeEntryProgram
#check RationalGateBinary.nativeEntry
set_option pp.universes false in #print axioms RationalGateBinary.nativeEntry
#check RationalGateInterface.rationalGate
set_option pp.universes false in #print axioms RationalGateInterface.rationalGate
#check CircuitRecursion.binaryPacketInputProgram
set_option pp.universes false in #print axioms CircuitRecursion.binaryPacketInputProgram
#check CircuitRecursion.BinaryPacketInputResult.actions
set_option pp.universes false in #print axioms CircuitRecursion.BinaryPacketInputResult.actions
#check CircuitRecursion.binaryTrimProgram
set_option pp.universes false in #print axioms CircuitRecursion.binaryTrimProgram
#check CircuitRecursion.signedBinaryNormalizeProgram
set_option pp.universes false in #print axioms CircuitRecursion.signedBinaryNormalizeProgram
#check CircuitRecursion.ListAssemblyTrace
set_option pp.universes false in #print axioms CircuitRecursion.ListAssemblyTrace
#check CircuitRecursion.ListAssemblyTrace.actions
set_option pp.universes false in #print axioms CircuitRecursion.ListAssemblyTrace.actions
#check CircuitRecursion.ListAssemblyTrace.copies
set_option pp.universes false in #print axioms CircuitRecursion.ListAssemblyTrace.copies
#check CircuitRecursion.listAppendProgram
set_option pp.universes false in #print axioms CircuitRecursion.listAppendProgram
#check CircuitRecursion.listReverseMapIntoProgram
set_option pp.universes false in #print axioms CircuitRecursion.listReverseMapIntoProgram
#check CircuitRecursion.instructionInverseProgram
set_option pp.universes false in #print axioms CircuitRecursion.instructionInverseProgram
#check CircuitRecursion.InputListAssemblyTrace
set_option pp.universes false in #print axioms CircuitRecursion.InputListAssemblyTrace
#check CircuitRecursion.InputListAssemblyTrace.actions
set_option pp.universes false in #print axioms CircuitRecursion.InputListAssemblyTrace.actions
#check CircuitRecursion.InputListAssemblyTrace.inverseCalls
set_option pp.universes false in #print axioms CircuitRecursion.InputListAssemblyTrace.inverseCalls
#check CircuitRecursion.assembleCorrectedInput
set_option pp.universes false in #print axioms CircuitRecursion.assembleCorrectedInput
#check CircuitRecursion.assembledInputCorrection
set_option pp.universes false in #print axioms CircuitRecursion.assembledInputCorrection
#check CircuitRecursion.assembledInputPairWord
set_option pp.universes false in #print axioms CircuitRecursion.assembledInputPairWord
#check CircuitRecursion.AssembledInputWordResult.onlineActions
set_option pp.universes false in #print axioms CircuitRecursion.AssembledInputWordResult.onlineActions
#check CircuitRecursion.assembledInputCachedRun
set_option pp.universes false in #print axioms CircuitRecursion.assembledInputCachedRun
#check CircuitRecursion.inputCachedRun
set_option pp.universes false in #print axioms CircuitRecursion.inputCachedRun
#check CircuitRecursion.InputArithmeticWordResult.numericalActions
set_option pp.universes false in #print axioms CircuitRecursion.InputArithmeticWordResult.numericalActions
#check CircuitRecursion.InputArithmeticWordResult.readActions
set_option pp.universes false in #print axioms CircuitRecursion.InputArithmeticWordResult.readActions
#check CircuitRecursion.InputArithmeticWordResult.onlineActions
set_option pp.universes false in #print axioms CircuitRecursion.InputArithmeticWordResult.onlineActions
#check CircuitRecursion.nativeCacheInputRead
set_option pp.universes false in #print axioms CircuitRecursion.nativeCacheInputRead
#check CircuitRecursion.nativeListLookup
set_option pp.universes false in #print axioms CircuitRecursion.nativeListLookup
#check CircuitRecursion.NativeListLookupTrace.actions
set_option pp.universes false in #print axioms CircuitRecursion.NativeListLookupTrace.actions
#check EffectiveEncoding.nativeBooleanRankProgram
set_option pp.universes false in #print axioms EffectiveEncoding.nativeBooleanRankProgram
#check EffectiveEncoding.NativeBooleanRankResult.booleanActions
set_option pp.universes false in #print axioms EffectiveEncoding.NativeBooleanRankResult.booleanActions
#check EffectiveEncoding.nativeTripleScanProgram
set_option pp.universes false in #print axioms EffectiveEncoding.nativeTripleScanProgram
#check EffectiveEncoding.NativeTripleComparison.actions
set_option pp.universes false in #print axioms EffectiveEncoding.NativeTripleComparison.actions
#check EffectiveEncoding.NativeTripleScanResult.comparisonActions
set_option pp.universes false in #print axioms EffectiveEncoding.NativeTripleScanResult.comparisonActions
#check EffectiveEncoding.scannedRankWordProgram
set_option pp.universes false in #print axioms EffectiveEncoding.scannedRankWordProgram
#check EffectiveEncoding.scannedNativeDescriptorRun
set_option pp.universes false in #print axioms EffectiveEncoding.scannedNativeDescriptorRun
#check EffectiveEncoding.ScannedGeneratedRun.scanActions
set_option pp.universes false in #print axioms EffectiveEncoding.ScannedGeneratedRun.scanActions
#check EffectiveEncoding.NativeBinaryRankResult.encodingActions
set_option pp.universes false in #print axioms EffectiveEncoding.NativeBinaryRankResult.encodingActions
#check EffectiveEncoding.BinaryGeneratedRun.encodingActions
set_option pp.universes false in #print axioms EffectiveEncoding.BinaryGeneratedRun.encodingActions
#check EffectiveEncoding.retainedAssembledTargetRun
set_option pp.universes false in #print axioms EffectiveEncoding.retainedAssembledTargetRun
#check EffectiveEncoding.RetainedAssembledTargetResult.erase
set_option pp.universes false in #print axioms EffectiveEncoding.RetainedAssembledTargetResult.erase
#check EffectiveEncoding.RetainedAssembledTargetResult.assemblyActions
set_option pp.universes false in #print axioms EffectiveEncoding.RetainedAssembledTargetResult.assemblyActions
#check EffectiveEncoding.compileAssembledWord
set_option pp.universes false in #print axioms EffectiveEncoding.compileAssembledWord
#check EffectiveEncoding.FullyAssembledInputResult.erase
set_option pp.universes false in #print axioms EffectiveEncoding.FullyAssembledInputResult.erase
#check EffectiveEncoding.FullyAssembledInputResult.accountedPrimitiveActions
set_option pp.universes false in #print axioms EffectiveEncoding.FullyAssembledInputResult.accountedPrimitiveActions
#check EffectiveEncoding.fullyAssembledInputRun
set_option pp.universes false in #print axioms EffectiveEncoding.fullyAssembledInputRun
#check EffectiveEncoding.RetainedInputTargetResult.accountedActions
set_option pp.universes false in #print axioms EffectiveEncoding.RetainedInputTargetResult.accountedActions
#check EffectiveEncoding.RetainedInputTargetResult.providerActions
set_option pp.universes false in #print axioms EffectiveEncoding.RetainedInputTargetResult.providerActions
#check EffectiveEncoding.RetainedNativeTargetResult.providerActions
set_option pp.universes false in #print axioms EffectiveEncoding.RetainedNativeTargetResult.providerActions
#check EffectiveEncoding.buildNativeTargetPrograms
set_option pp.universes false in #print axioms EffectiveEncoding.buildNativeTargetPrograms

run_cmd NativeExecutionVerification.dumpModels [
  ``ConcreteNativeExtraction.OfflineNet,
  ``ConcreteNativeExtraction.assembledRun,
  ``ConcreteNativeExtraction.assembledPrimitiveBound,
  ``ConcreteNativeExtraction.gateHeightCoefficient,
  ``RationalGateBinary.nativeEntryProgram,
  ``RationalGateBinary.nativeEntry,
  ``RationalGateInterface.rationalGate,
  ``CircuitRecursion.binaryPacketInputProgram,
  ``CircuitRecursion.BinaryPacketInputResult.actions,
  ``CircuitRecursion.binaryTrimProgram,
  ``CircuitRecursion.signedBinaryNormalizeProgram,
  ``CircuitRecursion.ListAssemblyTrace,
  ``CircuitRecursion.ListAssemblyTrace.actions,
  ``CircuitRecursion.ListAssemblyTrace.copies,
  ``CircuitRecursion.listAppendProgram,
  ``CircuitRecursion.listReverseMapIntoProgram,
  ``CircuitRecursion.instructionInverseProgram,
  ``CircuitRecursion.InputListAssemblyTrace,
  ``CircuitRecursion.InputListAssemblyTrace.actions,
  ``CircuitRecursion.InputListAssemblyTrace.inverseCalls,
  ``CircuitRecursion.assembleCorrectedInput,
  ``CircuitRecursion.assembledInputCorrection,
  ``CircuitRecursion.assembledInputPairWord,
  ``CircuitRecursion.AssembledInputWordResult.onlineActions,
  ``CircuitRecursion.assembledInputCachedRun,
  ``CircuitRecursion.inputCachedRun,
  ``CircuitRecursion.InputArithmeticWordResult.numericalActions,
  ``CircuitRecursion.InputArithmeticWordResult.readActions,
  ``CircuitRecursion.InputArithmeticWordResult.onlineActions,
  ``CircuitRecursion.nativeCacheInputRead,
  ``CircuitRecursion.nativeListLookup,
  ``CircuitRecursion.NativeListLookupTrace.actions,
  ``EffectiveEncoding.nativeBooleanRankProgram,
  ``EffectiveEncoding.NativeBooleanRankResult.booleanActions,
  ``EffectiveEncoding.nativeTripleScanProgram,
  ``EffectiveEncoding.NativeTripleComparison.actions,
  ``EffectiveEncoding.NativeTripleScanResult.comparisonActions,
  ``EffectiveEncoding.scannedRankWordProgram,
  ``EffectiveEncoding.scannedNativeDescriptorRun,
  ``EffectiveEncoding.ScannedGeneratedRun.scanActions,
  ``EffectiveEncoding.NativeBinaryRankResult.encodingActions,
  ``EffectiveEncoding.BinaryGeneratedRun.encodingActions,
  ``EffectiveEncoding.retainedAssembledTargetRun,
  ``EffectiveEncoding.RetainedAssembledTargetResult.erase,
  ``EffectiveEncoding.RetainedAssembledTargetResult.assemblyActions,
  ``EffectiveEncoding.compileAssembledWord,
  ``EffectiveEncoding.FullyAssembledInputResult.erase,
  ``EffectiveEncoding.FullyAssembledInputResult.accountedPrimitiveActions,
  ``EffectiveEncoding.fullyAssembledInputRun,
  ``EffectiveEncoding.RetainedInputTargetResult.accountedActions,
  ``EffectiveEncoding.RetainedInputTargetResult.providerActions,
  ``EffectiveEncoding.RetainedNativeTargetResult.providerActions,
  ``EffectiveEncoding.buildNativeTargetPrograms
] "/mnt/lean-research-d/worktrees/extraction-native-execution-audit-20261019/formalizations/extraction-native-execution-audit/verification/native-execution-20261018T232406707027Z/models"
