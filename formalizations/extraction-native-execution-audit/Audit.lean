import NativeExecutionAudit
import NativeExecutionVerification.ReplaySupport

run_cmd NativeExecutionVerification.replayAll [
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
  ``EffectiveEncoding.retainedInputTargetRun_cache,
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
] "@EVIDENCE@/kernel"

run_cmd NativeExecutionVerification.rejectCorruptTheorem ``ConcreteNativeExtraction.assembledRun_word "@EVIDENCE@/control-1"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``ConcreteNativeExtraction.assembledRun_erase "@EVIDENCE@/control-2"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``ConcreteNativeExtraction.assembledRun_word_eq_inputRun "@EVIDENCE@/control-3"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``ConcreteNativeExtraction.assembledRun_uses_finite_library "@EVIDENCE@/control-4"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``ConcreteNativeExtraction.assembledRun_length "@EVIDENCE@/control-5"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``ConcreteNativeExtraction.assembledRun_fidelity "@EVIDENCE@/control-6"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``ConcreteNativeExtraction.assembledRun_accounted_actions "@EVIDENCE@/control-7"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``ConcreteNativeExtraction.assembledRun_inverse_calls "@EVIDENCE@/control-8"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``ConcreteNativeExtraction.concrete_assembled_compiler_exists "@EVIDENCE@/control-9"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``ConcreteNativeExtraction.offlineNet_exists "@EVIDENCE@/control-10"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``ConcreteNativeExtraction.queried_gate_height "@EVIDENCE@/control-11"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``RationalGateBinary.nativeEntry_decode "@EVIDENCE@/control-12"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``RationalGateBinary.nativeEntry_correct "@EVIDENCE@/control-13"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``RationalGateBinary.nativeEntryProgram_normalization_actions "@EVIDENCE@/control-14"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``RationalGateInterface.rationalGate_inverse "@EVIDENCE@/control-15"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``RationalGateUniversality.rationalGate_dense "@EVIDENCE@/control-16"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``CircuitRecursion.inputCachedRun_onlineActions_degree338 "@EVIDENCE@/control-17"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``CircuitRecursion.inputCachedRun_readActions_degree73 "@EVIDENCE@/control-18"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``CircuitRecursion.assembledInputCachedRun_erase "@EVIDENCE@/control-19"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``CircuitRecursion.assembledInputCachedRun_onlineActions_degree338 "@EVIDENCE@/control-20"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``CircuitRecursion.assembledInputCachedRun_actions_degree13 "@EVIDENCE@/control-21"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``CircuitRecursion.assembledInputPairWord_program "@EVIDENCE@/control-22"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``EffectiveEncoding.nativeBooleanRankProgram_ranked "@EVIDENCE@/control-23"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``EffectiveEncoding.nativeBooleanRankProgram_booleanActions_polynomial "@EVIDENCE@/control-24"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``EffectiveEncoding.scannedNativeDescriptorRun_result "@EVIDENCE@/control-25"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``EffectiveEncoding.scannedNativeDescriptorRun_scanActions "@EVIDENCE@/control-26"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``EffectiveEncoding.retainedAssembledTargetRun_erase "@EVIDENCE@/control-27"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``EffectiveEncoding.retainedAssembledTargetRun_cached "@EVIDENCE@/control-28"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``EffectiveEncoding.fullyAssembledInputRun_erase "@EVIDENCE@/control-29"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``EffectiveEncoding.fullyAssembledInputRun_accountedPrimitiveActions "@EVIDENCE@/control-30"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``EffectiveEncoding.fullyAssembledInputRun_fidelity "@EVIDENCE@/control-31"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``EffectiveEncoding.retainedInputTargetRun_cached "@EVIDENCE@/control-32"
run_cmd NativeExecutionVerification.rejectCorruptTheorem ``EffectiveEncoding.retainedInputTargetRun_cache "@EVIDENCE@/control-33"
