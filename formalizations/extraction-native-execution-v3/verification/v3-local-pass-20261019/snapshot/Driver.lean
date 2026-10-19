import Lean.Replay
import Lean.Util.Path

open Lean
namespace NativeExecutionV3

@[extern "lean_internal_set_max_memory"]
opaque setMaximumMemory (max : USize) : BaseIO Unit

def theoremNames : List Name := [
  `ConcreteNativeExtraction.assembledRun_word,
  `ConcreteNativeExtraction.assembledRun_erase,
  `ConcreteNativeExtraction.assembledRun_word_eq_inputRun,
  `ConcreteNativeExtraction.assembledRun_uses_finite_library,
  `ConcreteNativeExtraction.assembledRun_length,
  `ConcreteNativeExtraction.assembledRun_fidelity,
  `ConcreteNativeExtraction.assembledRun_accounted_actions,
  `ConcreteNativeExtraction.assembledRun_inverse_calls,
  `ConcreteNativeExtraction.concrete_assembled_compiler_exists,
  `ConcreteNativeExtraction.offlineNet_exists,
  `ConcreteNativeExtraction.queried_gate_height,
  `RationalGateBinary.nativeEntry_decode,
  `RationalGateBinary.nativeEntry_correct,
  `RationalGateBinary.nativeEntryProgram_normalization_actions,
  `RationalGateInterface.rationalGate_inverse,
  `RationalGateUniversality.rationalGate_dense,
  `CircuitRecursion.inputCachedRun_onlineActions_degree338,
  `CircuitRecursion.inputCachedRun_readActions_degree73,
  `CircuitRecursion.assembledInputCachedRun_erase,
  `CircuitRecursion.assembledInputCachedRun_onlineActions_degree338,
  `CircuitRecursion.assembledInputCachedRun_actions_degree13,
  `CircuitRecursion.assembledInputPairWord_program,
  `EffectiveEncoding.nativeBooleanRankProgram_ranked,
  `EffectiveEncoding.nativeBooleanRankProgram_booleanActions_polynomial,
  `EffectiveEncoding.scannedNativeDescriptorRun_result,
  `EffectiveEncoding.scannedNativeDescriptorRun_scanActions,
  `EffectiveEncoding.retainedAssembledTargetRun_erase,
  `EffectiveEncoding.retainedAssembledTargetRun_cached,
  `EffectiveEncoding.fullyAssembledInputRun_erase,
  `EffectiveEncoding.fullyAssembledInputRun_accountedPrimitiveActions,
  `EffectiveEncoding.fullyAssembledInputRun_fidelity,
  `EffectiveEncoding.retainedInputTargetRun_cached,
  `EffectiveEncoding.retainedInputTargetRun_cache
]

def modelNames : List Name := [
  `ConcreteNativeExtraction.OfflineNet,
  `ConcreteNativeExtraction.assembledRun,
  `ConcreteNativeExtraction.assembledPrimitiveBound,
  `ConcreteNativeExtraction.gateHeightCoefficient,
  `RationalGateBinary.nativeEntryProgram,
  `RationalGateBinary.nativeEntry,
  `RationalGateInterface.rationalGate,
  `CircuitRecursion.binaryPacketInputProgram,
  `CircuitRecursion.BinaryPacketInputResult.actions,
  `CircuitRecursion.binaryTrimProgram,
  `CircuitRecursion.signedBinaryNormalizeProgram,
  `CircuitRecursion.ListAssemblyTrace,
  `CircuitRecursion.ListAssemblyTrace.actions,
  `CircuitRecursion.ListAssemblyTrace.copies,
  `CircuitRecursion.listAppendProgram,
  `CircuitRecursion.listReverseMapIntoProgram,
  `CircuitRecursion.instructionInverseProgram,
  `CircuitRecursion.InputListAssemblyTrace,
  `CircuitRecursion.InputListAssemblyTrace.actions,
  `CircuitRecursion.InputListAssemblyTrace.inverseCalls,
  `CircuitRecursion.assembleCorrectedInput,
  `CircuitRecursion.assembledInputCorrection,
  `CircuitRecursion.assembledInputPairWord,
  `CircuitRecursion.AssembledInputWordResult.onlineActions,
  `CircuitRecursion.assembledInputCachedRun,
  `CircuitRecursion.inputCachedRun,
  `CircuitRecursion.InputArithmeticWordResult.numericalActions,
  `CircuitRecursion.InputArithmeticWordResult.readActions,
  `CircuitRecursion.InputArithmeticWordResult.onlineActions,
  `CircuitRecursion.nativeCacheInputRead,
  `CircuitRecursion.nativeListLookup,
  `CircuitRecursion.NativeListLookupTrace.actions,
  `EffectiveEncoding.nativeBooleanRankProgram,
  `EffectiveEncoding.NativeBooleanRankResult.booleanActions,
  `EffectiveEncoding.nativeTripleScanProgram,
  `EffectiveEncoding.NativeTripleComparison.actions,
  `EffectiveEncoding.NativeTripleScanResult.comparisonActions,
  `EffectiveEncoding.scannedRankWordProgram,
  `EffectiveEncoding.scannedNativeDescriptorRun,
  `EffectiveEncoding.ScannedGeneratedRun.scanActions,
  `EffectiveEncoding.NativeBinaryRankResult.encodingActions,
  `EffectiveEncoding.BinaryGeneratedRun.encodingActions,
  `EffectiveEncoding.retainedAssembledTargetRun,
  `EffectiveEncoding.RetainedAssembledTargetResult.erase,
  `EffectiveEncoding.RetainedAssembledTargetResult.assemblyActions,
  `EffectiveEncoding.compileAssembledWord,
  `EffectiveEncoding.FullyAssembledInputResult.erase,
  `EffectiveEncoding.FullyAssembledInputResult.accountedPrimitiveActions,
  `EffectiveEncoding.fullyAssembledInputRun,
  `EffectiveEncoding.RetainedInputTargetResult.accountedActions,
  `EffectiveEncoding.RetainedInputTargetResult.providerActions,
  `EffectiveEncoding.RetainedNativeTargetResult.providerActions,
  `EffectiveEncoding.buildNativeTargetPrograms
]


def emit (text : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStrLn text
  out.flush

partial def collect (env : Environment) (todo : List Name)
    (seen : Std.HashMap Name ConstantInfo) : Except String (Std.HashMap Name ConstantInfo) :=
  match todo with
  | [] => .ok seen
  | n :: rest =>
    if seen.contains n then collect env rest seen
    else match env.find? n with
    | none => .error s!"Missing dependency {n}"
    | some ci =>
      let extra := match ci with
        | .inductInfo v => v.all ++ v.ctors
        | .ctorInfo v => [v.induct]
        | .recInfo v => v.all
        | _ => []
      collect env (extra ++ ci.getUsedConstantsAsSet.toList ++ rest) (seen.insert n ci)

def collected (env : Environment) (names : List Name) : IO (Std.HashMap Name ConstantInfo) :=
  match collect env names {} with
  | .ok cs => pure cs
  | .error e => throw <| IO.userError e

def checkSafety (cs : Std.HashMap Name ConstantInfo) : IO Unit := do
  for (n, ci) in cs.toList do
    if ci.isUnsafe || ci.isPartial then throw <| IO.userError s!"Unsafe/partial dependency {n}"
    if ci.isAxiom && ![``propext, ``Classical.choice, ``Quot.sound].contains n then
      throw <| IO.userError s!"Unexpected axiom {n}"

def sortedNames (cs : Std.HashMap Name ConstantInfo) : List String :=
  (cs.toList.map (fun p => p.1.toString)).mergeSort (fun a b => decide (a < b))

def axiomNames (cs : Std.HashMap Name ConstantInfo) : List String :=
  (cs.toList.filterMap (fun p => if p.2.isAxiom then some p.1.toString else none)).mergeSort (fun a b => decide (a < b))

def writeLines (path : String) (names : List String) : IO Unit :=
  IO.FS.writeFile path (String.intercalate "\n" names ++ "\n")

def jsonFile (path : String) (j : Json) : IO Unit :=
  IO.FS.writeFile path (j.pretty ++ "\n")

def info (env : Environment) (n : Name) : IO ConstantInfo := do
  let some ci := env.find? n | throw <| IO.userError s!"Missing declaration {n}"
  return ci

def typeText (ci : ConstantInfo) : String :=
  "name " ++ ci.name.toString ++ "\nlevels " ++ reprStr ci.levelParams ++ "\ntype " ++ reprStr ci.type ++ "\n"

def types (env : Environment) (out : String) : IO Unit := do
  for n in theoremNames do
    unless (← info env n).isTheorem do throw <| IO.userError s!"Expected theorem {n}"
  for n in modelNames do
    match ← info env n with
    | .defnInfo _ => pure ()
    | .inductInfo _ => pure ()
    | _ => throw <| IO.userError s!"Expected model definition/inductive {n}"
  emit s!"DECLARATION_KIND_CHECK_PASS {theoremNames.length} theorems; {modelNames.length} definitions"
  for (n, i) in (theoremNames ++ modelNames).zipIdx do
    IO.FS.writeFile s!"{out}/root-types/{i+1}.expr" (typeText (← info env n))
  for (n, i) in modelNames.zipIdx do
    let ci ← info env n
    let tail ← match ci with
      | .defnInfo v => pure ("value " ++ reprStr v.value ++ "\n")
      | .inductInfo v => do
        let mut text := "inductive " ++ reprStr v.all ++ "\nconstructors " ++ reprStr v.ctors ++ "\n"
        for ctor in v.ctors do
          text := text ++ "constructor " ++ typeText (← info env ctor)
        pure text
      | _ => throw <| IO.userError s!"Unexpected model {n}"
    IO.FS.writeFile s!"{out}/models/{i+1}.expr" (typeText ci ++ tail)
  emit s!"ACTUAL_MODEL_CORE_EXPR_EXPORT_PASS {modelNames.length} models"
  let mut rows : List (String × Json) := []
  for n in theoremNames ++ modelNames do
    let cs ← collected env [n]
    checkSafety cs
    rows := rows ++ [(n.toString, Json.arr ((axiomNames cs).map Json.str).toArray)]
  jsonFile s!"{out}/AXIOM_REPORT.json" (Json.mkObj rows)
  emit s!"ACTUAL_TYPE_AXIOM_REPORT_PASS {theoremNames.length+modelNames.length} roots"

def positive (env : Environment) (out : String) : IO Unit := do
  let roots := theoremNames ++ modelNames
  let cs ← collected env roots
  checkSafety cs
  emit s!"POSITIVE_CLOSURE_READY {cs.size} declarations"
  let base ← mkEmptyEnvironment 0
  let verified ← base.toKernelEnv.replay cs
  for root in roots do
    let original ← info env root
    let some checked := verified.find? root | throw <| IO.userError s!"Replayed root missing {root}"
    unless original.type == checked.type && original.levelParams == checked.levelParams do
      throw <| IO.userError s!"Changed type/levels {root}"
  writeLines s!"{out}/kernel-roots.txt" (roots.map Name.toString)
  writeLines s!"{out}/kernel-closure.txt" (sortedNames cs)
  writeLines s!"{out}/kernel-axioms.txt" (axiomNames cs)
  emit s!"EMPTY_KERNEL_REPLAY_PASS {cs.size} declarations; {roots.length} roots; trust level zero"

def control (env : Environment) (index : Nat) (out : String) : IO Unit := do
  if index == 0 then throw <| IO.userError "Control indices start at one"
  let some root := theoremNames[index-1]? | throw <| IO.userError "Control index out of scope"
  let ci ← info env root
  let bad ← match ci with
    | .thmInfo v => pure (ConstantInfo.thmInfo {v with value := mkConst ``True.intro})
    | _ => throw <| IO.userError "Corruption control must select theorem"
  unless bad.type == ci.type && bad.levelParams == ci.levelParams do
    throw <| IO.userError "Corruption changed expected type/levels"
  let deps ← collected env bad.getUsedConstantsAsSet.toList
  if deps.contains root then throw <| IO.userError "Unexpected self dependency"
  unless deps.contains ``True.intro do throw <| IO.userError "Missing forged constructor"
  checkSafety deps
  let positiveBase ← mkEmptyEnvironment 0
  let _ ← positiveBase.toKernelEnv.replay deps
  emit s!"TYPE_CLOSURE_REPLAY_PASS {deps.size} declarations; trust level zero"
  let rejected ← try
    let negativeBase ← mkEmptyEnvironment 0
    let _ ← negativeBase.toKernelEnv.replay (deps.insert root bad)
    pure false
  catch e =>
    let reason := e.toString
    unless (reason.splitOn "(kernel) declaration type mismatch").length > 1 &&
        (reason.splitOn s!"while replaying declaration '{root}'").length > 1 do
      throw <| IO.userError s!"Unexpected rejection reason: {reason}"
    emit s!"EXPECTED_KERNEL_REJECTION: {reason}"
    pure true
  unless rejected do throw <| IO.userError "Forged theorem accepted"
  writeLines s!"{out}/control-{index}-roots.txt" [root.toString]
  writeLines s!"{out}/control-{index}-type-dependencies.txt" (sortedNames deps)
  writeLines s!"{out}/control-{index}-axioms.txt" (axiomNames deps)
  emit s!"CORRUPTED_PROOF_REJECTED {root}"
  emit s!"CORRUPTED_PROOF_TYPE_MISMATCH_REJECTED {root}"

end NativeExecutionV3

def main (args : List String) : IO Unit := do
  NativeExecutionV3.setMaximumMemory (4000 * 1024 * 1024)
  NativeExecutionV3.emit "NATIVE_MAX_MEMORY_BYTES 4194304000"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `ConcreteNativeExtraction.AssembledProgram }] {}
    (trustLevel := 0) (leakEnv := false) (loadExts := false) (level := .private)
  let env := env.setExporting false
  NativeExecutionV3.emit "DATA_ONLY_IMPORT_COMPLETE_NOT_KERNEL_REPLAY"
  match args with
  | ["types", out] => NativeExecutionV3.types env out
  | ["positive", out] => NativeExecutionV3.positive env out
  | ["control", index, out] =>
    let some i := index.toNat? | throw <| IO.userError "Invalid control index"
    NativeExecutionV3.control env i out
  | _ => throw <| IO.userError "Expected types OUT | positive OUT | control INDEX OUT"
