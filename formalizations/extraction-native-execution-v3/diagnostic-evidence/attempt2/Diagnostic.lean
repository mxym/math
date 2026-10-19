import Lean.Replay
import Lean.Util.Path

open Lean

/-- Exact runtime ABI documented by Lean/Shell.lean; that module's declaration
is private, so this native-only diagnostic binds the same C symbol directly. -/
@[extern "lean_internal_set_max_memory"]
opaque setDiagnosticMaxMemory (max : USize) : BaseIO Unit

/-- Data-only presence/kind diagnostic. Import is not kernel replay. -/
def main : IO Unit := do
  let cap : USize := 4000 * 1024 * 1024
  setDiagnosticMaxMemory cap
  IO.println s!"DIAGNOSTIC_MAX_MEMORY_BYTES {cap}"
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `NativeExecutionAudit }] {}
    (trustLevel := 0) (leakEnv := false) (loadExts := false) (level := .private)
  for name in [`ConcreteNativeExtraction.concrete_assembled_compiler_exists,
      `ConcreteNativeExtraction.assembledRun_accounted_actions,
      `ConcreteNativeExtraction.assembledRun_erase] do
    match env.find? name with
    | some (.thmInfo _) => IO.println s!"DATA_ONLY_THEOREM_PRESENT {name}"
    | _ => throw <| IO.userError s!"Missing/wrong theorem {name}"
  for name in [`ConcreteNativeExtraction.assembledRun,
      `ConcreteNativeExtraction.assembledPrimitiveBound] do
    match env.find? name with
    | some (.defnInfo _) => IO.println s!"DATA_ONLY_DEFINITION_PRESENT {name}"
    | _ => throw <| IO.userError s!"Missing/wrong definition {name}"
  IO.println "DATA_ONLY_IMPORT_DIAGNOSTIC_COMPLETE_NOT_KERNEL_REPLAY"
