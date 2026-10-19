import Lean.Replay
import Lean.Shell

open Lean

/-- Data-only presence/kind diagnostic. Import is not kernel replay. -/
def main : IO Unit := do
  let cap : USize := 4000 * 1024 * 1024
  Internal.setMaxMemory cap
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
