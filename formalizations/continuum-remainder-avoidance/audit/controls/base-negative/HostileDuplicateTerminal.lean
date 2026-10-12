import ContinuumGeometric.RoutingSeparation
open ContinuumGeometric
def c : RoutingTemplate 2 1 := ⟨3, 4, 10⟩
def root : InternalNode 2 1 := ⟨0, Fin.elim0⟩
noncomputable def duplicateTerminal (σ : SelectorAddress c → Bool) :
    Fin 2 → TerminalAddress c (by decide) :=
  localTerminalAddresses c (by decide) (by decide) root (fun _ => 0) (fun _ => 0) σ
example (σ : SelectorAddress c → Bool) : duplicateTerminal σ 0 ≠ duplicateTerminal σ 1 := by
  simp [duplicateTerminal, localTerminalAddresses]
