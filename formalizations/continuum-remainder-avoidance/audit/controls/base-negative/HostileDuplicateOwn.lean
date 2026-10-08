import ContinuumGeometric.RoutingSeparation
open ContinuumGeometric
def c : RoutingTemplate 2 1 := ⟨3, 4, 10⟩
def root : InternalNode 2 1 := ⟨0, Fin.elim0⟩
noncomputable def duplicateOwn : Fin 2 → SelectorAddress c :=
  localOwnAddresses c root (fun _ => 0) (fun _ => 0)
example : duplicateOwn 0 ≠ duplicateOwn 1 := by simp [duplicateOwn, localOwnAddresses]
