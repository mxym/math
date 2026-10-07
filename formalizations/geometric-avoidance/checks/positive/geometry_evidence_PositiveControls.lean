import ContinuumGeometric.RoutingStableGeometry
import ContinuumGeometric.RoutingSeparation
import ContinuumGeometric.RoutingFactorization

namespace ContinuumGeometric.GeometryControls

def c : RoutingTemplate 2 1 := ⟨3, 4, 10⟩
def root : InternalNode 2 1 := ⟨0, Fin.elim0⟩
def first : RoutingEdge 2 1 := ⟨root, 0⟩
def second : RoutingEdge 2 1 := ⟨root, 1⟩

example : c.edgeStart first = 10 ∧ c.edgeEnd first = 13 ∧
    c.edgeStart second = 17 ∧ c.edgeEnd second = 20 := by decide

example : c.edgeStart second = c.edgeEnd first + c.gap + 1 := by decide

def p : PowerParams 1 1 := (⟨1, by norm_num⟩, ⟨1, by norm_num⟩)

example : p ∉ powerActivation 3 0 3 5 := by norm_num [p, powerActivation]
example : p ∈ powerActivation 12 0 10 14 := by norm_num [p, powerActivation]

example : periodicGridKey 8 0 = 0 := by norm_num [periodicGridKey]
example : periodicGridKey 8 (1 / 8 : ℝ) = 1 := by norm_num [periodicGridKey]

def zeroParameter : PowerParams 0 0 := (⟨0, by norm_num⟩, ⟨1, by norm_num⟩)

example : zeroParameter ∉ powerActivation 3 0 3 5 := by
  norm_num [zeroParameter, powerActivation]

-- A default decision reads all nondefault selectors, including the last one.
example : chooseRoutingChild 3 (by decide) (fun _ => false) = 2 := by decide
example : chooseRoutingChild 3 (by decide)
    (fun i => if i.val = 0 then false else true) = 1 := by decide
example : chooseRoutingChild 3 (by decide) (fun _ => true) =
    chooseRoutingChild 3 (by decide) (fun i => i.val = 0) := by decide

-- A nested key determines every coarser key, including negative lifts.
example : periodicGridKey 16 (-3 / 16 : ℝ) / 2 =
    periodicGridKey 8 (-3 / 16 : ℝ) := by norm_num [periodicGridKey]

example : ¬NoGridBoundary 8 0 (1 / 8 : ℝ) := by
  intro h
  exact h 1 (by norm_num)

noncomputable def duplicateOwn : Fin 2 → SelectorAddress c :=
  localOwnAddresses c root (fun _ => 0) (fun _ => 0)
noncomputable def duplicateTerminal (σ : SelectorAddress c → Bool) :
    Fin 2 → TerminalAddress c (by decide) :=
  localTerminalAddresses c (by decide) (by decide) root (fun _ => 0) (fun _ => 0) σ

example : ¬Function.Injective duplicateOwn := by
  intro hi
  have hh : (0 : Fin 2) = 1 := hi rfl
  have hv := congrArg Fin.val hh
  norm_num at hv

example (σ : SelectorAddress c → Bool) : ¬Function.Injective (duplicateTerminal σ) := by
  intro hi
  have hh : (0 : Fin 2) = 1 := hi rfl
  have hv := congrArg Fin.val hh
  norm_num at hv

/-- A concrete genuine strict-active original index verifies the full contract.
All terminal routing remains arbitrary in this positive control. -/
example (bits : SelectorEdge 2 1 → Bool) :
    LocalAddressSeparation (actualCenterExposure c 0 bits)
      (localOwnAddresses c root (fun _ : Fin 1 => 0)
        (fun _ => powerPoint (dyadic 12) ((2 : ℝ) ^ (0 : ℤ)) (0, p)))
      (localTerminalAddresses c (by decide) (by decide) root (fun _ : Fin 1 => 0)
        (fun _ => powerPoint (dyadic 12) ((2 : ℝ) ^ (0 : ℤ)) (0, p))) := by
  apply active_original_local_address_separation c (by decide) (by decide)
    (by decide) (by decide) 1 1 0 3 0 (by norm_num) bits root
    (fun _ : Fin 1 => 0) (fun _ => 12)
  · intro i j _
    exact Subsingleton.elim _ _
  · intro _
    exact ⟨4, rfl⟩
  · intro _
    norm_num [c, root, RoutingTemplate.selectorRoutingEdge, RoutingTemplate.edgeStart,
      RoutingTemplate.edgeLength, RoutingTemplate.nodeStart, RoutingTemplate.subtreeStart,
      RoutingTemplate.lengthAt, RoutingTemplate.blockSpan, p, powerActivation]

end ContinuumGeometric.GeometryControls
