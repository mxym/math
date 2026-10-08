import ContinuumGeometric.FiniteRoutingProbability
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Rev

namespace ContinuumGeometric.ProbabilityControls

open scoped BigOperators
attribute [local instance] Classical.propDecidable Classical.decEq
set_option backward.isDefEq.respectTransparency false

noncomputable local instance : DecidableEq Unit := Classical.decEq Unit
noncomputable local instance : DecidableEq (Fin 2) := Classical.decEq (Fin 2)

theorem sum_unit_bool_functions [Fintype (Unit → Bool)] (f : (Unit → Bool) → ℝ) :
    (∑ σ : Unit → Bool, f σ) = f (fun _ => false) + f (fun _ => true) := by
  rw [Fintype.sum_equiv (Equiv.funUnique Unit Bool) f
    (fun b => f (fun _ => b)) (fun _ => by congr 1)]
  simp [add_comm]

theorem sum_fin_two_bool_functions [Fintype (Fin 2 → Bool)] (f : (Fin 2 → Bool) → ℝ) :
    (∑ σ : Fin 2 → Bool, f σ) =
      f ![false, false] + f ![false, true] + f ![true, false] + f ![true, true] := by
  rw [Fintype.sum_equiv (finTwoArrowEquiv Bool) f
    (fun b => f ![b.1, b.2]) (fun _ => by congr 1; ext i; fin_cases i <;> rfl)]
  simp [Fintype.sum_prod_type]
  ring

def noExposure {S : Type*} : S → Option Bool := fun _ => none

theorem noExposure_atom {S : Type*} (σ : S → Bool) :
    centerExposureAtom noExposure σ := by simp [centerExposureAtom, noExposure]

/-- Only own-address injectivity is dropped; routed terminal addresses are distinct. -/
def duplicatedOwn : Fin 2 → Unit := fun _ => ()
def distinctTerminals : (Unit → Bool) → Fin 2 → Fin 2 := fun _ i => i

theorem duplicate_own_other_conditions :
    (∀ i : Fin 2, noExposure (duplicatedOwn i) = none) ∧
      (∀ σ : Unit → Bool, centerExposureAtom noExposure σ →
        Function.Injective (distinctTerminals σ)) := by
  exact ⟨fun _ => rfl, fun _ _ => Function.injective_id⟩

theorem duplicate_own_not_injective : ¬Function.Injective duplicatedOwn := by
  intro h
  have := h (show duplicatedOwn 0 = duplicatedOwn 1 by rfl)
  norm_num at this

theorem duplicate_own_joint_probability :
    tableProbability (1 : ℝ) (fun ω : FiniteRoutingTables Unit (Fin 2) =>
      centerExposureAtom noExposure ω.selectors ∧
      localRoutingAllMiss duplicatedOwn distinctTerminals ω) = 1 / 2 := by
  unfold tableProbability
  rw [sum_unit_bool_functions]
  simp_rw [sum_fin_two_bool_functions]
  norm_num [bitTableWeight, bernoulliWeight, centerExposureAtom, noExposure,
    localRoutingAllMiss, localRoutingSuccess, duplicatedOwn, distinctTerminals,
    Fin.prod_univ_two, Fin.forall_fin_two]

theorem duplicate_own_atom_probability :
    tableProbability (T := Fin 2) (1 : ℝ)
      (fun ω : FiniteRoutingTables Unit (Fin 2) =>
        centerExposureAtom noExposure ω.selectors) = 1 := by
  rw [center_atom_probability]
  simp [noExposure, exposureMass]

theorem duplicate_own_breaks_joint_identity :
    tableProbability (1 : ℝ) (fun ω : FiniteRoutingTables Unit (Fin 2) =>
      centerExposureAtom noExposure ω.selectors ∧
      localRoutingAllMiss duplicatedOwn distinctTerminals ω) ≠
    tableProbability (T := Fin 2) (1 : ℝ)
      (fun ω : FiniteRoutingTables Unit (Fin 2) =>
        centerExposureAtom noExposure ω.selectors) * (1 - 1 / 2) ^ 2 := by
  rw [duplicate_own_joint_probability, duplicate_own_atom_probability]
  norm_num

/-- Only routed terminal injectivity is dropped; own addresses are distinct and free. -/
def distinctOwn : Fin 2 → Fin 2 := id
def duplicatedTerminal : (Fin 2 → Bool) → Fin 2 → Unit := fun _ _ => ()

theorem duplicate_terminal_other_conditions :
    Function.Injective distinctOwn ∧
      (∀ i : Fin 2, noExposure (distinctOwn i) = none) := by
  exact ⟨Function.injective_id, fun _ => rfl⟩

theorem duplicate_terminal_not_injective (σ : Fin 2 → Bool) :
    ¬Function.Injective (duplicatedTerminal σ) := by
  intro h
  have := h (show duplicatedTerminal σ 0 = duplicatedTerminal σ 1 by rfl)
  norm_num at this

theorem duplicate_terminal_joint_probability :
    tableProbability (1 / 2 : ℝ) (fun ω : FiniteRoutingTables (Fin 2) Unit =>
      centerExposureAtom noExposure ω.selectors ∧
      localRoutingAllMiss distinctOwn duplicatedTerminal ω) = 5 / 8 := by
  unfold tableProbability
  rw [sum_fin_two_bool_functions]
  simp_rw [sum_unit_bool_functions]
  norm_num [bitTableWeight, bernoulliWeight, centerExposureAtom, noExposure,
    localRoutingAllMiss, localRoutingSuccess, distinctOwn, duplicatedTerminal,
    Fin.prod_univ_two, Fin.forall_fin_two]

theorem duplicate_terminal_atom_probability :
    tableProbability (T := Unit) (1 / 2 : ℝ)
      (fun ω : FiniteRoutingTables (Fin 2) Unit =>
        centerExposureAtom noExposure ω.selectors) = 1 := by
  rw [center_atom_probability]
  simp [noExposure, exposureMass]

theorem duplicate_terminal_breaks_joint_identity :
    tableProbability (1 / 2 : ℝ) (fun ω : FiniteRoutingTables (Fin 2) Unit =>
      centerExposureAtom noExposure ω.selectors ∧
      localRoutingAllMiss distinctOwn duplicatedTerminal ω) ≠
    tableProbability (T := Unit) (1 / 2 : ℝ)
      (fun ω : FiniteRoutingTables (Fin 2) Unit =>
        centerExposureAtom noExposure ω.selectors) * (1 - (1 / 2) / 2) ^ 2 := by
  rw [duplicate_terminal_joint_probability, duplicate_terminal_atom_probability]
  norm_num

/-- Only avoidance of exposed own entries is dropped, with one genuine local test. -/
def exposedOwn : Unit → Option Bool := fun _ => some true
def singleOwn : Fin 1 → Unit := fun _ => ()
def singleTerminal : (Unit → Bool) → Fin 1 → Unit := fun _ _ => ()

theorem exposed_own_other_conditions :
    Function.Injective singleOwn ∧
      (∀ σ : Unit → Bool, centerExposureAtom exposedOwn σ →
        Function.Injective (singleTerminal σ)) := by
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ _ _ _ _ => Subsingleton.elim _ _⟩

theorem exposed_own_not_avoided : ¬∀ i : Fin 1, exposedOwn (singleOwn i) = none := by
  intro h
  simpa [exposedOwn, singleOwn] using h 0

theorem exposed_own_joint_probability :
    tableProbability (1 / 2 : ℝ) (fun ω : FiniteRoutingTables Unit Unit =>
      centerExposureAtom exposedOwn ω.selectors ∧
      localRoutingAllMiss singleOwn singleTerminal ω) = 1 / 4 := by
  unfold tableProbability
  rw [sum_unit_bool_functions]
  simp_rw [sum_unit_bool_functions]
  norm_num [bitTableWeight, bernoulliWeight, centerExposureAtom, exposedOwn,
    localRoutingAllMiss, localRoutingSuccess, singleOwn, singleTerminal]

theorem exposed_own_atom_probability :
    tableProbability (T := Unit) (1 / 2 : ℝ)
      (fun ω : FiniteRoutingTables Unit Unit =>
        centerExposureAtom exposedOwn ω.selectors) = 1 / 2 := by
  rw [center_atom_probability]
  simp [exposedOwn, exposureMass]

theorem exposed_own_breaks_joint_identity :
    tableProbability (1 / 2 : ℝ) (fun ω : FiniteRoutingTables Unit Unit =>
      centerExposureAtom exposedOwn ω.selectors ∧
      localRoutingAllMiss singleOwn singleTerminal ω) ≠
    tableProbability (T := Unit) (1 / 2 : ℝ)
      (fun ω : FiniteRoutingTables Unit Unit =>
        centerExposureAtom exposedOwn ω.selectors) * (1 - (1 / 2) / 2) ^ 1 := by
  rw [exposed_own_joint_probability, exposed_own_atom_probability]
  norm_num

/-- Both paths share selector 2; the routing permutation reads every selector. -/
def auxiliaryExposure : Fin 3 → Option Bool := fun s => if s = 2 then some true else none
def auxiliaryOwn : Fin 2 → Fin 3 := Fin.castAdd 1
def auxiliaryParity (σ : Fin 3 → Bool) : Bool := Bool.xor (Bool.xor (σ 0) (σ 1)) (σ 2)
def auxiliaryTerminals (σ : Fin 3 → Bool) (i : Fin 2) : Fin 2 :=
  if auxiliaryParity σ then i.rev else i

theorem shared_auxiliary_separation :
    LocalAddressSeparation auxiliaryExposure auxiliaryOwn auxiliaryTerminals := by
  refine ⟨Fin.castAdd_injective _ _, ?_, ?_⟩
  · intro i
    fin_cases i <;> simp [auxiliaryExposure, auxiliaryOwn]
  · intro σ _
    unfold auxiliaryTerminals
    split
    · exact Fin.rev_injective
    · exact Function.injective_id

theorem shared_auxiliary_atom_probability :
    tableProbability (T := Fin 2) (1 / 2 : ℝ)
      (fun ω : FiniteRoutingTables (Fin 3) (Fin 2) =>
        centerExposureAtom auxiliaryExposure ω.selectors) = 1 / 2 := by
  rw [center_atom_probability]
  norm_num [auxiliaryExposure, exposureMass, Fin.prod_univ_succ]

theorem shared_auxiliary_joint_probability :
    tableProbability (1 / 2 : ℝ) (fun ω : FiniteRoutingTables (Fin 3) (Fin 2) =>
      centerExposureAtom auxiliaryExposure ω.selectors ∧
      localRoutingAllMiss auxiliaryOwn auxiliaryTerminals ω) = 9 / 32 := by
  rw [joint_center_atom_all_miss _ _ _ _ shared_auxiliary_separation,
    shared_auxiliary_atom_probability]
  norm_num

/-- Changing any selector coordinate changes path 0's routed terminal address. -/
theorem shared_routing_depends_on_every_selector (s : Fin 3) :
    auxiliaryTerminals (fun _ => false) 0 ≠
      auxiliaryTerminals (fun t => if t = s then true else false) 0 := by
  fin_cases s <;> norm_num [auxiliaryTerminals, auxiliaryParity]

/-- The same auxiliary selector changes both routed terminal addresses. -/
theorem shared_auxiliary_changes_both_paths (i : Fin 2) :
    auxiliaryTerminals (fun _ => false) i ≠
      auxiliaryTerminals (fun t => if t = 2 then true else false) i := by
  fin_cases i <;> norm_num [auxiliaryTerminals, auxiliaryParity]

end ContinuumGeometric.ProbabilityControls

#print axioms ContinuumGeometric.ProbabilityControls.duplicate_own_breaks_joint_identity
#print axioms ContinuumGeometric.ProbabilityControls.duplicate_terminal_breaks_joint_identity
#print axioms ContinuumGeometric.ProbabilityControls.exposed_own_breaks_joint_identity
#print axioms ContinuumGeometric.ProbabilityControls.shared_auxiliary_joint_probability
#print axioms ContinuumGeometric.ProbabilityControls.shared_routing_depends_on_every_selector
#print axioms ContinuumGeometric.ProbabilityControls.shared_auxiliary_changes_both_paths
