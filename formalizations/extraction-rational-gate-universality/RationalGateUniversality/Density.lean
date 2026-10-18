import RationalGateUniversality.Euler

open CircuitRecursion RationalGateProvider
namespace RationalGateUniversality

set_option maxHeartbeats 1000000

theorem zTorus_phaseCircle : zTorus phaseCircle = RationalGateInterface.rationalGate 0 := by
  apply ext_first_row <;> rfl

theorem xTorus_phaseCircle : xTorus phaseCircle = RationalGateInterface.rationalGate 2 := by
  apply ext_first_row <;>
    norm_num [xTorus, phaseCircle, rationalPhase_formula, RationalGateInterface.rationalGate,
      quaternionSU2, quaternionMatrix, Complex.div_re, Complex.div_im]
  ring

/-- The concrete inverse-closed four-gate alphabet generates a dense subgroup
of the actual matrix SU2. No Euler factorization or density certificate is an
input: the factorization and circle density are proved upstream. -/
theorem rationalGate_dense :
    Dense (Subgroup.closure (Set.range RationalGateInterface.rationalGate) : Set SU2) := by
  let : IsTopologicalGroup SU2 := su2_topologicalGroup
  let S : Subgroup SU2 := Subgroup.closure (Set.range RationalGateInterface.rationalGate)
  let H : Subgroup SU2 := S.topologicalClosure
  have hZ : zTorus phaseCircle ∈ H := by
    rw [zTorus_phaseCircle]
    exact Subgroup.le_topologicalClosure S (Subgroup.subset_closure (Set.mem_range_self 0))
  have hX : xTorus phaseCircle ∈ H := by
    rw [xTorus_phaseCircle]
    exact Subgroup.le_topologicalClosure S (Subgroup.subset_closure (Set.mem_range_self 2))
  have hZall : ∀ z : Circle, zTorus z ∈ H := by
    intro z
    exact phaseCircle_dense_zpowers.induction_on (p := fun w : Circle => zTorus w ∈ H) z
      ((Subgroup.isClosed_topologicalClosure S).preimage continuous_zTorus)
      (fun n => by
        change zHom (phaseCircle^n) ∈ H
        rw [map_zpow]
        exact H.zpow_mem hZ n)
  have hXall : ∀ z : Circle, xTorus z ∈ H := by
    intro z
    exact phaseCircle_dense_zpowers.induction_on (p := fun w : Circle => xTorus w ∈ H) z
      ((Subgroup.isClosed_topologicalClosure S).preimage continuous_xTorus)
      (fun n => by
        change xHom (phaseCircle^n) ∈ H
        rw [map_zpow]
        exact H.zpow_mem hX n)
  have hAll : ∀ U : SU2, U ∈ H := by
    intro U
    obtain ⟨s,t,r,he⟩ := su2_euler U
    rw [he]
    exact H.mul_mem (H.mul_mem (hZall s) (hXall t)) (hZall r)
  change Dense (S : Set SU2)
  rw [dense_iff_closure_eq]
  change (H : Set SU2) = Set.univ
  exact Set.eq_univ_of_forall hAll

/-- One fixed offline net exists for this concrete alphabet. This is a
mathematical existence result, not a bound on generating the table. -/
theorem rationalGate_precomputedNet :
    ∃ (L n : ℕ) (table : Fin (n+1) → List (Fin 4)),
      (∀ j, (table j).length ≤ L) ∧
      (∀ U : SU2, ∃ j, unitaryDistance (su2AsUnitary U)
        (su2AsUnitary (instructionWordValue RationalGateInterface.rationalGate (table j))) ≤ 1/576) := by
  exact precomputedNet_exists RationalGateInterface.rationalGate
    (fun i => ⟨RationalGateInterface.inverseLabel i, RationalGateInterface.rationalGate_inverse i⟩)
    rationalGate_dense

end RationalGateUniversality
