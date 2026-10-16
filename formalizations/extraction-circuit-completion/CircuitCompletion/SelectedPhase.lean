import CircuitCompletion.Pauli

open scoped BigOperators
namespace CircuitCompletion

theorem run_pauliWords {n : ℕ} (hn : 0<n) (ss : List (Finset (Fin n)))
    (θ : Finset (Fin n) → ℝ) (v : Bits n → ℂ) :
    run (ss.flatMap (fun S => pauliWord hn S (θ S))) v=
      fun w => complexPhase ((ss.map (fun S => θ S*maskCharacter S w)).sum)*v w := by
  induction ss generalizing v with
  | nil => simp [run,denote,complexPhase]
  | cons S ss ih =>
    simp only [List.flatMap_cons,run_append,ih,pauliWord_action,List.map_cons,List.sum_cons]
    funext w
    simp only [complexPhase_add]
    ring

theorem walsh_mask_identity {n : ℕ} (x w : Bits n) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      maskCharacter S x*maskCharacter S w)=if w=x then (2 : ℝ)^n else 0 := by
  have hprod : (∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
      maskCharacter S x*maskCharacter S w)=
      ∏ i : Fin n,(1+boolSign (x i)*boolSign (w i)) := by
    simp only [maskCharacter,← Finset.prod_mul_distrib]
    exact (Finset.prod_one_add _).symm
  rw [hprod]
  by_cases h : w=x
  · subst w
    simp only [if_pos rfl]
    have he (b : Bool) : 1+boolSign b*boolSign b=(2 : ℝ) := by
      cases b <;> norm_num [boolSign]
    simp [he]
  · rw [if_neg h]
    obtain ⟨i,hi⟩ : ∃ i,w i≠x i := by
      by_contra hn
      apply h
      funext i
      by_contra hi
      exact hn ⟨i,hi⟩
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    cases hx : x i <;> cases hw : w i <;> simp_all [boolSign]

/-- Exact selected-string phase synthesis into actual one-wire gates and
CNOTs on the same register. This is the Pauli expansion part of the
ancilla-free two-level synthesis; no selective gate is a primitive. -/
noncomputable def selectedPhaseWord {n : ℕ} (hn : 0<n) (x : Bits n) (θ : ℝ) : Circuit n :=
  (Finset.univ : Finset (Fin n)).powerset.toList.flatMap
    (fun S => pauliWord hn S ((θ/(2 : ℝ)^n)*maskCharacter S x))

theorem selectedPhaseWord_action {n : ℕ} (hn : 0<n) (x : Bits n) (θ : ℝ)
    (v : Bits n → ℂ) :
    run (selectedPhaseWord hn x θ) v=
      fun w => complexPhase (if w=x then θ else 0)*v w := by
  unfold selectedPhaseWord
  rw [run_pauliWords]
  funext w
  have hs : (((Finset.univ : Finset (Fin n)).powerset.toList.map
      (fun S => θ/(2 : ℝ)^n*maskCharacter S x*maskCharacter S w)).sum)=
      if w=x then θ else 0 := by
    rw [Finset.sum_map_toList]
    simp only [mul_assoc]
    rw [← Finset.mul_sum,walsh_mask_identity]
    by_cases h : w=x
    · simp [h]
    · simp [h]
  rw [hs]

theorem selectedPhaseWord_length {n : ℕ} (hn : 0<n) (x : Bits n) (θ : ℝ) :
    (selectedPhaseWord hn x θ).length≤2^n*(2*n+1) := by
  simp only [selectedPhaseWord,List.length_flatMap]
  calc
    _ ≤ ((Finset.univ : Finset (Fin n)).powerset.toList.map (fun _ => 2*n+1)).sum := by
      apply List.sum_le_sum
      intro S hS
      exact pauliWord_length hn S _
    _ = 2^n*(2*n+1) := by simp

end CircuitCompletion
