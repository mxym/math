import CofactorCrossPositive

/-! The first-compound indicator inequality for all complex Hermitian PSD
matrices, derived from actual permutation fibers and finite contractions. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace CofactorSpectral
variable {V W S T : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W] [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]
noncomputable section

def permutationWeight (A : Matrix V V ℂ) (σ : Equiv.Perm V) : ℂ := ∏ r, A r (σ r)

theorem compound_eq_fiber_sum (A : Matrix V V ℂ) (i j : V) :
    compound A i j = ∑ σ : {σ : Equiv.Perm V // σ i = j}, permutationWeight A σ.val := by
  unfold compound
  rw [firstCofactor_eq_permutationFiber, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  unfold permutationWeight
  rw [Fintype.prod_eq_mul_prod_subtype_ne (fun r => A r (σ.val r)) i, σ.property]

theorem compound_eq_permutation_sum (A : Matrix V V ℂ) (i j : V) :
    compound A i j = ∑ σ : Equiv.Perm V,
      if σ i = j then permutationWeight A σ else 0 := by
  rw [compound_eq_fiber_sum]
  have h := (Finset.sum_subtype
    (p := fun σ : Equiv.Perm V => σ i = j)
    (F := inferInstance)
    (Finset.univ.filter (fun σ : Equiv.Perm V => σ i = j))
    (by simp) (permutationWeight A)).symm
  simpa only [Finset.sum_filter] using h

theorem compound_reindex (A : Matrix V V ℂ) (e : W ≃ V) (i j : W) :
    compound (A.submatrix e e) i j = compound A (e i) (e j) := by
  rw [compound_eq_permutation_sum, compound_eq_permutation_sum]
  apply Fintype.sum_equiv e.permCongr
  intro σ
  by_cases h : σ i = j
  · have he : e.permCongr σ (e i) = e j := by simp [Equiv.permCongr_apply, h]
    simp only [h, he, ite_true]
    unfold permutationWeight
    apply Fintype.prod_equiv e
    intro r
    simp [Matrix.submatrix, Equiv.permCongr_apply]
  · have he : e.permCongr σ (e i) ≠ e j := by
      intro heq
      apply h
      apply e.injective
      simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using heq
    simp [h, he]

theorem compound_cross_sum (A : Matrix (S ⊕ T) (S ⊕ T) ℂ) :
    (∑ s : S, ∑ t : T, compound A (Sum.inl s) (Sum.inr t)) =
      ∑ σ : Equiv.Perm (S ⊕ T), crossWeight σ * permutationWeight A σ := by
  simp_rw [compound_eq_permutation_sum]
  conv_lhs => arg 2; ext s; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  have hs : ∀ s : S, (∑ t : T, if σ (Sum.inl s) = Sum.inr t
      then permutationWeight A σ else 0) =
        if crossLeft σ s then permutationWeight A σ else 0 := by
    intro s
    unfold crossLeft
    cases hx : σ (Sum.inl s) <;> simp [hx, eq_comm]
  simp_rw [hs]
  rw [← Finset.sum_filter]
  simp [crossWeight, Fintype.card_subtype, Finset.sum_const, nsmul_eq_mul]

theorem compound_cross_sum_nonneg (A : Matrix (S ⊕ T) (S ⊕ T) ℂ)
    (hA : A.PosSemidef) : 0 ≤ ∑ s : S, ∑ t : T, compound A (Sum.inl s) (Sum.inr t) := by
  obtain ⟨v,rfl⟩ := psd_exists_complexGram A hA
  rw [compound_cross_sum]
  exact crossWeighted_permanent_nonneg v

theorem compound_indicator_sum_blocks (A : Matrix (S ⊕ T) (S ⊕ T) ℂ)
    (hA : A.PosSemidef) :
    (∑ s : S, ∑ t : S, compound A (Sum.inl s) (Sum.inl t)) ≤
      (Fintype.card S : ℂ) * A.permanent := by
  have hc := compound_cross_sum_nonneg A hA
  have hr : (∑ s : S, ∑ t : S, compound A (Sum.inl s) (Sum.inl t)) +
      (∑ s : S, ∑ t : T, compound A (Sum.inl s) (Sum.inr t)) =
        (Fintype.card S : ℂ) * A.permanent := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← Fintype.sum_sum_type, compound_row_sum]
    simp [nsmul_eq_mul]
  rw [← hr]
  exact le_add_of_nonneg_right hc

theorem compound_indicator_sum (A : Matrix V V ℂ) (hA : A.PosSemidef) (s : Finset V) :
    (∑ i ∈ s, ∑ j ∈ s, compound A i j) ≤ (s.card : ℂ) * A.permanent := by
  let e := Equiv.sumCompl (fun i : V => i ∈ s)
  have h := compound_indicator_sum_blocks (A.submatrix e e) (hA.submatrix e)
  have he : ∀ i j : {i : V // i ∈ s},
      compound (A.submatrix e e) (Sum.inl i) (Sum.inl j) = compound A i.val j.val := by
    intro i j
    exact compound_reindex A e _ _
  simp_rw [he] at h
  have hp : (A.submatrix e e).permanent = A.permanent := permanent_reindex A e
  rw [hp] at h
  have hs : Fintype.card {i : V // i ∈ s} = s.card := Fintype.card_coe s
  rw [hs] at h
  have ht : (∑ i : {i : V // i ∈ s}, ∑ j : {j : V // j ∈ s}, compound A i.val j.val) =
      ∑ i ∈ s, ∑ j ∈ s, compound A i j := by
    calc
      _ = ∑ i ∈ s, ∑ j : {j : V // j ∈ s}, compound A i j.val :=
        (Finset.sum_subtype (F := inferInstance) s (fun _ => Iff.rfl)
          (fun i => ∑ j : {j : V // j ∈ s}, compound A i j.val)).symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        exact (Finset.sum_subtype (F := inferInstance) s (fun _ => Iff.rfl)
          (fun j => compound A i j)).symm
  rw [ht] at h
  exact h

end
end CofactorSpectral
