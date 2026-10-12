import CofactorWeightedAverage

/-! Nonnegativity of the cross-block permanent sum, obtained by actual finite
two-sided averaging and squared coordinate contractions. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace CofactorSpectral
variable {S T C : Type*} [Fintype S] [DecidableEq S]
  [Fintype T] [DecidableEq T] [Fintype C] [DecidableEq C]
noncomputable section

def crossWeight (σ : Equiv.Perm (S ⊕ T)) : ℂ :=
  (Fintype.card {s : S // crossLeft σ s} : ℂ)

theorem crossWeight_block_invariant (σ : Equiv.Perm (S ⊕ T))
    (a c : Equiv.Perm S) (b d : Equiv.Perm T) :
    crossWeight ((a.sumCongr b).trans (σ.trans (c.sumCongr d))) = crossWeight σ := by
  let e : {s : S // crossLeft ((a.sumCongr b).trans (σ.trans (c.sumCongr d))) s} ≃
      {s : S // crossLeft σ s} := a.subtypeEquiv (fun s => by
    change ((c.sumCongr d) (σ (Sum.inl (a s)))).isRight ↔ (σ (Sum.inl (a s))).isRight
    cases σ (Sum.inl (a s)) <;> rfl)
  exact congrArg (fun n : ℕ => (n : ℂ)) (Fintype.card_congr e)

theorem crossWeight_nonneg (σ : Equiv.Perm (S ⊕ T)) : 0 ≤ crossWeight σ := by
  unfold crossWeight
  exact_mod_cast (Nat.zero_le _)

theorem weighted_cross_positive (u : (S → C) → ℂ) (v : (T → C) → ℂ) :
    0 ≤ weightedPermutationSum crossWeight (blockArray u v) := by
  let φ : Equiv.Perm S × Equiv.Perm T → Equiv.Perm (S ⊕ T) := fun h => h.1.sumCongr h.2
  have hw : ∀ σ h k, crossWeight ((φ h).trans (σ.trans (φ k).symm)) = crossWeight σ := by
    intro σ h k
    exact crossWeight_block_invariant σ h.1 k.1.symm h.2 k.2.symm
  rw [← weightedPermutationSum_average φ crossWeight (blockArray u v) hw]
  have havg : averageArray φ (blockArray u v) =
      blockArray (symmetrizeArray u) (symmetrizeArray v) := by
    funext f
    unfold averageArray
    rw [Fintype.card_prod]
    exact (blockArray_sum_symmetrized u v f).symm
  rw [havg]
  unfold weightedPermutationSum
  apply Finset.sum_nonneg
  intro σ _
  exact mul_nonneg (crossWeight_nonneg σ) (symmetricBlock_coefficient_nonneg u v σ)

theorem rowTensor_sum_blocks (v : S ⊕ T → C → ℂ) :
    rowTensor v = blockArray (rowTensor (fun s => v (Sum.inl s)))
      (rowTensor (fun t => v (Sum.inr t))) := by
  funext f
  exact Fintype.prod_sum_type _

theorem crossWeighted_permanent_nonneg (v : S ⊕ T → C → ℂ) :
    0 ≤ ∑ σ : Equiv.Perm (S ⊕ T), crossWeight σ * ∏ i, complexGram v i (σ i) := by
  have h := weighted_cross_positive (rowTensor (fun s => v (Sum.inl s)))
    (rowTensor (fun t => v (Sum.inr t)))
  rw [← rowTensor_sum_blocks v] at h
  simpa only [weightedPermutationSum, arrayCoefficient_rowTensor] using h

end
end CofactorSpectral
