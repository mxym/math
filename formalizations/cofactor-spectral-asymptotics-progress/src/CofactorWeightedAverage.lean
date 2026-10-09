import CofactorCrossNormalForm

/-! Finite weighted permutation sums are unchanged by averaging a coordinate
array on both sides over block permutations. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace CofactorSpectral
variable {V C H : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]
  [Fintype H] [Nonempty H]
noncomputable section

theorem arrayPair_sum_left (p : H → (V → C) → ℂ) (q : (V → C) → ℂ) :
    arrayPair (fun f => ∑ h, p h f) q = ∑ h, arrayPair (p h) q := by
  unfold arrayPair
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]

theorem arrayPair_sum_right (p : (V → C) → ℂ) (q : H → (V → C) → ℂ) :
    arrayPair p (fun f => ∑ h, q h f) = ∑ h, arrayPair p (q h) := by
  unfold arrayPair
  simp_rw [star_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

theorem arrayPair_const_left (a : ℂ) (p q : (V → C) → ℂ) :
    arrayPair (fun f => a * p f) q = a * arrayPair p q := by
  simp [arrayPair, mul_assoc, Finset.mul_sum]

theorem arrayPair_const_right (a : ℂ) (p q : (V → C) → ℂ) :
    arrayPair p (fun f => a * q f) = star a * arrayPair p q := by
  unfold arrayPair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  simp only [star_mul]
  ring

def averageArray (φ : H → Equiv.Perm V) (p : (V → C) → ℂ) (f : V → C) : ℂ :=
  (Fintype.card H : ℂ)⁻¹ * ∑ h, p (f ∘ φ h)

def permSandwich (a b : Equiv.Perm V) : Equiv.Perm (Equiv.Perm V) where
  toFun σ := a.trans (σ.trans b)
  invFun σ := a.symm.trans (σ.trans b.symm)
  left_inv σ := by ext x; simp
  right_inv σ := by ext x; simp

theorem arrayPair_sandwich (p : (V → C) → ℂ) (a b σ : Equiv.Perm V) :
    arrayPair (fun f => p (f ∘ a)) (fun f => p ((f ∘ σ.symm) ∘ b)) =
      arrayCoefficient p (a.trans (σ.trans b.symm)) := by
  unfold arrayPair arrayCoefficient
  apply Fintype.sum_equiv (assignmentPerm (C := C) a)
  intro f
  have hf : ((f ∘ σ.symm) ∘ b) =
      ((f ∘ a) ∘ (a.trans (σ.trans b.symm)).symm) := by
    funext i
    simp [Function.comp_def]
  change p (f ∘ a) * star (p ((f ∘ σ.symm) ∘ b)) =
    p (f ∘ a) * star (p ((f ∘ a) ∘ (a.trans (σ.trans b.symm)).symm))
  rw [hf]

theorem arrayCoefficient_average (φ : H → Equiv.Perm V) (p : (V → C) → ℂ)
    (σ : Equiv.Perm V) :
    arrayCoefficient (averageArray φ p) σ =
      (Fintype.card H : ℂ)⁻¹ * star ((Fintype.card H : ℂ)⁻¹) *
        ∑ h, ∑ k, arrayCoefficient p ((φ h).trans (σ.trans (φ k).symm)) := by
  unfold arrayCoefficient averageArray
  rw [arrayPair_const_left, arrayPair_const_right, arrayPair_sum_left]
  simp_rw [arrayPair_sum_right, arrayPair_sandwich]
  simp only [arrayCoefficient, mul_assoc]

def weightedPermutationSum (w : Equiv.Perm V → ℂ) (p : (V → C) → ℂ) : ℂ :=
  ∑ σ : Equiv.Perm V, w σ * arrayCoefficient p σ

theorem weightedPermutationSum_average (φ : H → Equiv.Perm V)
    (w : Equiv.Perm V → ℂ) (p : (V → C) → ℂ)
    (hw : ∀ σ h k, w ((φ h).trans (σ.trans (φ k).symm)) = w σ) :
    weightedPermutationSum w (averageArray φ p) = weightedPermutationSum w p := by
  have hsum : ∀ h k, (∑ σ : Equiv.Perm V,
      w σ * arrayCoefficient p ((φ h).trans (σ.trans (φ k).symm))) =
        weightedPermutationSum w p := by
    intro h k
    unfold weightedPermutationSum
    apply Fintype.sum_equiv (permSandwich (φ h) (φ k).symm)
    intro σ
    rw [show permSandwich (φ h) (φ k).symm σ =
      (φ h).trans (σ.trans (φ k).symm) from rfl, hw]
  unfold weightedPermutationSum
  simp_rw [arrayCoefficient_average]
  have hfactor : (∑ σ : Equiv.Perm V,
      w σ * ((Fintype.card H : ℂ)⁻¹ * star ((Fintype.card H : ℂ)⁻¹) *
        ∑ h, ∑ k, arrayCoefficient p ((φ h).trans (σ.trans (φ k).symm)))) =
      ((Fintype.card H : ℂ)⁻¹ * star ((Fintype.card H : ℂ)⁻¹)) *
        ∑ h, ∑ k, ∑ σ : Equiv.Perm V,
          w σ * arrayCoefficient p ((φ h).trans (σ.trans (φ k).symm)) := by
    let c : ℂ := (Fintype.card H : ℂ)⁻¹ * star ((Fintype.card H : ℂ)⁻¹)
    change (∑ σ, w σ * (c * ∑ h, ∑ k, arrayCoefficient p
      ((φ h).trans (σ.trans (φ k).symm)))) = _
    calc
      _ = c * ∑ σ, ∑ h, ∑ k, w σ * arrayCoefficient p
          ((φ h).trans (σ.trans (φ k).symm)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro σ _
        rw [mul_left_comm]
        congr 1
        simp only [Finset.mul_sum]
      _ = _ := by
        congr 1
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro h _
        rw [Finset.sum_comm]
  rw [hfactor]
  simp_rw [hsum]
  have hn : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, star_inv₀, star_natCast]
  change ((Fintype.card H : ℂ)⁻¹ * (Fintype.card H : ℂ)⁻¹) *
    ((Fintype.card H : ℂ) * ((Fintype.card H : ℂ) * weightedPermutationSum w p)) =
      weightedPermutationSum w p
  field_simp

end
end CofactorSpectral
