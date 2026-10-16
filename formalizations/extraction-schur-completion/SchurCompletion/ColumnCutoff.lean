import SchurCompletion.AlternatingSupport

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum ExtractionRankSupport

noncomputable section

def prefixPositionPerm (l t : ℕ) (σ : Equiv.Perm (Fin l)) : Equiv.Perm (Fin (l+t)) where
  toFun := Fin.addCases (fun i => Fin.castAdd t (σ i)) (Fin.natAdd l)
  invFun := Fin.addCases (fun i => Fin.castAdd t (σ.symm i)) (Fin.natAdd l)
  left_inv := by intro i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp
  right_inv := by intro i; refine Fin.addCases ?_ ?_ i <;> intro j <;> simp

theorem prefixPositionPerm_left (l t : ℕ) (σ : Equiv.Perm (Fin l)) (i : Fin l) :
    prefixPositionPerm l t σ (Fin.castAdd t i) = Fin.castAdd t (σ i) := by
  simp [prefixPositionPerm]

theorem prefixPositionPerm_right (l t : ℕ) (σ : Equiv.Perm (Fin l)) (j : Fin t) :
    prefixPositionPerm l t σ (Fin.natAdd l j) = Fin.natAdd l j := by
  simp [prefixPositionPerm]

def prefixAntisymmetrizer (D l t : ℕ) : Matrix (Word D (l+t)) (Word D (l+t)) ℂ :=
  ∑ σ : Equiv.Perm (Fin l), (Equiv.Perm.sign σ : ℤ) •
    copyPermutationMatrix D (l+t) (prefixPositionPerm l t σ)⁻¹

theorem prefix_productVector_factor (D l t : ℕ) (σ : Equiv.Perm (Fin l))
    (z : Fin (l+t) → Fin D → ℂ) (w : Word D (l+t)) :
    productVector D (l+t) (z ∘ prefixPositionPerm l t σ) w =
      productVector D l ((z ∘ Fin.castAdd t) ∘ σ) (w ∘ Fin.castAdd t) *
        productVector D t (z ∘ Fin.natAdd l) (w ∘ Fin.natAdd l) := by
  simp only [productVector,Function.comp_apply,Fin.prod_univ_add,
    prefixPositionPerm_left,prefixPositionPerm_right]

theorem prefixAntisymmetrizer_productVector (D l t : ℕ)
    (z : Fin (l+t) → Fin D → ℂ) (w : Word D (l+t)) :
    (prefixAntisymmetrizer D l t *ᵥ productVector D (l+t) z) w =
      alternatingTensorMap D l (z ∘ Fin.castAdd t) (w ∘ Fin.castAdd t) *
        productVector D t (z ∘ Fin.natAdd l) (w ∘ Fin.natAdd l) := by
  simp only [prefixAntisymmetrizer,Matrix.sum_mulVec,Matrix.smul_mulVec,
    copyPermutation_productVector,Finset.sum_apply,Pi.smul_apply,prefix_productVector_factor]
  rw [alternatingTensorMap,MultilinearMap.alternatization_apply,Finset.sum_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  simp only [MultilinearMap.smul_apply,MultilinearMap.domDomCongr_apply,Pi.smul_apply,
    productTensorMultilinear_apply,Units.smul_def,smul_mul_assoc]
  rfl

theorem prefix_factor_rank_le (D l t : ℕ) (z : Fin (l+t) → Fin D → ℂ) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range (z ∘ Fin.castAdd t))) ≤
      Module.finrank ℂ (Submodule.span ℂ (Set.range z)) := by
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨i,rfl⟩
  exact ⟨Fin.castAdd t i,rfl⟩

/-- A column longer than the rank budget annihilates the actual iid common
support, with all unselected tensor positions kept on the original register. -/
theorem prefixAntisymmetrizer_annihilates_rankBudgetSpace (D l t s : ℕ) (hsl : s < l)
    (v : Word D (l+t) → ℂ) (hv : v ∈ rankBudgetSpace D (l+t) s) :
    prefixAntisymmetrizer D l t *ᵥ v = 0 := by
  have hle : rankBudgetSpace D (l+t) s ≤ LinearMap.ker (prefixAntisymmetrizer D l t).mulVecLin := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z,hz,rfl⟩
    change prefixAntisymmetrizer D l t *ᵥ productVector D (l+t) z = 0
    ext w
    rw [prefixAntisymmetrizer_productVector,
      alternatingTensorMap_rank_deficient D l s hsl _ ((prefix_factor_rank_le D l t z).trans hz)]
    simp
  exact hle hv

theorem prefixAntisymmetrizer_mul_rankBudgetProjector (D l t s : ℕ) (hsl : s < l) :
    prefixAntisymmetrizer D l t * rankBudgetProjector D (l+t) s = 0 := by
  ext v w
  have hw : (rankBudgetProjector D (l+t) s).col w ∈ rankBudgetSpace D (l+t) s := by
    rw [← rankBudgetProjector_range,Matrix.range_mulVecLin]
    exact Submodule.subset_span ⟨w,rfl⟩
  have h := congrFun (prefixAntisymmetrizer_annihilates_rankBudgetSpace D l t s hsl _ hw) v
  simpa only [Matrix.mulVec,dotProduct,Matrix.mul_apply,Matrix.col,Matrix.transpose_apply,
    Pi.zero_apply,Matrix.zero_apply] using h

end
end ExtractionSchur
