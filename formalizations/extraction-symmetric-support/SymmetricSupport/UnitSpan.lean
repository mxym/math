import SymmetricSupport.Density
import Mathlib.Analysis.Real.Sqrt

open scoped BigOperators ComplexOrder
open Matrix

namespace SymmetricSupport

noncomputable section

def IsUnitVector {D : ℕ} (z : Fin D → ℂ) : Prop :=
  ∑ i, Complex.normSq (z i) = 1

def unitPurePower (D k : ℕ) (z : {z : Fin D → ℂ // IsUnitVector z}) : Word D k → ℂ :=
  purePower D k z.val

theorem purePower_smul (D k : ℕ) (c : ℂ) (z : Fin D → ℂ) :
    purePower D k (c • z) = c ^ k • purePower D k z := by
  ext w
  simp [purePower, Finset.prod_mul_distrib]

theorem purePower_zero (D k : ℕ) (hk : 0 < k) :
    purePower D k 0 = 0 := by
  ext w
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  simp [purePower, Nat.ne_of_gt hk]

theorem exists_unitVector_multiple {D : ℕ} (z : Fin D → ℂ) (hz : z ≠ 0) :
    ∃ (c : ℂ) (u : Fin D → ℂ), IsUnitVector u ∧ z = c • u := by
  classical
  have hi : ∃ i, z i ≠ 0 := by
    contrapose! hz
    ext i
    exact hz i
  obtain ⟨i, hi⟩ := hi
  have hpos : 0 < ∑ j, Complex.normSq (z j) := by
    exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i,
      Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩
  let r : ℝ := Real.sqrt (∑ j, Complex.normSq (z j))
  have hr : 0 < r := Real.sqrt_pos.mpr hpos
  have hc : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  let u : Fin D → ℂ := fun j => z j / (r : ℂ)
  refine ⟨r, u, ?_, ?_⟩
  · change (∑ j, Complex.normSq (z j / (r : ℂ))) = 1
    simp only [Complex.normSq_div, Complex.normSq_ofReal]
    rw [← Finset.sum_div]
    have hr2 : r * r = ∑ j, Complex.normSq (z j) := Real.mul_self_sqrt hpos.le
    rw [hr2]
    exact div_self (ne_of_gt hpos)
  · ext j
    change z j = (r : ℂ) * (z j / (r : ℂ))
    field_simp

theorem purePower_mem_unitPurePower_span (D k : ℕ) (hD : 0 < D) (z : Fin D → ℂ) :
    purePower D k z ∈ Submodule.span ℂ (Set.range (unitPurePower D k)) := by
  classical
  by_cases hk : k = 0
  · let e : Fin D → ℂ := Pi.single ⟨0, hD⟩ 1
    have he : IsUnitVector e := by
      simp [IsUnitVector, e, Pi.single_apply]
    have hp : purePower D k z = unitPurePower D k ⟨e, he⟩ := by
      ext w
      simp [unitPurePower, purePower, hk]
    rw [hp]
    exact Submodule.subset_span ⟨⟨e, he⟩, rfl⟩
  by_cases hz : z = 0
  · rw [hz, purePower_zero D k (Nat.pos_of_ne_zero hk)]
    exact Submodule.zero_mem _
  obtain ⟨c, u, hu, rfl⟩ := exists_unitVector_multiple z hz
  rw [purePower_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩)

/-- Actual normalized pure iid vectors generate the whole symmetric support. -/
theorem symmetricProjector_range_eq_unitPurePower_span (D k : ℕ) (hD : 0 < D) :
    LinearMap.range (symmetricProjector D k).mulVecLin =
      Submodule.span ℂ (Set.range (unitPurePower D k)) := by
  rw [symmetricProjector_range_eq_purePower_span]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    exact purePower_mem_unitPurePower_span D k hD z
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    exact Submodule.subset_span ⟨z.val, rfl⟩

theorem unitVector_trace (D k : ℕ) (z : Fin D → ℂ) (hz : IsUnitVector z) :
    (purePowerDensity D k z).trace = 1 := by
  apply purePowerDensity_trace_one
  calc
    (∑ i, z i * star (z i)) = ∑ i, (Complex.normSq (z i) : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Complex.mul_conj _
    _ = ((∑ i, Complex.normSq (z i) : ℝ) : ℂ) := by simp
    _ = 1 := by exact_mod_cast hz

/-- A linear effect fixing every actual normalized pure iid vector fixes all of P's range. -/
theorem fixes_unitPurePower_mul_symmetricProjector (D k : ℕ) (hD : 0 < D)
    (M : Matrix (Word D k) (Word D k) ℂ)
    (hM : ∀ z : Fin D → ℂ, IsUnitVector z →
      M.mulVec (purePower D k z) = purePower D k z) :
    M * symmetricProjector D k = symmetricProjector D k := by
  classical
  let F : (Word D k → ℂ) →ₗ[ℂ] (Word D k → ℂ) := M.mulVecLin - LinearMap.id
  have hspan : Submodule.span ℂ (Set.range (unitPurePower D k)) ≤ LinearMap.ker F := by
    apply Submodule.span_le.mpr
    rintro _ ⟨z, rfl⟩
    change M.mulVec (purePower D k z.val) - purePower D k z.val = 0
    rw [hM z.val z.property, sub_self]
  have hfix : ∀ x, M.mulVec ((symmetricProjector D k).mulVec x) =
      (symmetricProjector D k).mulVec x := by
    intro x
    have hx : (symmetricProjector D k).mulVec x ∈
        LinearMap.range (symmetricProjector D k).mulVecLin := ⟨x, rfl⟩
    rw [symmetricProjector_range_eq_unitPurePower_span D k hD] at hx
    have h := hspan hx
    change M.mulVec ((symmetricProjector D k).mulVec x) -
      (symmetricProjector D k).mulVec x = 0 at h
    exact sub_eq_zero.mp h
  ext x y
  have hy := congrArg (fun v => v x) (hfix (Pi.single y 1))
  rw [Matrix.mulVec_mulVec] at hy
  simpa only [Matrix.mulVec_single, MulOpposite.op_one, one_smul,
    Matrix.col, Matrix.transpose_apply] using hy

end
end SymmetricSupport
