import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite-law specialization of entry005 v3, Section 3, equation (3.1).
The argument applies to any real values and nonnegative weights; neither
probability normalization nor a determinant identity is assumed. -/
namespace Mxym.FiniteDefect
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

noncomputable def positiveMass (p z : ι → ℝ) : ℝ := ∑ i, p i * max (z i) 0
noncomputable def negativeMass (p z : ι → ℝ) : ℝ := ∑ i, p i * max (-z i) 0

theorem mean_decomposition (p z : ι → ℝ) :
    (∑ i, p i * z i) = positiveMass p z - negativeMass p z := by
  unfold positiveMass negativeMass
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hz : 0 ≤ z i
  · rw [max_eq_left hz, max_eq_right (by linarith : -z i ≤ 0)]
    ring
  · rw [max_eq_right (le_of_not_ge hz), max_eq_left (by linarith : 0 ≤ -z i)]
    ring

theorem absolute_decomposition (p z : ι → ℝ) :
    (∑ i, p i * |z i|) = positiveMass p z + negativeMass p z := by
  unfold positiveMass negativeMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hz : 0 ≤ z i
  · rw [max_eq_left hz, max_eq_right (by linarith : -z i ≤ 0), abs_of_nonneg hz]
    ring
  · rw [max_eq_right (le_of_not_ge hz), max_eq_left (by linarith : 0 ≤ -z i),
      abs_of_nonpos (le_of_not_ge hz)]
    ring

theorem defect_identity (p z : ι → ℝ) :
    (∑ i, p i * |z i|) - |∑ i, p i * z i| =
      2 * min (positiveMass p z) (negativeMass p z) := by
  rw [absolute_decomposition p z, mean_decomposition p z]
  rcases le_total (positiveMass p z) (negativeMass p z) with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem finite_jensen (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    |∑ i, p i * z i| ≤ ∑ i, p i * |z i| := by
  have hpos : 0 ≤ positiveMass p z :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (le_max_right _ _))
  have hneg : 0 ≤ negativeMass p z :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (le_max_right _ _))
  have h := defect_identity p z
  have hm : 0 ≤ min (positiveMass p z) (negativeMass p z) := le_min hpos hneg
  linarith

theorem defect_lower_bound (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (i j : ι) (hi : 0 ≤ z i) (hj : z j ≤ 0) :
    2 * min (p i * z i) (p j * (-z j)) ≤
      (∑ k, p k * |z k|) - |∑ k, p k * z k| := by
  have hpos : p i * z i ≤ positiveMass p z := by
    have h := Finset.single_le_sum (f := fun k => p k * max (z k) 0)
      (fun k (_ : k ∈ Finset.univ) => mul_nonneg (hp k) (le_max_right _ _))
      (Finset.mem_univ i)
    simpa [positiveMass, max_eq_left hi] using h
  have hneg : p j * (-z j) ≤ negativeMass p z := by
    have h := Finset.single_le_sum (f := fun k => p k * max (-z k) 0)
      (fun k (_ : k ∈ Finset.univ) => mul_nonneg (hp k) (le_max_right _ _))
      (Finset.mem_univ j)
    simpa [negativeMass, max_eq_left (neg_nonneg.mpr hj)] using h
  rw [defect_identity]
  exact mul_le_mul_of_nonneg_left (min_le_min hpos hneg) (by norm_num)

theorem strict_of_opposite_signs (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (i j : ι) (hpi : 0 < p i) (hpj : 0 < p j) (hi : 0 < z i) (hj : z j < 0) :
    |∑ k, p k * z k| < ∑ k, p k * |z k| := by
  have h := defect_lower_bound p z hp i j hi.le hj.le
  have hm : 0 < min (p i * z i) (p j * (-z j)) :=
    lt_min (mul_pos hpi hi) (mul_pos hpj (neg_pos.mpr hj))
  linarith

 theorem positive_mass_eq_zero_iff (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    positiveMass p z = 0 ↔ ∀ i, 0 < p i → z i ≤ 0 := by
  constructor
  · intro h i hpi
    have hb := Finset.single_le_sum (f := fun k => p k * max (z k) 0)
      (fun k (_ : k ∈ Finset.univ) => mul_nonneg (hp k) (le_max_right _ _))
      (Finset.mem_univ i)
    change p i * max (z i) 0 ≤ positiveMass p z at hb
    have hz : p i * max (z i) 0 = 0 := by
      rw [h] at hb
      exact le_antisymm hb (mul_nonneg (hp i) (le_max_right _ _))
    have hmax := (mul_eq_zero.mp hz).resolve_left (ne_of_gt hpi)
    have hle := le_max_left (z i) 0
    rwa [hmax] at hle
  · intro h
    apply Finset.sum_eq_zero
    intro i _
    by_cases hpi : p i = 0
    · simp [hpi]
    · have hip : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm hpi)
      rw [max_eq_right (h i hip), mul_zero]

 theorem negative_mass_eq_zero_iff (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    negativeMass p z = 0 ↔ ∀ i, 0 < p i → 0 ≤ z i := by
  simpa [positiveMass, negativeMass] using positive_mass_eq_zero_iff p (fun i => -z i) hp

/-- Exact equality characterization of finite weighted Jensen / triangle inequality. -/
 theorem finite_jensen_eq_iff (p z : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    |∑ i, p i * z i| = (∑ i, p i * |z i|) ↔
      (∀ i, 0 < p i → 0 ≤ z i) ∨ (∀ i, 0 < p i → z i ≤ 0) := by
  have hP : 0 ≤ positiveMass p z :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (le_max_right _ _))
  have hQ : 0 ≤ negativeMass p z :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hp i) (le_max_right _ _))
  have he : |∑ i, p i * z i| = (∑ i, p i * |z i|) ↔
      positiveMass p z = 0 ∨ negativeMass p z = 0 := by
    constructor
    · intro h
      have hz : min (positiveMass p z) (negativeMass p z) = 0 := by
        have hd := defect_identity p z
        linarith
      rcases le_total (positiveMass p z) (negativeMass p z) with hle | hle
      · left; rwa [min_eq_left hle] at hz
      · right; rwa [min_eq_right hle] at hz
    · intro h
      have hz : min (positiveMass p z) (negativeMass p z) = 0 := by
        rcases h with h | h
        · rw [h, min_eq_left hQ]
        · rw [h, min_eq_right hP]
      have hd := defect_identity p z
      rw [hz] at hd
      linarith
  rw [he, positive_mass_eq_zero_iff p z hp, negative_mass_eq_zero_iff p z hp]
  exact or_comm

end Mxym.FiniteDefect
