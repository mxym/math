import Mathlib.Tactic

/-! Actual finite probability laws, signed marginal kernels, and total variation.
The feature matrix is arbitrary; image indicators will instantiate it.
No optimization theorem is assumed. -/

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {I J : Type*} [Fintype I]

def Probability (p : I → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

def TV (v : I → ℝ) : ℝ := (∑ i, |v i|) / 2

def Kernel (A : J → I → ℝ) (v : I → ℝ) : Prop :=
  (∑ i, v i = 0) ∧ ∀ j, ∑ i, A j i * v i = 0

def Match (A : J → I → ℝ) (p q : I → ℝ) : Prop :=
  ∀ j, ∑ i, A j i * p i = ∑ i, A j i * q i

theorem tv_nonneg (v : I → ℝ) : 0 ≤ TV v := by
  exact div_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) (by norm_num)

theorem tv_eq_zero_iff (v : I → ℝ) : TV v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hs : ∑ i, |v i| = 0 := by dsimp [TV] at h; linarith
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => abs_nonneg (v i)).mp hs
    funext i
    exact abs_eq_zero.mp (hi i (Finset.mem_univ i))
  · rintro rfl
    simp [TV]

theorem tv_pos (v : I → ℝ) (h : v ≠ 0) : 0 < TV v :=
  lt_of_le_of_ne (tv_nonneg v) (Ne.symm (mt (tv_eq_zero_iff v).mp h))

theorem tv_smul (a : ℝ) (v : I → ℝ) :
    TV (fun i => a * v i) = |a| * TV v := by
  simp only [TV, abs_mul, ← Finset.mul_sum]
  ring

theorem tv_neg (v : I → ℝ) : TV (fun i => -v i) = TV v := by
  simp [TV]

theorem kernel_of_match (A : J → I → ℝ) (p q : I → ℝ)
    (hp : Probability p) (hq : Probability q) (hm : Match A p q) :
    Kernel A (fun i => p i - q i) := by
  constructor
  · simp only [Finset.sum_sub_distrib, hp.2, hq.2, sub_self]
  · intro j
    simp only [mul_sub, Finset.sum_sub_distrib, hm j, sub_self]

theorem tv_probability_difference_le_one (p q : I → ℝ)
    (hp : Probability p) (hq : Probability q) :
    TV (fun i => p i - q i) ≤ 1 := by
  have hs : ∑ i, |p i - q i| ≤ ∑ i, (p i + q i) := by
    apply Finset.sum_le_sum
    intro i _
    calc
      |p i - q i| ≤ |p i| + |q i| := abs_sub _ _
      _ = p i + q i := by rw [abs_of_nonneg (hp.1 i), abs_of_nonneg (hq.1 i)]
  simp only [Finset.sum_add_distrib, hp.2, hq.2] at hs
  dsimp [TV]
  linarith

def posPart (v : I → ℝ) (i : I) : ℝ := max (v i) 0
def negPart (v : I → ℝ) (i : I) : ℝ := max (-v i) 0

omit [Fintype I] in
theorem part_difference (v : I → ℝ) (i : I) :
    posPart v i - negPart v i = v i := by
  dsimp [posPart, negPart]
  by_cases h : 0 ≤ v i
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith)]
    ring

omit [Fintype I] in
theorem part_sum (v : I → ℝ) (i : I) :
    posPart v i + negPart v i = |v i| := by
  dsimp [posPart, negPart]
  by_cases h : 0 ≤ v i
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]
    ring
  · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith),
      abs_of_neg (lt_of_not_ge h)]
    ring

theorem part_masses (v : I → ℝ) (h : ∑ i, v i = 0) :
    (∑ i, posPart v i) = TV v ∧ (∑ i, negPart v i) = TV v := by
  have hd : (∑ i, posPart v i) - (∑ i, negPart v i) = 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa only [part_difference] using h
  have hs : (∑ i, posPart v i) + (∑ i, negPart v i) = ∑ i, |v i| := by
    rw [← Finset.sum_add_distrib]
    simp only [part_sum]
  dsimp [TV]
  constructor <;> linarith

def jordanP (v : I → ℝ) (i : I) : ℝ := posPart v i / TV v
def jordanQ (v : I → ℝ) (i : I) : ℝ := negPart v i / TV v

theorem jordan_probabilities (A : J → I → ℝ) (v : I → ℝ)
    (hv : Kernel A v) (hne : v ≠ 0) :
    Probability (jordanP v) ∧ Probability (jordanQ v) := by
  have hd := tv_pos v hne
  have hm := part_masses v hv.1
  constructor
  · constructor
    · intro i
      exact div_nonneg (le_max_right _ _) hd.le
    · simp only [jordanP, ← Finset.sum_div, hm.1, div_self hd.ne']
  · constructor
    · intro i
      exact div_nonneg (le_max_right _ _) hd.le
    · simp only [jordanQ, ← Finset.sum_div, hm.2, div_self hd.ne']

theorem jordan_difference (v : I → ℝ) (i : I) :
    jordanP v i - jordanQ v i = v i / TV v := by
  dsimp [jordanP, jordanQ]
  rw [← sub_div, part_difference]

theorem jordan_match (A : J → I → ℝ) (v : I → ℝ)
    (hv : Kernel A v) : Match A (jordanP v) (jordanQ v) := by
  intro j
  apply sub_eq_zero.mp
  calc
    (∑ i, A j i * jordanP v i) - (∑ i, A j i * jordanQ v i) =
        ∑ i, A j i * (jordanP v i - jordanQ v i) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ = (∑ i, A j i * v i) / TV v := by
      simp only [jordan_difference, mul_div_assoc, Finset.sum_div]
    _ = 0 := by rw [hv.2 j, zero_div]

theorem jordan_disjoint (v : I → ℝ) (i : I) :
    jordanP v i = 0 ∨ jordanQ v i = 0 := by
  by_cases h : 0 ≤ v i
  · right
    simp [jordanQ, negPart, max_eq_right (show -v i ≤ 0 by linarith)]
  · left
    simp [jordanP, posPart, max_eq_right (le_of_not_ge h)]

theorem jordan_tv_one (v : I → ℝ) (hne : v ≠ 0) :
    TV (fun i => jordanP v i - jordanQ v i) = 1 := by
  have hd := tv_pos v hne
  simp_rw [jordan_difference, div_eq_mul_inv, mul_comm (v _) (TV v)⁻¹]
  rw [tv_smul, abs_of_pos (inv_pos.mpr hd), inv_mul_cancel₀ hd.ne']

end
end OrbitalMarginals
