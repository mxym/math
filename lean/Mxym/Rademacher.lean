import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Compact
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

namespace Mxym.Rademacher
open scoped BigOperators Classical
open Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Each Boolean is a uniform sign; all functions form the independent product law. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem abs_sign (b : Bool) : |sign b| = 1 := by cases b <;> norm_num [sign]
@[simp] theorem sign_not (b : Bool) : sign (!b) = -sign b := by cases b <;> norm_num [sign]

noncomputable def signedSum (c : ι → ℝ) (ε : ι → Bool) : ℝ :=
  ∑ i, sign (ε i) * c i

noncomputable def mean (c : ι → ℝ) : ℝ :=
  (∑ ε : ι → Bool, |signedSum c ε|) / Fintype.card (ι → Bool)

 theorem sign_space_card : Fintype.card (ι → Bool) = 2 ^ Fintype.card ι := by
  simp

 theorem mean_nonneg (c : ι → ℝ) : 0 ≤ mean c := by
  unfold mean
  positivity

 theorem mean_smul (a : ℝ) (c : ι → ℝ) : mean (a • c) = |a| * mean c := by
  have hs (ε : ι → Bool) : signedSum (a • c) ε = a * signedSum c ε := by
    simp only [signedSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [mean, hs, abs_mul, ← Finset.mul_sum]
  ring

 theorem convex_mean : ConvexOn ℝ univ (mean (ι := ι)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hs (ε : ι → Bool) :
      signedSum (a • x + b • y) ε = a * signedSum x ε + b * signedSum y ε := by
    simp only [signedSum, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hsum : (∑ ε : ι → Bool, |signedSum (a • x + b • y) ε|) ≤
      a * (∑ ε : ι → Bool, |signedSum x ε|) +
      b * (∑ ε : ι → Bool, |signedSum y ε|) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro ε _
    rw [hs]
    simpa [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using
      abs_add_le (a * signedSum x ε) (b * signedSum y ε)
  change mean (a • x + b • y) ≤ a * mean x + b * mean y
  unfold mean
  calc
    _ ≤ (a * (∑ ε : ι → Bool, |signedSum x ε|) +
      b * (∑ ε : ι → Bool, |signedSum y ε|)) / Fintype.card (ι → Bool) :=
        div_le_div_of_nonneg_right hsum (by positivity)
    _ = _ := by ring

 theorem continuous_mean : Continuous (mean (ι := ι)) := by
  unfold mean signedSum
  fun_prop

private noncomputable def flip (k : ι) (ε : ι → Bool) : ι → Bool :=
  Function.update ε k (!ε k)

omit [Fintype ι] in
private theorem flip_flip (k : ι) (ε : ι → Bool) :
    flip k (flip k ε) = ε := by
  funext i
  by_cases hi : i = k
  · subst i; simp [flip]
  · simp [flip, hi]

private noncomputable def flipEquiv (k : ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun := flip k
  invFun := flip k
  left_inv := flip_flip k
  right_inv := flip_flip k

 theorem abs_pair (a z : ℝ) (hz : |z| ≤ |a|) :
    |a + z| + |-a + z| = 2 * |a| := by
  rcases le_total 0 a with ha | ha
  · rw [abs_of_nonneg ha] at hz ⊢
    have hzp := le_trans (le_abs_self z) hz
    have hzm := le_trans (neg_le_abs z) hz
    rw [abs_of_nonneg (by linarith : 0 ≤ a + z),
      abs_of_nonpos (by linarith : -a + z ≤ 0)]
    ring
  · rw [abs_of_nonpos ha] at hz ⊢
    have hzp := le_trans (le_abs_self z) hz
    have hzm := le_trans (neg_le_abs z) hz
    rw [abs_of_nonpos (by linarith : a + z ≤ 0),
      abs_of_nonneg (by linarith : 0 ≤ -a + z)]
    ring

/-- The second equality mechanism, valid for any number of coefficients. -/
 theorem mean_eq_of_dominant (c : ι → ℝ) (k : ι)
    (hk : (∑ i, |c i|) - |c k| ≤ |c k|) : mean c = |c k| := by
  classical
  let Z (ε : ι → Bool) : ℝ := ∑ i ∈ Finset.univ.erase k, sign (ε i) * c i
  have hz (ε : ι → Bool) : |Z ε| ≤ |sign (ε k) * c k| := by
    rw [abs_mul, abs_sign, one_mul]
    have h := Finset.abs_sum_le_sum_abs (s := Finset.univ.erase k)
      (fun i => sign (ε i) * c i)
    simp only [abs_mul, abs_sign, one_mul] at h
    have he : (∑ i ∈ Finset.univ.erase k, |c i|) = (∑ i, |c i|) - |c k| := by
      have he := Finset.sum_erase_add Finset.univ (fun i => |c i|) (Finset.mem_univ k)
      linarith
    exact h.trans (he ▸ hk)
  have hs (ε : ι → Bool) : signedSum c ε = sign (ε k) * c k + Z ε := by
    have he := Finset.sum_erase_add Finset.univ (fun i => sign (ε i) * c i)
      (Finset.mem_univ k)
    change _ = _
    unfold signedSum
    linarith [he]
  have hf (ε : ι → Bool) : signedSum c (flip k ε) = -(sign (ε k) * c k) + Z ε := by
    rw [hs]
    have he : Z (flip k ε) = Z ε := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [flip, (Finset.mem_erase.mp hi).1]
    rw [he]
    simp [flip, neg_mul]
  have hp (ε : ι → Bool) : |signedSum c ε| + |signedSum c (flip k ε)| = 2 * |c k| := by
    rw [hs, hf]
    simpa [abs_mul] using abs_pair (sign (ε k) * c k) (Z ε) (hz ε)
  have heq : (∑ ε : ι → Bool, |signedSum c (flip k ε)|) =
      (∑ ε : ι → Bool, |signedSum c ε|) := by
    exact Fintype.sum_equiv (flipEquiv k) _ _ (fun _ => rfl)
  have h := congrArg (fun f : (ι → Bool) → ℝ => ∑ ε, f ε) (funext hp)
  simp only [Finset.sum_add_distrib, heq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  have hn : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := by positivity
  unfold mean
  apply (div_eq_iff hn).2
  nlinarith [h]

/-- Normalized nonnegative coefficients of total mass one, each capped at one half. -/
def balancedPolytope : Set (ι → ℝ) :=
  {t | (∀ i, 0 ≤ t i ∧ t i ≤ 1 / 2) ∧ (∑ i, t i) = 1}

omit [DecidableEq ι] in
 theorem compact_balancedPolytope : IsCompact (balancedPolytope (ι := ι)) := by
  have he : balancedPolytope (ι := ι) =
      Icc (0 : ι → ℝ) (fun _ => (1 / 2 : ℝ)) ∩ {t : ι → ℝ | (∑ i, t i) = 1} := by
    ext t
    simp only [balancedPolytope, mem_ofPred_eq, mem_inter_iff, mem_Icc, Pi.le_def,
      Pi.zero_apply]
    aesop
  rw [he]
  exact isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)

omit [DecidableEq ι] in
 theorem convex_balancedPolytope : Convex ℝ (balancedPolytope (ι := ι)) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    change 0 ≤ a * x i + b * y i ∧ a * x i + b * y i ≤ 1 / 2
    constructor
    · exact add_nonneg (mul_nonneg ha (hx.1 i).1) (mul_nonneg hb (hy.1 i).1)
    · nlinarith [mul_nonneg ha (sub_nonneg.mpr (hx.1 i).2),
        mul_nonneg hb (sub_nonneg.mpr (hy.1 i).2)]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, hx.2, hy.2, mul_one, hab]

/-- An extreme point must saturate the one-half cap. -/
 theorem extreme_has_half (t : ι → ℝ)
    (ht : t ∈ (balancedPolytope (ι := ι)).extremePoints ℝ) :
    ∃ i, t i = 1 / 2 := by
  classical
  by_contra h
  have hlt (i : ι) : t i < 1 / 2 := lt_of_le_of_ne (ht.1.1 i).2 (by aesop)
  obtain ⟨i, hi⟩ : ∃ i, 0 < t i := by
    by_contra hn
    push Not at hn
    have := Finset.sum_nonpos (fun i (_ : i ∈ Finset.univ) => hn i)
    linarith [ht.1.2]
  obtain ⟨j, hji, hj⟩ : ∃ j, j ≠ i ∧ 0 < t j := by
    by_contra hn
    push Not at hn
    have hs : (∑ j, t j) = t i := by
      apply Finset.sum_eq_single i
      · intro j _ hji
        exact le_antisymm (hn j hji) (ht.1.1 j).1
      · simp
    linarith [ht.1.2, hlt i]
  let δ : ℝ := min (min (t i) (t j)) (min (1 / 2 - t i) (1 / 2 - t j))
  have hδ : 0 < δ := lt_min (lt_min hi hj) (lt_min (by linarith [hlt i]) (by linarith [hlt j]))
  have hd1 : δ ≤ t i := (min_le_left _ _).trans (min_le_left _ _)
  have hd2 : δ ≤ t j := (min_le_left _ _).trans (min_le_right _ _)
  have hd3 : δ ≤ 1 / 2 - t i := (min_le_right _ _).trans (min_le_left _ _)
  have hd4 : δ ≤ 1 / 2 - t j := (min_le_right _ _).trans (min_le_right _ _)
  let d : ι → ℝ := Pi.single i δ - Pi.single j δ
  have hds : (∑ k, d k) = 0 := by simp [d, Finset.sum_sub_distrib]
  have hu : t + d ∈ balancedPolytope (ι := ι) := by
    constructor
    · intro k
      by_cases hki : k = i
      · subst k; simp [d, hji.symm]; constructor <;> linarith [(ht.1.1 i).1]
      · by_cases hkj : k = j
        · subst k; simp [d, hji]; constructor <;> linarith [(ht.1.1 j).2]
        · simpa [d, Pi.single_apply, hki, hkj] using ht.1.1 k
    · simp [Finset.sum_add_distrib, ht.1.2, hds]
  have hv : t - d ∈ balancedPolytope (ι := ι) := by
    constructor
    · intro k
      by_cases hki : k = i
      · subst k; simp [d, hji.symm]; constructor <;> linarith [(ht.1.1 i).2]
      · by_cases hkj : k = j
        · subst k; simp [d, hji]; constructor <;> linarith [(ht.1.1 j).1]
        · simpa [d, Pi.single_apply, hki, hkj] using ht.1.1 k
    · simp [Finset.sum_sub_distrib, ht.1.2, hds]
  have hm : t ∈ openSegment ℝ (t + d) (t - d) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have he := ht.2 hu hv hm
  have hei := congrFun he i
  simp [d, hji.symm] at hei
  linarith

 theorem normalized_bound (t : ι → ℝ) (ht : t ∈ balancedPolytope (ι := ι)) :
    mean t ≤ 1 / 2 := by
  have hsub : (balancedPolytope (ι := ι)).extremePoints ℝ ⊆
      {t : ι → ℝ | mean t ≤ 1 / 2} := by
    intro t ht
    obtain ⟨i, hi⟩ := extreme_has_half t ht
    have habs : (∑ j, |t j|) = 1 := by
      simp only [abs_of_nonneg (ht.1.1 _).1, ht.1.2]
    have he := mean_eq_of_dominant t i (by rw [habs, abs_of_nonneg (ht.1.1 i).1, hi]; norm_num)
    simp [he, hi]
  have hc : Convex ℝ {t : ι → ℝ | mean t ≤ 1 / 2} := by
    simpa using (convex_mean (ι := ι)).convex_le (1 / 2 : ℝ)
  have hclosed : IsClosed {t : ι → ℝ | mean t ≤ 1 / 2} :=
    isClosed_le continuous_mean continuous_const
  have hm := closure_minimal (convexHull_min hsub hc) hclosed
  rw [closure_convexHull_extremePoints compact_balancedPolytope convex_balancedPolytope] at hm
  exact hm ht

 theorem mean_abs (c : ι → ℝ) : mean (fun i => |c i|) = mean c := by
  let T (ε : ι → Bool) : ι → Bool := fun i => if c i < 0 then !ε i else ε i
  have hT (ε : ι → Bool) : T (T ε) = ε := by
    funext i
    by_cases hi : c i < 0 <;> simp [T, hi]
  let e : (ι → Bool) ≃ (ι → Bool) := ⟨T, T, hT, hT⟩
  have hs (ε : ι → Bool) : signedSum (fun i => |c i|) ε = signedSum c (e ε) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : c i < 0
    · simp [e, T, hi, abs_of_neg hi, sign_not]
    · simp [e, T, hi, abs_of_nonneg (le_of_not_gt hi)]
  unfold mean
  congr 1
  exact Fintype.sum_equiv e _ _ (fun ε => congrArg abs (hs ε))

 theorem mean_zero : mean (0 : ι → ℝ) = 0 := by simp [mean, signedSum]

/-- Entry005 v3 Lemma 6.1 / v4 equation (2.2), for arbitrary finite real coefficients. -/
 theorem balanced_bound (c : ι → ℝ)
    (hbal : ∀ i, |c i| ≤ (∑ j, |c j|) / 2) :
    mean c ≤ (∑ j, |c j|) / 2 := by
  let M : ℝ := ∑ j, |c j|
  have hM : 0 ≤ M := Finset.sum_nonneg (fun i _ => abs_nonneg (c i))
  by_cases hzero : M = 0
  · have hc : c = 0 := by
      funext i
      have h := hbal i
      change |c i| ≤ M / 2 at h
      rw [hzero] at h
      have habs : |c i| = 0 := by linarith [abs_nonneg (c i)]
      exact abs_eq_zero.mp habs
    rw [hc, mean_zero]
    simp
  · have hpos : 0 < M := lt_of_le_of_ne hM (Ne.symm hzero)
    let t : ι → ℝ := fun i => |c i| / M
    have ht : t ∈ balancedPolytope (ι := ι) := by
      constructor
      · intro i
        constructor
        · exact div_nonneg (abs_nonneg _) hM
        · apply (div_le_iff₀ hpos).2
          have h := hbal i
          change |c i| ≤ M / 2 at h
          linarith
      · simp only [t, div_eq_mul_inv, ← Finset.sum_mul]
        exact mul_inv_cancel₀ hzero
    have hscale : M • t = fun i => |c i| := by
      funext i
      change M * (|c i| / M) = |c i|
      field_simp
    have hm := mean_smul M t
    rw [hscale, mean_abs, abs_of_pos hpos] at hm
    have hb := normalized_bound t ht
    change mean c ≤ M / 2
    nlinarith

 theorem mean_eq_half_of_half_mass (c : ι → ℝ) (k : ι)
    (hk : |c k| = (∑ i, |c i|) / 2) :
    mean c = (∑ i, |c i|) / 2 := by
  rw [← hk]
  apply mean_eq_of_dominant
  linarith [hk]

end Mxym.Rademacher
