import GaussianQuantile

/-! Ordered residual-mass entropy for the Gaussian mass-envelope theorem. -/
open scoped BigOperators

namespace GaussianMeasureBridge

noncomputable def residualMass {k : ℕ} (p : Fin k → ℝ) (i : ℕ) : ℝ :=
  ∑ j, if i ≤ j.val then p j else 0

lemma residualMass_nonneg {k : ℕ} (p : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i) (i : ℕ) :
    0 ≤ residualMass p i := by
  apply Finset.sum_nonneg
  intro j _
  split_ifs
  · exact hp j
  · exact le_rfl

lemma residualMass_pos {k : ℕ} (p : Fin k → ℝ) (hp : ∀ i, 0 < p i) (i : Fin k) :
    0 < residualMass p i.val := by
  have h : p i ≤ residualMass p i.val := by
    have h := Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin k => if i.val ≤ j.val then p j else 0)
      (fun j _ => by split_ifs; exact (hp j).le; exact le_rfl) (Finset.mem_univ i)
    simpa only [le_refl, if_true] using h
  exact (hp i).trans_le h

lemma residualMass_antitone {k : ℕ} (p : Fin k → ℝ) (hp : ∀ i, 0 ≤ p i) :
    Antitone (residualMass p) := by
  intro a b hab
  apply Finset.sum_le_sum
  intro j _
  by_cases hb : b ≤ j.val
  · simp only [hb, hab.trans hb, if_true, le_refl]
  · by_cases ha : a ≤ j.val <;> simp [hb, ha, hp j]

lemma residualMass_zero {k : ℕ} (p : Fin k → ℝ) : residualMass p 0 = ∑ j, p j := by
  simp [residualMass]

lemma residualMass_length {k : ℕ} (p : Fin k → ℝ) : residualMass p k = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  exact if_neg (Nat.not_le.mpr j.isLt)

lemma residualMass_sub_succ {k : ℕ} (p : Fin k → ℝ) (i : Fin k) :
    residualMass p i.val - residualMass p (i.val + 1) = p i := by
  classical
  unfold residualMass
  rw [← Finset.sum_sub_distrib]
  have hterm (j : Fin k) :
      (if i.val ≤ j.val then p j else 0) -
        (if i.val + 1 ≤ j.val then p j else 0) = if j = i then p i else 0 := by
    by_cases hji : j = i
    · subst j
      simp
    · have hne : j.val ≠ i.val := by exact fun h => hji (Fin.ext h)
      by_cases hle : i.val ≤ j.val
      · have hlt : i.val + 1 ≤ j.val := by omega
        simp [hle, hlt, hji]
      · have hlt : ¬ i.val + 1 ≤ j.val := by omega
        simp [hle, hlt, hji]
  simp_rw [hterm]
  simp

noncomputable def entropyArea (s : ℝ) : ℝ := s - s * Real.log s

lemma entropyArea_step {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    -(s - t) * Real.log s ≤ entropyArea s - entropyArea t := by
  by_cases ht0 : t = 0
  · simp only [ht0, entropyArea, mul_zero, zero_mul, sub_zero]
    linarith
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hs htpos)) ht
    rw [Real.log_div hs.ne' htpos.ne'] at h
    have he : t * (s / t - 1) = s - t := by field_simp [htpos.ne']; ring
    rw [he] at h
    unfold entropyArea
    nlinarith

lemma sum_fin_differences (f : ℕ → ℝ) (k : ℕ) :
    (∑ i : Fin k, (f i.val - f (i.val + 1))) = f 0 - f k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    ring

/-- The residual logarithmic Riemann sum is bounded by its exact integral. -/
theorem residual_entropy_riemann_bound {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) :
    ∑ i, p i * (-Real.log (residualMass p i.val)) ≤ 1 := by
  have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k)))
    (fun i _ => entropyArea_step (residualMass_pos p hp i)
      (residualMass_nonneg p (fun j => (hp j).le) (i.val + 1)))
  simp_rw [residualMass_sub_succ, neg_mul, mul_neg] at h
  rw [sum_fin_differences] at h
  simpa [residualMass_zero, residualMass_length, hsum, entropyArea] using h

/-- Exact weighted covariance identity used in the ordered mass estimate. -/
lemma weighted_covariance_identity {k : ℕ} (w f g : Fin k → ℝ) :
    (∑ i, ∑ j, w i * w j * (f i - f j) * (g i - g j)) =
      2 * ((∑ i, w i * f i * g i) * (∑ i, w i) -
        (∑ i, w i * f i) * (∑ i, w i * g i)) := by
  have hterm (i j : Fin k) : w i * w j * (f i - f j) * (g i - g j) =
      (w i * f i * g i) * w j - (w i * f i) * (w j * g j) -
        (w i * g i) * (w j * f j) + w i * (w j * f j * g j) := by ring
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Oppositely ordered observables have nonpositive covariance under arbitrary
nonnegative weights. -/
theorem opposite_order_weighted_sum {k : ℕ} (w f g : Fin k → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hf : Antitone f) (hg : Monotone g) :
    (∑ i, w i * f i * g i) * (∑ i, w i) ≤
      (∑ i, w i * f i) * (∑ i, w i * g i) := by
  have h : (∑ i, ∑ j, w i * w j * (f i - f j) * (g i - g j)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    apply Finset.sum_nonpos
    intro j _
    have hfg : (f i - f j) * (g i - g j) ≤ 0 := by
      rcases le_total i j with hij | hji
      · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (hf hij))
          (sub_nonpos.mpr (hg hij))
      · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hf hji))
          (sub_nonneg.mpr (hg hji))
    have hmul := mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (hw i) (hw j)) hfg
    nlinarith
  rw [weighted_covariance_identity] at h
  linarith

/-- Lemma 3 of the mass-envelope paper for every finite positive sorted mass
vector, with residual masses defined by their actual finite sums. -/
theorem ordered_residual_entropy_bound {k : ℕ} (p : Fin k → ℝ)
    (hp : ∀ i, 0 < p i) (hsum : ∑ i, p i = 1) (horder : Antitone p) :
    ∑ i, p i ^ 2 * Real.log (1 / residualMass p i.val) ≤ ∑ i, p i ^ 2 := by
  let g : Fin k → ℝ := fun i => -Real.log (residualMass p i.val)
  have hg : Monotone g := by
    intro i j hij
    apply neg_le_neg
    exact Real.log_le_log (residualMass_pos p hp j)
      (residualMass_antitone p (fun l => (hp l).le) hij)
  have h := opposite_order_weighted_sum p p g (fun i => (hp i).le) horder hg
  rw [hsum, mul_one] at h
  have hB := residual_entropy_riemann_bound p hp hsum
  have hQ : 0 ≤ ∑ i, p i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hB hQ
  simp only [pow_two] at hmul ⊢
  simp only [one_div, Real.log_inv]
  dsimp [g] at h
  nlinarith

end GaussianMeasureBridge
