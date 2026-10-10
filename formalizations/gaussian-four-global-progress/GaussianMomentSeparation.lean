import GaussianTent
import GaussianWinningPartition

/-! Uniform pair separation for actual Gaussian Bochner moments.
The general theorem allows fractional labels and unequal masses; the final
specialization is Lemma 4 of the four-cell global manuscript. -/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace GaussianFourGlobal
open GaussianMeasureBridge

lemma two_label_tent (a t z r s : ℝ) (hr0 : 0 ≤ r) (hs0 : 0 ≤ s)
    (hrs : r + s ≤ 1) (hr : 0 < r → t ≤ z) (hs : 0 < s → z ≤ t) :
    a * (r + s) ≤ r * (z - t) - s * (z - t) + tent a t z := by
  have hri : r * (z - t) = r * |z - t| := by
    by_cases hz : r = 0
    · simp [hz]
    · rw [abs_of_nonneg (sub_nonneg.mpr (hr (lt_of_le_of_ne hr0 (Ne.symm hz))))]
  have hsj : s * (t - z) = s * |z - t| := by
    by_cases hz : s = 0
    · simp [hz]
    · rw [abs_of_nonpos (sub_nonpos.mpr (hs (lt_of_le_of_ne hs0 (Ne.symm hz))))]
      ring
  have hgap : r * (z - t) - s * (z - t) = (r + s) * |z - t| := by
    nlinarith
  rw [hgap]
  by_cases h : a ≤ |z - t|
  · have hm := mul_le_mul_of_nonneg_right h (add_nonneg hr0 hs0)
    nlinarith [tent_nonneg a t z]
  · have ht : tent a t z = a - |z - t| := max_eq_left (by linarith)
    rw [ht]
    nlinarith [mul_nonneg (show 0 ≤ 1 - r - s by linarith)
      (show 0 ≤ a - |z - t| by linarith)]

lemma pair_label_sum_le_one {d k : ℕ} (F : FractionalPartition d k)
    (i j : Fin k) (hij : i ≠ j) :
    ∀ᵐ x ∂gaussian d, F.labels i x + F.labels j x ≤ 1 := by
  classical
  filter_upwards [ae_all_iff.mpr F.nonneg, F.sum_one] with x hx hsum
  have h := Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.subset_univ ({i, j} : Finset (Fin k))) (fun l _ _ => hx l)
  simpa [hij, hsum] using h

/-- A quantitative separation theorem on the actual Gaussian space. Labels i
and j lie on opposite sides of a unit-normal hyperplane. The mass correction
is explicit, so no equal-mass or stationarity hypothesis is hidden. -/
theorem fractional_pair_separation {d k : ℕ} [NeZero k]
    (F : FractionalPartition d k) (i j : Fin k) (hij : i ≠ j)
    (u : Space d) (hu : ‖u‖ = 1) (t : ℝ)
    (hi : ∀ᵐ x ∂gaussian d, 0 < F.labels i x → t ≤ ⟪u, x⟫)
    (hj : ∀ᵐ x ∂gaussian d, 0 < F.labels j x → ⟪u, x⟫ ≤ t) :
    (F.mass i + F.mass j) ^ 2 / (4 * densityCap) ≤
      ⟪u, F.moment i - F.moment j⟫ - t * (F.mass i - F.mass j) := by
  let q := F.mass i + F.mass j
  let a := q / (2 * densityCap)
  have hq : 0 ≤ q := add_nonneg (F.mass_nonneg i) (F.mass_nonneg j)
  have ha : 0 ≤ a := div_nonneg hq (le_of_lt (mul_pos (by norm_num) densityCap_pos))
  have hd : Integrable (fun x => F.labels i x * (⟪u, x⟫ - t) -
      F.labels j x * (⟪u, x⟫ - t)) (gaussian d) :=
    (F.integrable_weighted_score i u t).sub (F.integrable_weighted_score j u t)
  have heval : (∫ x, F.labels i x * (⟪u, x⟫ - t) -
      F.labels j x * (⟪u, x⟫ - t) ∂gaussian d) =
      ⟪u, F.moment i - F.moment j⟫ - t * (F.mass i - F.mass j) := by
    rw [integral_sub (F.integrable_weighted_score i u t)
      (F.integrable_weighted_score j u t), F.integral_weighted_score i u t,
      F.integral_weighted_score j u t, inner_sub_right]
    ring
  have hineq := integral_mono_ae
    (((F.integrable_label i).add (F.integrable_label j)).const_mul a)
    (hd.add (integrable_inner_tent u a t ha))
    (by
      filter_upwards [F.nonneg i, F.nonneg j, pair_label_sum_le_one F i j hij, hi, hj]
        with x hni hnj hs hwi hwj
      exact two_label_tent a t ⟪u, x⟫ (F.labels i x) (F.labels j x) hni hnj hs hwi hwj)
  simp only [Pi.add_apply, Pi.sub_apply] at hineq
  rw [integral_const_mul, integral_add (F.integrable_label i) (F.integrable_label j),
    integral_add hd (integrable_inner_tent u a t ha), heval] at hineq
  change a * q ≤ ⟪u, F.moment i - F.moment j⟫ - t * (F.mass i - F.mass j) +
    (∫ x, tent a t ⟪u, x⟫ ∂gaussian d) at hineq
  have hb := gaussian_inner_tent_bound u hu a t ha
  have halg : a * q - densityCap * a ^ 2 = q ^ 2 / (4 * densityCap) := by
    dsimp [a]
    field_simp [ne_of_gt densityCap_pos]
    ring
  change q ^ 2 / (4 * densityCap) ≤ _
  linarith

/-- In the equal-mass case the hyperplane offset cancels exactly. -/
theorem fractional_equal_mass_pair_separation {d k : ℕ} [NeZero k]
    (F : FractionalPartition d k) (i j : Fin k) (hij : i ≠ j)
    (u : Space d) (hu : ‖u‖ = 1) (t p : ℝ)
    (hmi : F.mass i = p) (hmj : F.mass j = p)
    (hi : ∀ᵐ x ∂gaussian d, 0 < F.labels i x → t ≤ ⟪u, x⟫)
    (hj : ∀ᵐ x ∂gaussian d, 0 < F.labels j x → ⟪u, x⟫ ≤ t) :
    p ^ 2 / densityCap ≤ ⟪u, F.moment i - F.moment j⟫ := by
  have h := fractional_pair_separation F i j hij u hu t hi hj
  rw [hmi, hmj, sub_self, mul_zero, sub_zero] at h
  calc
    p ^ 2 / densityCap = (p + p) ^ 2 / (4 * densityCap) := by
      field_simp [ne_of_gt densityCap_pos]
      ring
    _ ≤ _ := h

/-- The exact paper constant. It is positive and equals sqrt(2*pi)/16. -/
noncomputable def separationConstant : ℝ := 1 / (16 * densityCap)

lemma separationConstant_pos : 0 < separationConstant := by
  unfold separationConstant
  exact div_pos zero_lt_one (mul_pos (by norm_num) densityCap_pos)

lemma separationConstant_eq : separationConstant = Real.sqrt (2 * Real.pi) / 16 := by
  rw [separationConstant, densityCap_eq]
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp

/-- Uniform pair separation for balanced winning cells, using actual Bochner
moments. No local/global optimum, facet matrix, or rank assumption is present. -/
theorem balanced_winning_moment_separation {d : ℕ}
    (v : Fin 4 → Space d) (b : Fin 4 → ℝ) (hv : Function.Injective v)
    (hb : ∀ i, (gaussian d).real (winningCell v b i) = 1 / 4)
    (i j : Fin 4) (hij : i ≠ j) :
    separationConstant ≤
      ⟪‖v i - v j‖⁻¹ • (v i - v j),
        (winningPartition v b hv).moment i - (winningPartition v b hv).moment j⟫ := by
  let F := winningPartition v b hv
  let w := v i - v j
  let u := ‖w‖⁻¹ • w
  let t := (b i - b j) / ‖w‖
  have hw : w ≠ 0 := sub_ne_zero.mpr (fun h => hij (hv h))
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  have hu : ‖u‖ = 1 := by
    simp [u, norm_smul, hn]
  have hi : ∀ᵐ x ∂gaussian d, 0 < F.labels i x → t ≤ ⟪u, x⟫ := by
    apply ae_of_all
    intro x hx
    have hwin : x ∈ winningCell v b i := by
      by_contra h
      simp [F, winningPartition, h] at hx
    have hs := hwin j (Ne.symm hij)
    have hc : b i - b j ≤ ⟪v i, x⟫ - ⟪v j, x⟫ := by linarith
    dsimp [u, t, w]
    rw [real_inner_smul_left, inner_sub_left]
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr (norm_nonneg (v i - v j)))
  have hj : ∀ᵐ x ∂gaussian d, 0 < F.labels j x → ⟪u, x⟫ ≤ t := by
    apply ae_of_all
    intro x hx
    have hwin : x ∈ winningCell v b j := by
      by_contra h
      simp [F, winningPartition, h] at hx
    have hs := hwin i hij
    have hc : ⟪v i, x⟫ - ⟪v j, x⟫ ≤ b i - b j := by linarith
    dsimp [u, t, w]
    rw [real_inner_smul_left, inner_sub_left]
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr (norm_nonneg (v i - v j)))
  have hm : ∀ l, F.mass l = (1 / 4 : ℝ) := fun l => by
    rw [winningPartition_mass]
    exact hb l
  have h := fractional_equal_mass_pair_separation F i j hij u hu t (1 / 4)
    (hm i) (hm j) hi hj
  have hc : (1 / 4 : ℝ) ^ 2 / densityCap = separationConstant := by
    unfold separationConstant
    field_simp [ne_of_gt densityCap_pos]
    norm_num
  rwa [hc] at h

/-- The actual moment vectors of a balanced winning diagram are uniformly
separated in norm as well as along their inducing pair directions. -/
theorem balanced_winning_moment_norm_separation {d : ℕ}
    (v : Fin 4 → Space d) (b : Fin 4 → ℝ) (hv : Function.Injective v)
    (hb : ∀ i, (gaussian d).real (winningCell v b i) = 1 / 4)
    (i j : Fin 4) (hij : i ≠ j) :
    separationConstant ≤
      ‖(winningPartition v b hv).moment i - (winningPartition v b hv).moment j‖ := by
  have hn : ‖v i - v j‖ ≠ 0 := norm_ne_zero_iff.mpr
    (sub_ne_zero.mpr (fun h => hij (hv h)))
  have hu : ‖‖v i - v j‖⁻¹ • (v i - v j)‖ = 1 := by
    simp [norm_smul, hn]
  have h := real_inner_le_norm (‖v i - v j‖⁻¹ • (v i - v j))
    ((winningPartition v b hv).moment i - (winningPartition v b hv).moment j)
  rw [hu, one_mul] at h
  exact (balanced_winning_moment_separation v b hv hb i j hij).trans h

end GaussianFourGlobal
