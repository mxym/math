import GaussianFour.PriceBounds
import Mathlib.Topology.Sequences

/-! Uniform boundedness and sequential compactness of actual centered prices. -/
open MeasureTheory ProbabilityTheory Set Filter Metric
open scoped RealInnerProductSpace Topology
open GaussianMeasureBridge
namespace GaussianFour
variable {d : ℕ}

theorem centered_balanced_four_price_coordinate_bound
    (v : Fin 4 → Space d) (b : Fin 4 → ℝ)
    (hmass : ∀ i, (gaussian d).real (winningCell v b i) = 1 / 4)
    (hcenter : ∑ i, b i = 0) (D : ℝ)
    (hdiam : ∀ i j, ‖v i - v j‖ ≤ D) (i : Fin 4) :
    |b i| ≤ quarterQuantile * D := by
  have hp : ∀ i j, b i - b j ≤ quarterQuantile * D := by
    intro i j
    exact (le_abs_self _).trans ((balanced_four_price_difference_bound v b hmass i j).trans
      (mul_le_mul_of_nonneg_left (hdiam i j) quarterQuantile_pos.le))
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j)
  have hl := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp j i)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat, hcenter] at hu hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem centered_balanced_four_price_norm_bound
    (v : Fin 4 → Space d) (b : Fin 4 → ℝ)
    (hmass : ∀ i, (gaussian d).real (winningCell v b i) = 1 / 4)
    (hcenter : ∑ i, b i = 0) (D : ℝ) (hD : 0 ≤ D)
    (hdiam : ∀ i j, ‖v i - v j‖ ≤ D) :
    ‖b‖ ≤ quarterQuantile * D := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg quarterQuantile_pos.le hD)).mpr
  intro i
  simpa only [Real.norm_eq_abs] using
    centered_balanced_four_price_coordinate_bound v b hmass hcenter D hdiam i

/-- Compactness also applies to rank-deficient score families. -/
theorem centered_balanced_four_prices_tendsto_subseq
    (v : ℕ → Fin 4 → Space d) (b : ℕ → Fin 4 → ℝ)
    (hmass : ∀ n i, (gaussian d).real (winningCell (v n) (b n) i) = 1 / 4)
    (hcenter : ∀ n, ∑ i, b n i = 0) (D : ℝ) (hD : 0 ≤ D)
    (hdiam : ∀ n i j, ‖v n i - v n j‖ ≤ D) :
    ∃ b₀ : Fin 4 → ℝ, (∑ i, b₀ i = 0) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (b ∘ φ) atTop (𝓝 b₀) := by
  have hb : ∀ n, b n ∈ closedBall (0 : Fin 4 → ℝ) (quarterQuantile * D) := by
    intro n
    rw [mem_closedBall, dist_zero_right]
    exact centered_balanced_four_price_norm_bound (v n) (b n) (hmass n)
      (hcenter n) D hD (hdiam n)
  obtain ⟨b₀, _, φ, hφ, hlim⟩ :=
    (isCompact_closedBall (0 : Fin 4 → ℝ) (quarterQuantile * D)).tendsto_subseq hb
  refine ⟨b₀, ?_, φ, hφ, hlim⟩
  have hcont : Continuous (fun c : Fin 4 → ℝ => ∑ i, c i) := by fun_prop
  have hs := hcont.continuousAt.tendsto.comp hlim
  have hz : Tendsto (fun n => ∑ i, (b ∘ φ) n i) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, hcenter] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique hs hz

end GaussianFour
