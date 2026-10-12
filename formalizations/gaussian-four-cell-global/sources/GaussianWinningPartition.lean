import GaussianBalancedPrices

/-! Winning cells are actual measurable fractional partitions, and exactly
attain their own-mass Gaussian price dual. -/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge

variable {d k : ℕ} [NeZero k]

noncomputable def winningPartition (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) : FractionalPartition d k where
  labels i := (winningCell v b i).indicator (fun _ => 1)
  measurable_labels i := measurable_const.indicator (measurableSet_winningCell v b i)
  nonneg i := ae_of_all _ fun x => by
    by_cases h : x ∈ winningCell v b i <;> simp [h]
  le_one i := ae_of_all _ fun x => by
    by_cases h : x ∈ winningCell v b i <;> simp [h]
  sum_one := by
    classical
    filter_upwards [ae_unique_winner v b hv] with x hx
    obtain ⟨r, hr⟩ := hx
    have hnot : ∀ j, j ≠ r → x ∉ winningCell v b j := by
      intro j hj hxj
      have h1 := hr j hj
      have h2 := hxj r hj.symm
      linarith
    rw [Finset.sum_eq_single r]
    · simp [hr]
    · intro j _ hj
      simp [hnot j hj]
    · simp

theorem winningPartition_mass (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) (i : Fin k) :
    (winningPartition v b hv).mass i = (gaussian d).real (winningCell v b i) := by
  simpa only [winningPartition, FractionalPartition.mass, smul_eq_mul, mul_one] using
    integral_indicator_const (1 : ℝ) (measurableSet_winningCell v b i)

theorem winningPartition_dual_attainment (v : Fin k → Space d) (b : Fin k → ℝ)
    (hv : Function.Injective v) :
    (∑ i, ⟪v i, (winningPartition v b hv).moment i⟫) =
      expectedScore v b + ∑ i, (winningPartition v b hv).mass i * b i := by
  classical
  let F := winningPartition v b hv
  have heq : (fun x => ∑ i, F.labels i x * (⟪v i, x⟫ - b i)) =ᵐ[gaussian d]
      scoreMax v b := by
    filter_upwards [ae_unique_winner v b hv] with x hx
    obtain ⟨r, hr⟩ := hx
    have hnot : ∀ j, j ≠ r → x ∉ winningCell v b j := by
      intro j hj hxj
      have h1 := hr j hj
      have h2 := hxj r hj.symm
      linarith
    rw [Finset.sum_eq_single r]
    · simp only [F, winningPartition, Set.indicator_of_mem hr, one_mul]
      exact (scoreMax_eq_winning_score v b x r hr).symm
    · intro j _ hj
      simp [F, winningPartition, hnot j hj]
    · simp
  have hi := integral_congr_ae heq
  rw [integral_finsetSum Finset.univ
    (fun i _ => F.integrable_weighted_score i (v i) (b i))] at hi
  simp_rw [F.integral_weighted_score] at hi
  rw [Finset.sum_sub_distrib] at hi
  change (∑ i, ⟪v i, F.moment i⟫) = expectedScore v b + ∑ i, F.mass i * b i
  change (∑ i, ⟪v i, F.moment i⟫) - (∑ i, F.mass i * b i) = expectedScore v b at hi
  linarith

theorem balanced_price_is_minimizer (v : Fin k → Space d) (p b : Fin k → ℝ)
    (hv : Function.Injective v)
    (hb : ∀ i, (gaussian d).real (winningCell v b i) = p i) :
    ∀ c, priceObjective v p b ≤ priceObjective v p c := by
  intro c
  have hd := (winningPartition v b hv).price_dual v c
  rw [winningPartition_dual_attainment] at hd
  simp_rw [winningPartition_mass, hb] at hd
  exact hd

end GaussianMeasureBridge
