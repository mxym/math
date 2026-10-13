import APPTReview.MovingScaleBand

open scoped BigOperators NNReal Topology
open MeasureTheory Filter
namespace APPTReview

/-- Weak convergence plus a vanishing strip width suffices for the simultaneous
energy upper bound. The same probability sequence and limit serve every scale. -/
theorem lacunary_moving_energy_eventually (μs : ℕ → ProbabilityMeasure ℝ≥0)
    (μ : ProbabilityMeasure ℝ≥0) (ts : ℕ → ℝ)
    (hμ : Tendsto μs atTop (𝓝 μ)) (ht : Tendsto ts atTop (𝓝 0))
    (ds : List ℝ) (hds : LacunaryScales ds) (e : ℝ → ℝ) (B : ℝ)
    (hB : 0≤B) (he : ∀ d∈ds,0≤e d) (heB : ∀ d∈ds,e d≤B)
    (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ n in atTop,
      2*(∑ d∈ds.toFinset,Real.sqrt (e d*((μs n).prod (μs n)).toMeasure.real (scaleBand d (ts n))/2)) <
        Real.sqrt (∑ d∈ds.toFinset,e d)+Real.sqrt (2*B)+ε := by
  classical
  let F : ℝ → ℝ := fun t =>
    2*(∑ d∈ds.toFinset,Real.sqrt (e d*((μ.prod μ).toMeasure.real (scaleLine d)+t)/2))
  have hF : Continuous F := by dsimp [F]; fun_prop
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp (hF.continuousAt (x:=0)) ε hε
  let τ := δ/2
  have hτ : 0<τ := by dsimp [τ]; positivity
  have hdist : dist τ 0<δ := by
    rw [Real.dist_eq,sub_zero,abs_of_pos hτ]
    dsimp [τ]
    linarith
  have hFτ : F τ<F 0+ε := by
    have hh := hclose hdist
    rw [Real.dist_eq] at hh
    linarith [(abs_lt.mp hh).2]
  have h0 : F 0 ≤ Real.sqrt (∑ d∈ds.toFinset,e d)+Real.sqrt (2*B) := by
    have h := lacunary_probability_energy_doubled μ.toMeasure ds hds e B hB he heB
    convert h using 1 <;> simp only [F,add_zero,ProbabilityMeasure.toMeasure_prod,mul_div_assoc]
  have hall : ∀ᶠ n in atTop, ∀ d∈ds.toFinset,
      ((μs n).prod (μs n)).toMeasure.real (scaleBand d (ts n)) ≤
        (μ.prod μ).toMeasure.real (scaleLine d)+τ := by
    apply (Filter.eventually_all_finite ds.toFinset.finite_toSet).2
    intro d _
    exact (moving_scaleBand_eventually_lt μs μ ts hμ ht d τ hτ).mono (fun _ h => h.le)
  filter_upwards [hall] with n hn
  have hle : 2*(∑ d∈ds.toFinset,Real.sqrt (e d*((μs n).prod (μs n)).toMeasure.real (scaleBand d (ts n))/2))≤F τ := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
    apply Finset.sum_le_sum
    intro d hd
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hn d hd) (he d (List.mem_toFinset.mp hd))) (by norm_num)
  exact hle.trans_lt (by linarith [hFτ,h0])

end APPTReview
