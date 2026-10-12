import BapatHaarLowerBound

set_option autoImplicit false
open MeasureTheory Set Filter
open scoped Topology

namespace BapatRealExistence
noncomputable section

theorem unitRows_positive_factors {n : ℕ} (v : Fin n → RealUnitSphere4) (z : ComplexUnitSphere4)
    (hp : 0 < rowProductModulus (unitCoefficientRows v) z) (i : Fin n) :
    realComplexLinear (v i) z ≠ 0 := by
  rw [unitCoefficientRows_product_norm] at hp
  exact norm_ne_zero_iff.mp ((Finset.prod_ne_zero_iff.mp hp.ne') i (Finset.mem_univ i))

theorem unitRows_log_truncation_upper {n : ℕ} (v : Fin n → RealUnitSphere4) (z : ComplexUnitSphere4)
    (hp : 0 < rowProductModulus (unitCoefficientRows v) z) (K : ℝ) :
    Real.log (rowProductModulus (unitCoefficientRows v) z) ≤ ∑ i, truncatedLogLinear K (v i) z := by
  have hn (i : Fin n) := unitRows_positive_factors v z hp i
  rw [unitCoefficientRows_product_norm,Real.log_prod (fun i _ => norm_ne_zero_iff.mpr (hn i))]
  exact Finset.sum_le_sum (fun i _ => log_le_truncatedLogLinear K (v i) z (hn i))

def cloudRows (u : ℕ → RealUnitSphere4) (n : ℕ) : Fin n → Fin 4 → ℝ :=
  unitCoefficientRows (fun i : Fin n => u i.val)

theorem cloud_maximum_truncated_lower (u : ℕ → RealUnitSphere4) (n : ℕ) (hn : 0<n)
    (z : ComplexUnitSphere4)
    (hmax : ∀ w, rowProductModulus (cloudRows u n) w ≤ rowProductModulus (cloudRows u n) z)
    (K : ℝ) :
    sphereCanonicalPotential (1/2) ≤ empiricalAverage u n (fun v => truncatedLogLinear K v z) := by
  let v : Fin n → RealUnitSphere4 := fun i => u i.val
  obtain ⟨w,hw⟩ := unitRows_exists_positive v
  have hp := hw.trans_le (hmax w)
  have hlo := unitRows_maximum_log_lower v z hmax
  have hhi := unitRows_log_truncation_upper v z hp K
  have hsum : (n:ℝ)*sphereCanonicalPotential (1/2) ≤ ∑ i ∈ Finset.range n, truncatedLogLinear K (u i) z := by
    have hh := hlo.trans hhi
    change (n:ℝ)*sphereCanonicalPotential (1/2) ≤ ∑ i : Fin n, truncatedLogLinear K (u i.val) z at hh
    rw [Fin.sum_univ_eq_sum_range (fun i => truncatedLogLinear K (u i) z) n] at hh
    exact hh
  unfold empiricalAverage
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ (Nat.cast_pos.mpr hn)).mpr (by simpa only [mul_comm] using hsum)

/-- Every cluster point of actual product maximizers is balanced. -/
theorem cloud_maximizer_cluster_balanced (u : ℕ → RealUnitSphere4)
    (hu : ∀ f : C(RealUnitSphere4,ℝ), Tendsto (fun n => empiricalAverage u n f) atTop
      (𝓝 (∫ x, f x ∂normalizedSphere (volume : Measure RealSpace4))))
    (z : ℕ → ComplexUnitSphere4)
    (hmax : ∀ n w, rowProductModulus (cloudRows u n) w ≤ rowProductModulus (cloudRows u n) (z n))
    (a : ℕ → ℕ) (ha : Tendsto a atTop atTop) (z₀ : ComplexUnitSphere4)
    (hz : Tendsto (z ∘ a) atTop (𝓝 z₀)) : balanceParameter z₀ = 1/2 := by
  have hbound (K : ℕ) : sphereCanonicalPotential (1/2) ≤
      ∫ v, truncatedLogLinear K v z₀ ∂normalizedSphere (volume : Measure RealSpace4) := by
    have hlim := truncatedPotential_empirical_moving u hu a ha (z ∘ a) z₀ hz K
    apply ge_of_tendsto hlim
    filter_upwards [ha.eventually (eventually_gt_atTop 0)] with n hn
    exact cloud_maximum_truncated_lower u (a n) hn (z (a n)) (hmax (a n)) K
  have hpot : sphereCanonicalPotential (1/2) ≤ sphereLogPotential z₀ :=
    ge_of_tendsto' (truncatedPotential_integral_tendsto z₀) hbound
  exact (sphereLogPotential_unique_balanced z₀).2.mp
    (le_antisymm (sphereLogPotential_unique_balanced z₀).1 hpot)

/-- Lemma 2 of the real-symmetric construction: every choice of global maximizers
of an actual equidistributed real cloud becomes balanced. -/
theorem cloud_maximizers_balance_tendsto (u : ℕ → RealUnitSphere4)
    (hu : ∀ f : C(RealUnitSphere4,ℝ), Tendsto (fun n => empiricalAverage u n f) atTop
      (𝓝 (∫ x, f x ∂normalizedSphere (volume : Measure RealSpace4))))
    (z : ℕ → ComplexUnitSphere4)
    (hmax : ∀ n w, rowProductModulus (cloudRows u n) w ≤ rowProductModulus (cloudRows u n) (z n)) :
    Tendsto (fun n => balanceParameter (z n)) atTop (𝓝 (1/2:ℝ)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨z₀,ms,hms,hz⟩ := CompactSpace.tendsto_subseq (z ∘ ns)
  refine ⟨ms,?_⟩
  have hb := cloud_maximizer_cluster_balanced u hu z hmax (ns ∘ ms)
    (hns.comp hms.tendsto_atTop) z₀ hz
  have hcont : Continuous (fun z : ComplexUnitSphere4 => balanceParameter z) := by fun_prop
  have h := (hcont.tendsto z₀).comp hz
  simpa only [Function.comp_def,hb] using h

/-- Existence is discharged using the strong-law cloud and true compact maxima. -/
theorem exists_cloud_with_balanced_maximizers :
    ∃ (u : ℕ → RealUnitSphere4) (z : ℕ → ComplexUnitSphere4),
      (∀ f : C(RealUnitSphere4,ℝ), Tendsto (fun n => empiricalAverage u n f) atTop
        (𝓝 (∫ x, f x ∂normalizedSphere (volume : Measure RealSpace4)))) ∧
      (∀ n, 0 < rowProductModulus (cloudRows u n) (z n)) ∧
      (∀ n w, rowProductModulus (cloudRows u n) w ≤ rowProductModulus (cloudRows u n) (z n)) ∧
      Tendsto (fun n => balanceParameter (z n)) atTop (𝓝 (1/2:ℝ)) := by
  obtain ⟨u,hu⟩ := exists_real_sphere_cloud
  have hm (n : ℕ) := unitRows_exists_positive_maximum (fun i : Fin n => u i.val)
  choose z hp hmax using hm
  exact ⟨u,z,hu,hp,hmax,cloud_maximizers_balance_tendsto u hu z hmax⟩

end
end BapatRealExistence
