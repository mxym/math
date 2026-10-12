import BapatMovingCloud

set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped Topology

namespace BapatRealExistence
noncomputable section
variable {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K]
  [MeasurableSpace K] [BorelSpace K]

/-- Moving continuous tests for a triangular, rather than nested, cloud. -/
theorem triangular_empirical_moving_test (μ : Measure K) [IsProbabilityMeasure μ]
    (w : ℕ → ℕ → K)
    (hw : ∀ f : C(K,ℝ), Tendsto (fun n => empiricalAverage (w n) n f) atTop (𝓝 (∫ x, f x ∂μ)))
    (a : ℕ → ℕ) (ha : Tendsto a atTop atTop)
    (f : ℕ → C(K,ℝ)) (g : C(K,ℝ)) (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => empiricalAverage (w (a n)) (a n) (f n)) atTop (𝓝 (∫ x, g x ∂μ)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have h₁ := tendsto_iff_dist_tendsto_zero.mp hf
  have h₂ := tendsto_iff_dist_tendsto_zero.mp ((hw g).comp ha)
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun n => (dist_triangle _ (empiricalAverage (w (a n)) (a n) g) _).trans
      (add_le_add (empiricalAverage_dist_le (w (a n)) (a n) (f n) g) (le_refl _)))
  simpa using h₁.add h₂

theorem empiricalAverage_continuous (u : ℕ → K) (n : ℕ) :
    Continuous (fun f : C(K,ℝ) => empiricalAverage u n f) := by
  apply LipschitzWith.continuous (K := 1)
  exact LipschitzWith.of_dist_le_mul (by simpa using empiricalAverage_dist_le u n)

theorem continuous_integral_continuousMap (μ : Measure K) [IsProbabilityMeasure μ] :
    Continuous (fun f : C(K,ℝ) => ∫ x, f x ∂μ) := by
  apply LipschitzWith.continuous (K := 1)
  exact LipschitzWith.of_dist_le_mul (by simpa using integral_continuous_dist_le μ)

variable {T : Type*} [MetricSpace T] [CompactSpace T] [Nonempty T]

/-- Equidistribution is uniform over a compact continuous family of tests. -/
theorem triangular_empirical_family (μ : Measure K) [IsProbabilityMeasure μ]
    (w : ℕ → ℕ → K)
    (hw : ∀ f : C(K,ℝ), Tendsto (fun n => empiricalAverage (w n) n f) atTop (𝓝 (∫ x, f x ∂μ)))
    (F : T → C(K,ℝ)) (hF : Continuous F) :
    Tendsto (fun n => (⟨fun t => empiricalAverage (w n) n (F t),
      (empiricalAverage_continuous (w n) n).comp hF⟩ : C(T,ℝ))) atTop
      (𝓝 (⟨fun t => ∫ x, F t x ∂μ,(continuous_integral_continuousMap μ).comp hF⟩ : C(T,ℝ))) := by
  let f (n : ℕ) : C(T,ℝ) := ⟨fun t => empiricalAverage (w n) n (F t),
    (empiricalAverage_continuous (w n) n).comp hF⟩
  let g : C(T,ℝ) := ⟨fun t => ∫ x, F t x ∂μ,(continuous_integral_continuousMap μ).comp hF⟩
  have hm (n : ℕ) : ∃ t : T, ∀ s : T, dist (f n s) (g s) ≤ dist (f n t) (g t) := by
    obtain ⟨t,_,ht⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty
      (((f n).continuous.dist g.continuous).continuousOn)
    exact ⟨t,fun s => ht (mem_univ s)⟩
  choose t ht using hm
  have hd (n : ℕ) : dist (f n) g = dist (f n (t n)) (g (t n)) := by
    apply le_antisymm
    · exact (ContinuousMap.dist_le dist_nonneg).mpr (ht n)
    · exact ContinuousMap.dist_apply_le_dist (t n)
  change Tendsto f atTop (𝓝 g)
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨t₀,ms,hms,hlim⟩ := CompactSpace.tendsto_subseq (t ∘ ns)
  refine ⟨ms,?_⟩
  have hf := triangular_empirical_moving_test μ w hw (ns ∘ ms)
    (hns.comp hms.tendsto_atTop) (F ∘ t ∘ ns ∘ ms) (F t₀) ((hF.tendsto t₀).comp hlim)
  have hg := (g.continuous.tendsto t₀).comp hlim
  have h := hf.dist hg
  simpa [Function.comp_def,hd,f,g] using h

/-- Pair averages of every continuous test converge, without an independence
assumption on the deterministic cloud. -/
theorem triangular_empirical_pairs (μ : Measure K) [IsProbabilityMeasure μ]
    (w : ℕ → ℕ → K)
    (hw : ∀ f : C(K,ℝ), Tendsto (fun n => empiricalAverage (w n) n f) atTop (𝓝 (∫ x, f x ∂μ)))
    (φ : C(K × K,ℝ)) :
    Tendsto (fun n => empiricalAverage (w n) n (fun x => empiricalAverage (w n) n (fun y => φ (x,y))))
      atTop (𝓝 (∫ x, ∫ y, φ (x,y) ∂μ ∂μ)) := by
  let F : K → C(K,ℝ) := fun x => ⟨fun y => φ (x,y),
    φ.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact φ.continuous
  have h := triangular_empirical_family μ w hw F hF
  exact triangular_empirical_moving_test μ w hw id tendsto_id _ _ h


def pairEmpiricalMap (u : ℕ → K) (n : ℕ) (φ : C(K × K,ℝ)) : C(K,ℝ) :=
  ⟨fun x => empiricalAverage u n (fun y => φ (x,y)), by
    let F : K → C(K,ℝ) := fun x => ⟨fun y => φ (x,y),
      φ.continuous.comp (continuous_const.prodMk continuous_id)⟩
    have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F φ.continuous
    exact (empiricalAverage_continuous u n).comp hF⟩

theorem pairEmpiricalMap_dist_le (u : ℕ → K) (n : ℕ) (φ ψ : C(K × K,ℝ)) :
    dist (pairEmpiricalMap u n φ) (pairEmpiricalMap u n ψ) ≤ dist φ ψ := by
  apply (ContinuousMap.dist_le dist_nonneg).mpr
  intro x
  let f : C(K,ℝ) := ⟨fun y => φ (x,y),φ.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let g : C(K,ℝ) := ⟨fun y => ψ (x,y),ψ.continuous.comp (continuous_const.prodMk continuous_id)⟩
  exact (empiricalAverage_dist_le u n f g).trans
    ((ContinuousMap.dist_le dist_nonneg).mpr (fun y => ContinuousMap.dist_apply_le_dist (x,y)))

theorem pair_empirical_dist_le (u : ℕ → K) (n : ℕ) (φ ψ : C(K × K,ℝ)) :
    dist (empiricalAverage u n (pairEmpiricalMap u n φ))
      (empiricalAverage u n (pairEmpiricalMap u n ψ)) ≤ dist φ ψ :=
  (empiricalAverage_dist_le u n _ _).trans (pairEmpiricalMap_dist_le u n φ ψ)

/-- A continuously moving parameter is allowed in the pair test. -/
theorem triangular_empirical_pairs_moving {S : Type*} [MetricSpace S]
    (μ : Measure K) [IsProbabilityMeasure μ] (w : ℕ → ℕ → K)
    (hw : ∀ f : C(K,ℝ), Tendsto (fun n => empiricalAverage (w n) n f) atTop (𝓝 (∫ x, f x ∂μ)))
    (φ : (K × K) × S → ℝ) (hφ : Continuous φ)
    (t : ℕ → S) (t₀ : S) (ht : Tendsto t atTop (𝓝 t₀)) :
    Tendsto (fun n => empiricalAverage (w n) n
      (fun x => empiricalAverage (w n) n (fun y => φ ((x,y),t n)))) atTop
      (𝓝 (∫ x, ∫ y, φ ((x,y),t₀) ∂μ ∂μ)) := by
  let F : S → C(K × K,ℝ) := fun s => ⟨fun p => φ (p,s),
    hφ.comp (continuous_id.prodMk continuous_const)⟩
  have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F
    (hφ.comp continuous_swap)
  have h₁ := tendsto_iff_dist_tendsto_zero.mp ((hF.tendsto t₀).comp ht)
  have h₂ := tendsto_iff_dist_tendsto_zero.mp (triangular_empirical_pairs μ w hw (F t₀))
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun n => (dist_triangle _ (empiricalAverage (w n) n (pairEmpiricalMap (w n) n (F t₀))) _).trans
      (add_le_add (pair_empirical_dist_le (w n) n (F (t n)) (F t₀)) (le_refl _)))
  simpa [pairEmpiricalMap,F] using h₁.add h₂

end
end BapatRealExistence
