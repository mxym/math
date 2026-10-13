import APPTReview.LacunaryWeakLimit
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators NNReal Topology
open MeasureTheory Filter Set
namespace APPTReview

abbrev ScaleInterval := Set.Icc (0:ℝ≥0) 1
noncomputable def scaleLift (μ : ProbabilityMeasure ScaleInterval) : ProbabilityMeasure ℝ≥0 :=
  μ.map (fun x => x.val)

noncomputable def scaleBandEnergy (μ : ProbabilityMeasure ℝ≥0)
    (ds : List ℝ) (e : ℝ → ℝ) (t : ℝ) : ℝ :=
  2*(∑ d∈ds.toFinset,Real.sqrt (e d*(μ.prod μ).toMeasure.real (scaleBand d t)/2))

noncomputable def scaleEnergyBound (ds : List ℝ) (e : ℝ → ℝ) (B : ℝ) : ℝ :=
  Real.sqrt (∑ d∈ds.toFinset,e d)+Real.sqrt (2*B)

theorem scaleBandEnergy_mono (μ : ProbabilityMeasure ℝ≥0) (ds : List ℝ)
    (e : ℝ → ℝ) (he : ∀ d∈ds,0≤e d) : Monotone (scaleBandEnergy μ ds e) := by
  intro a b hab
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
  apply Finset.sum_le_sum
  intro d hd
  apply Real.sqrt_le_sqrt
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_left _ (he d (List.mem_toFinset.mp hd))
  exact measureReal_mono (fun _ h => h.trans hab)

/-- One strip-width threshold works for EVERY probability measure on [0,1].
The compactness and common-measure passage are fully proved, not hypotheses.
The finite list and energy allocation are fixed before the width tends to zero. -/
theorem lacunary_uniform_band_energy (ds : List ℝ) (hds : LacunaryScales ds)
    (e : ℝ → ℝ) (B : ℝ) (hB : 0≤B)
    (he : ∀ d∈ds,0≤e d) (heB : ∀ d∈ds,e d≤B)
    (ε : ℝ) (hε : 0<ε) :
    ∃ η : ℝ, 0<η ∧ ∀ μ : ProbabilityMeasure ScaleInterval,
      scaleBandEnergy (scaleLift μ) ds e η ≤ scaleEnergyBound ds e B+ε := by
  classical
  by_contra hbad
  push_neg at hbad
  let ts : ℕ → ℝ := fun n => 1/((n:ℝ)+1)
  have hts (n : ℕ) : 0<ts n := by dsimp [ts]; positivity
  choose μ hμ using (fun n : ℕ => hbad (ts n) (hts n))
  obtain ⟨ν,φ,hφ,hlim⟩ := CompactSpace.tendsto_subseq μ
  have hmap : Tendsto (fun n => scaleLift (μ (φ n))) atTop (𝓝 (scaleLift ν)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim continuous_subtype_val
  have htslim : Tendsto (fun n => ts (φ n)) atTop (𝓝 (0:ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hh := lacunary_moving_energy_eventually (fun n => scaleLift (μ (φ n)))
    (scaleLift ν) (fun n => ts (φ n)) hmap htslim ds hds e B hB he heB ε hε
  obtain ⟨n,hn⟩ := hh.exists
  exact (not_lt_of_ge (hμ (φ n)).le) hn

/-- The uniform bound also applies to every smaller width, not just the
particular threshold obtained by compactness. -/
theorem lacunary_uniform_all_smaller_bands (ds : List ℝ) (hds : LacunaryScales ds)
    (e : ℝ → ℝ) (B : ℝ) (hB : 0≤B)
    (he : ∀ d∈ds,0≤e d) (heB : ∀ d∈ds,e d≤B)
    (ε : ℝ) (hε : 0<ε) :
    ∃ η : ℝ, 0<η ∧ ∀ (μ : ProbabilityMeasure ScaleInterval) (t : ℝ), t≤η →
      scaleBandEnergy (scaleLift μ) ds e t ≤ scaleEnergyBound ds e B+ε := by
  obtain ⟨η,hη,hbound⟩ := lacunary_uniform_band_energy ds hds e B hB he heB ε hε
  exact ⟨η,hη,fun μ t ht => (scaleBandEnergy_mono _ ds e he ht).trans (hbound μ)⟩

end APPTReview
