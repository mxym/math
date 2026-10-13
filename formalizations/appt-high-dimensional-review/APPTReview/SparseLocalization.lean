import APPTReview.SparseScaleAlgebra

open scoped BigOperators NNReal
open MeasureTheory
namespace APPTReview
attribute [local instance] Classical.propDecidable

theorem unit_amplitude_le_one {ι : Type*} [Fintype ι] (s : ι → ℝ)
    (hs0 : ∀ i,0≤s i) (hs : (∑ i,(s i)^2)=1) (i : ι) : s i≤1 := by
  have h := Finset.single_le_sum (fun j (_ : j∈Finset.univ) => sq_nonneg (s j)) (Finset.mem_univ i)
  rw [hs] at h
  nlinarith [hs0 i]

noncomputable def unitAmplitudeProbability {ι : Type*} [Fintype ι]
    (L : ℝ) (s : ι → ℝ) (hL : 0<L) (hs0 : ∀ i,0≤s i) (hs : (∑ i,(s i)^2)=1) :
    ProbabilityMeasure ScaleInterval :=
  finiteScaleProbability (fun i => (s i)^2)
    (fun i => amplitudeScalePoint L (s i) hL (hs0 i) (unit_amplitude_le_one s hs0 hs i))
    (fun i => sq_nonneg _) hs

/-- The finite sparse-matrix localization bound, using the actual logarithmic
push-forward of its test vector. No band correspondence or small-mass estimate
is assumed: both are proved for every finite vector, including zero coordinates. -/
theorem sparse_scale_localization {ι : Type*} [Fintype ι]
    (L d η e : ℝ) (hL : 0<L) (hη : 0≤η) (he : 0≤e)
    (hcard : (Fintype.card ι:ℝ)≤Real.exp L)
    (s : ι → ℝ) (hs0 : ∀ i,0≤s i) (hs : (∑ i,(s i)^2)=1)
    (w : ι × ι → ℝ) (hw : ∀ z,0≤w z) (hw1 : ∀ z,w z≤1)
    (hwr : (∑ z,w z)≤2*sparseScaleRank L d) :
    sparseScaleCoefficient L d e*(∑ z,w z*(s z.1*s z.2)) ≤
      Real.sqrt (2*e*((scaleLift (unitAmplitudeProbability L s hL hs0 hs)).prod
        (scaleLift (unitAmplitudeProbability L s hL hs0 hs))).toMeasure.real (scaleBand d (4*η)))+
      sparseScaleError L η e := by
  let t : ι → ScaleInterval := fun i =>
    amplitudeScalePoint L (s i) hL (hs0 i) (unit_amplitude_le_one s hs0 hs i)
  let G : Finset ι := Finset.univ.filter (fun i => Real.exp (-(1+η)*L)≤(s i)^2)
  have hbad : (∑ i,if i∈G then 0 else (s i)^2)≤Real.exp (-η*L) := by
    simpa only [G,Finset.mem_filter,Finset.mem_univ,true_and] using small_amplitude_mass s L η hcard
  have hband : ∀ i j, i∈G → j∈G → Real.exp ((d/2-1-η)*L)≤s i*s j →
      s i*s j≤Real.exp ((d/2-1+η)*L) → |((t i).val:ℝ)+((t j).val:ℝ)-d|≤4*η := by
    intro i j hi hj hlo hhi
    exact amplitude_product_band L (s i) (s j) d η hL (hs0 i) (hs0 j) hη
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 hlo hhi
  have hab : Real.exp ((d/2-1-η)*L)≤Real.exp ((d/2-1+η)*L) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have h := weighted_pair_band_bound s hs0 hs t G w (sparseScaleRank L d)
    (Real.exp ((d/2-1-η)*L)) (Real.exp ((d/2-1+η)*L)) (Real.exp (-η*L)) d (4*η)
    (Real.exp_pos _).le (Real.exp_pos _).le (Real.exp_pos _) hab hw hw1 hwr hbad hband
  exact sparseScale_normalize_bound L d η e _ _ he h

end APPTReview
