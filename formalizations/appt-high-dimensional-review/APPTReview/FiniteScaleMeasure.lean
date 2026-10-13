import APPTReview.LacunaryUniformBand
import Mathlib.MeasureTheory.Measure.Prod

open scoped BigOperators NNReal ENNReal
open MeasureTheory Set
namespace APPTReview
attribute [local instance] Classical.propDecidable

/-- The actual finite amplitude distribution; repeated locations are allowed. -/
noncomputable def finiteScaleMeasure {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (p : ι → ℝ) (t : ι → X) : Measure X :=
  Measure.sum (fun i => ENNReal.ofReal (p i) • Measure.dirac (t i))

theorem finiteScaleMeasure_apply {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (p : ι → ℝ) (t : ι → X) (A : Set X) (hA : MeasurableSet A) :
    finiteScaleMeasure p t A = ∑ i, if t i∈A then ENNReal.ofReal (p i) else 0 := by
  classical
  simp only [finiteScaleMeasure,Measure.sum_apply _ hA,tsum_fintype,
    Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' _ hA]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Set.indicator_apply,Pi.one_apply]
  split_ifs <;> simp

theorem finiteScaleMeasure_probability {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (p : ι → ℝ) (t : ι → X) (hp : ∀ i,0≤p i) (hs : (∑ i,p i)=1) :
    IsProbabilityMeasure (finiteScaleMeasure p t) := by
  constructor
  rw [finiteScaleMeasure_apply p t Set.univ MeasurableSet.univ]
  simp only [Set.mem_univ,ite_true]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i),hs,ENNReal.ofReal_one]

theorem finiteScaleMeasure_real {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (p : ι → ℝ) (t : ι → X) (hp : ∀ i,0≤p i)
    (A : Set X) (hA : MeasurableSet A) :
    (finiteScaleMeasure p t).real A = ∑ i, if t i∈A then p i else 0 := by
  classical
  unfold Measure.real
  rw [finiteScaleMeasure_apply p t A hA]
  rw [ENNReal.toReal_sum (fun i _ => by split_ifs <;> simp)]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [ENNReal.toReal_ofReal,hp i]

end APPTReview

namespace APPTReview
attribute [local instance] Classical.propDecidable

/-- Products of the actual finite measures preserve all cross terms. -/
theorem finiteScaleMeasure_prod {ι κ X Y : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace X] [MeasurableSpace Y]
    (p : ι → ℝ) (q : κ → ℝ) (t : ι → X) (u : κ → Y)
    (hp : ∀ i,0≤p i) :
    (finiteScaleMeasure p t).prod (finiteScaleMeasure q u)=
      finiteScaleMeasure (fun z : ι × κ => p z.1*q z.2) (fun z => (t z.1,u z.2)) := by
  unfold finiteScaleMeasure
  rw [Measure.prod_sum]
  congr 1
  funext z
  rw [Measure.prod_smul_left,Measure.prod_smul_right,Measure.dirac_prod_dirac,smul_smul,
    ← ENNReal.ofReal_mul (hp z.1)]

/-- Mapping an atomic measure never requires the locations to be distinct. -/
theorem finiteScaleMeasure_map {ι X Y : Type*} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace Y]
    (p : ι → ℝ) (t : ι → X) (f : X → Y) (hf : Measurable f) :
    (finiteScaleMeasure p t).map f=finiteScaleMeasure p (fun i => f (t i)) := by
  unfold finiteScaleMeasure
  rw [Measure.map_sum hf.aemeasurable]
  congr 1
  funext i
  rw [Measure.map_smul,Measure.map_dirac' hf]
  exact hf.aemeasurable

noncomputable def finiteScaleProbability {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (t : ι → ScaleInterval) (hp : ∀ i,0≤p i) (hs : (∑ i,p i)=1) :
    ProbabilityMeasure ScaleInterval := ⟨finiteScaleMeasure p t,finiteScaleMeasure_probability p t hp hs⟩

/-- The probability appearing in the compactness theorem is the push-forward
of these same finite amplitudes, not a separately optimized level measure. -/
theorem finiteScaleProbability_band {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (t : ι → ScaleInterval) (hp : ∀ i,0≤p i) (hs : (∑ i,p i)=1)
    (d η : ℝ) :
    ((scaleLift (finiteScaleProbability p t hp hs)).prod
      (scaleLift (finiteScaleProbability p t hp hs))).toMeasure.real (scaleBand d η) =
      ∑ z : ι × ι, if |((t z.1).val:ℝ)+((t z.2).val:ℝ)-d|≤η then p z.1*p z.2 else 0 := by
  have hF : MeasurableSet (scaleBand d η) :=
    (isClosed_le (by fun_prop) continuous_const).measurableSet
  change (((finiteScaleMeasure p t).map Subtype.val).prod
    ((finiteScaleMeasure p t).map Subtype.val)).real (scaleBand d η)=_
  rw [finiteScaleMeasure_map p t Subtype.val measurable_subtype_coe,
    finiteScaleMeasure_prod p p _ _ hp]
  exact finiteScaleMeasure_real (fun z : ι × ι => p z.1*p z.2)
    (fun z => ((t z.1).val,(t z.2).val))
    (fun z => mul_nonneg (hp z.1) (hp z.2)) _ hF

end APPTReview
