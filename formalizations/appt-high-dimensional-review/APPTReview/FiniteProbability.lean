import APPTReview.LacunaryUniformBand
import Mathlib.MeasureTheory.Measure.WithDensity

open scoped BigOperators NNReal ENNReal
open MeasureTheory Set
namespace APPTReview

noncomputable def finiteAtomicMeasure {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (p : ι → ℝ) (x : ι → X) : Measure X :=
  Measure.sum (fun i => (ENNReal.ofReal (p i)) • Measure.dirac (x i))

theorem finiteAtomicMeasure_probability {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (p : ι → ℝ) (x : ι → X) (hp : ∀ i,0≤p i) (hs : (∑ i,p i)=1) :
    IsProbabilityMeasure (finiteAtomicMeasure p x) := by
  constructor
  simp only [finiteAtomicMeasure,Measure.sum_apply_of_countable,Measure.smul_apply,measure_univ,
    smul_eq_mul,mul_one,tsum_fintype]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i),hs,ENNReal.ofReal_one]

noncomputable def finiteAtomicProbability {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    (p : ι → ℝ) (x : ι → X) (hp : ∀ i,0≤p i) (hs : (∑ i,p i)=1) :
    ProbabilityMeasure X := ⟨finiteAtomicMeasure p x,finiteAtomicMeasure_probability p x hp hs⟩

/-- Repeated atom locations and zero weights are permitted. -/
theorem finiteAtomicMeasure_real {ι X : Type*} [Fintype ι] [MeasurableSpace X]
    [MeasurableSingletonClass X] (p : ι → ℝ) (x : ι → X) (hp : ∀ i,0≤p i)
    (S : Set X) [DecidablePred (fun i => x i∈S)] :
    (finiteAtomicMeasure p x).real S=∑ i,if x i∈S then p i else 0 := by
  classical
  simp only [Measure.real,finiteAtomicMeasure,Measure.sum_apply_of_countable,Measure.smul_apply,
    Measure.dirac_apply,Set.indicator_apply,Pi.one_apply,smul_eq_mul,tsum_fintype]
  rw [ENNReal.toReal_sum (fun i _ => by split_ifs <;> simp)]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : x i∈S <;> simp [hi,ENNReal.toReal_ofReal (hp i)]

/-- Exact product formula for the ordered pairs of original atoms. -/
theorem finiteAtomicMeasure_prod {ι κ X Y : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace X] [MeasurableSpace Y]
    (p : ι → ℝ) (q : κ → ℝ) (x : ι → X) (y : κ → Y)
    (hp : ∀ i,0≤p i) (hq : ∀ j,0≤q j) :
    (finiteAtomicMeasure p x).prod (finiteAtomicMeasure q y)=
      finiteAtomicMeasure (fun z : ι×κ => p z.1*q z.2) (fun z => (x z.1,y z.2)) := by
  simp only [finiteAtomicMeasure,Measure.prod_sum,Measure.prod_smul_left,
    Measure.prod_smul_right,Measure.dirac_prod_dirac,smul_smul]
  congr 1
  funext z
  rw [ENNReal.ofReal_mul (hp z.1),mul_comm]

theorem finiteAtomicMeasure_map {ι X Y : Type*} [Fintype ι]
    [MeasurableSpace X] [MeasurableSpace Y]
    (p : ι → ℝ) (x : ι → X) (f : X → Y) (hf : Measurable f) :
    Measure.map f (finiteAtomicMeasure p x)=finiteAtomicMeasure p (fun i => f (x i)) := by
  simp only [finiteAtomicMeasure,Measure.map_sum hf.aemeasurable,
    Measure.map_smul _ hf.aemeasurable,Measure.map_dirac' hf]

end APPTReview
