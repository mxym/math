import Spectrum.Tensor
import Mathlib.Probability.CentralLimitTheorem
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ENNReal Topology Classical

namespace ExtractionSpectrum

noncomputable section

variable {ι : Type*} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- The actual normalized finite eigenvalue law, with no deletion of zeros. -/
def finitePMF (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : PMF ι :=
  PMF.ofFintype (fun i => ENNReal.ofReal (p i)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i), hs]
    exact ENNReal.ofReal_one)

def finiteMeasure (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) : Measure ι :=
  (finitePMF p hp hs).toMeasure

instance finiteMeasure_isProbabilityMeasure (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) : IsProbabilityMeasure (finiteMeasure p hp hs) := by
  unfold finiteMeasure
  infer_instance

theorem finiteMeasure_singleton (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (i : ι) :
    finiteMeasure p hp hs {i} = ENNReal.ofReal (p i) := by
  exact PMF.toMeasure_apply_singleton _ i (measurableSet_singleton i)

def finiteMean (p f : ι → ℝ) : ℝ := ∑ i, p i * f i

def finiteVariance (p f : ι → ℝ) : ℝ :=
  ∑ i, p i * (f i - finiteMean p f) ^ 2

theorem finiteMeasure_integral (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (f : ι → ℝ) :
    ∫ i, f i ∂finiteMeasure p hp hs = finiteMean p f := by
  rw [integral_fintype Integrable.of_finite]
  simp only [Measure.real, finiteMeasure_singleton, ENNReal.toReal_ofReal (hp _),
    smul_eq_mul, finiteMean]

theorem finiteMeasure_real_event (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (s : Set ι) :
    (finiteMeasure p hp hs).real s = ∑ i, if i ∈ s then p i else 0 := by
  classical
  rw [← integral_indicator_one (Set.toFinite s).measurableSet,
    finiteMeasure_integral]
  unfold finiteMean
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i ∈ s <;> simp [Set.indicator, h]

theorem finiteMeasure_pi (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (n : ℕ) :
    Measure.pi (fun _ : Fin n => finiteMeasure p hp hs) =
      finiteMeasure (iidLaw p n) (iidLaw_nonneg p hp n) (iidLaw_sum p hs n) := by
  apply Measure.ext_of_singleton
  intro w
  rw [Measure.pi_singleton, finiteMeasure_singleton]
  simp only [finiteMeasure_singleton]
  exact (ENNReal.ofReal_prod_of_nonneg (fun j _ => hp (w j))).symm

theorem finiteMeasure_variance (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (f : ι → ℝ) :
    Var[f; finiteMeasure p hp hs] = finiteVariance p f := by
  rw [variance_eq_integral (measurable_of_countable f).aemeasurable,
    finiteMeasure_integral, finiteMeasure_integral]
  rfl

def iidMeasure (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    Measure (ℕ → ι) := Measure.infinitePi fun _ : ℕ => finiteMeasure p hp hs

instance iidMeasure_isProbabilityMeasure (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) : IsProbabilityMeasure (iidMeasure p hp hs) := by
  unfold iidMeasure
  infer_instance

/-- The canonical iid coordinate process has the specified finite one-copy law. -/
theorem iid_coordinate_identDistrib (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (f : ι → ℝ) (j : ℕ) :
    IdentDistrib (fun w : ℕ → ι => f (w j)) f (iidMeasure p hp hs)
      (finiteMeasure p hp hs) := by
  have h := (measurePreserving_eval_infinitePi (fun _ : ℕ => finiteMeasure p hp hs) j).hasLaw
  have hId : HasLaw (id : ι → ι) (finiteMeasure p hp hs) (finiteMeasure p hp hs) :=
    ⟨measurable_id.aemeasurable, Measure.map_id⟩
  exact (h.identDistrib hId).comp (measurable_of_countable f)

theorem iid_window_hasLaw (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (n : ℕ) :
    HasLaw (fun w : ℕ → ι => fun j : Fin n => w j)
      (Measure.pi fun _ : Fin n => finiteMeasure p hp hs) (iidMeasure p hp hs) := by
  have hi : iIndepFun (fun j : ℕ => Function.eval j) (iidMeasure p hp hs) :=
    iIndepFun_infinitePi fun _ => measurable_id
  have hif : iIndepFun (fun j : Fin n => Function.eval (j : ℕ)) (iidMeasure p hp hs) :=
    hi.precomp Fin.val_injective
  exact hif.hasLaw_pi fun j =>
    (measurePreserving_eval_infinitePi (fun _ : ℕ => finiteMeasure p hp hs) (j : ℕ)).hasLaw

/-- Exact identity between the finite iid probability appearing in the quantum
converse and the canonical independent process used by the limit theorems. -/
theorem iidInformationEvent_eq_measure (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (n : ℕ) (x : ℝ) :
    iidInformationEvent p n x = (iidMeasure p hp hs).real
      {w | (∑ j ∈ Finset.range n, -Real.log (p (w j))) ≤ x} := by
  classical
  have h := (iid_window_hasLaw p hp hs n).measureReal_eq
    (p := fun w : Fin n → ι => (∑ j, -Real.log (p (w j))) ≤ x)
    (Set.toFinite _).measurableSet
  rw [finiteMeasure_pi, finiteMeasure_real_event] at h
  change (iidMeasure p hp hs).real
    {w | (∑ j : Fin n, -Real.log (p (w j))) ≤ x} = iidInformationEvent p n x at h
  have hset : {w : ℕ → ι | (∑ j : Fin n, -Real.log (p (w j))) ≤ x} =
      {w | (∑ j ∈ Finset.range n, -Real.log (p (w j))) ≤ x} := by
    apply Set.ext
    intro w
    change ((∑ j : Fin n, -Real.log (p (w j))) ≤ x) ↔ _
    rw [Fin.sum_univ_eq_sum_range (fun j => -Real.log (p (w j))) n]
    rfl
  rw [hset] at h
  exact h.symm

/-- The iid finite-law central limit theorem, with its hypotheses constructed
from the normalized finite law. The CLT is invoked as a theorem, not a premise. -/
theorem finite_iid_central_limit (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (f : ι → ℝ) :
    TendstoInDistribution
      (fun (n : ℕ) (w : ℕ → ι) => (Real.sqrt n)⁻¹ *
        ((∑ j ∈ Finset.range n, f (w j)) - n * finiteMean p f))
      atTop id (fun _ => iidMeasure p hp hs)
      (gaussianReal 0 (finiteVariance p f).toNNReal) := by
  let X : ℕ → (ℕ → ι) → ℝ := fun j w => f (w j)
  have hi : iIndepFun X (iidMeasure p hp hs) :=
    iIndepFun_infinitePi fun _ => measurable_of_countable f
  have hid : ∀ j, IdentDistrib (X j) (X 0) (iidMeasure p hp hs) (iidMeasure p hp hs) :=
    fun j => (iid_coordinate_identDistrib p hp hs f j).trans
      (iid_coordinate_identDistrib p hp hs f 0).symm
  have hmean : (iidMeasure p hp hs)[X 0] = finiteMean p f :=
    (iid_coordinate_identDistrib p hp hs f 0).integral_eq.trans (finiteMeasure_integral p hp hs f)
  have hvar : Var[X 0; iidMeasure p hp hs] = finiteVariance p f :=
    (iid_coordinate_identDistrib p hp hs f 0).variance_eq.trans (finiteMeasure_variance p hp hs f)
  have hmem : MemLp (X 0) 2 (iidMeasure p hp hs) := by
    apply (iid_coordinate_identDistrib p hp hs f 0).memLp_iff.mpr
    exact (memLp_two_iff_integrable_sq (measurable_of_countable f).aestronglyMeasurable).mpr
      Integrable.of_finite
  have hY : HasLaw (id : ℝ → ℝ)
      (gaussianReal 0 (Var[X 0; iidMeasure p hp hs]).toNNReal)
      (gaussianReal 0 (Var[X 0; iidMeasure p hp hs]).toNNReal) :=
    ⟨measurable_id.aemeasurable, Measure.map_id⟩
  have h := tendstoInDistribution_inv_sqrt_mul_sum_sub hY hmem hi hid
  rwa [hmean, hvar] at h

/-- The CDF limit is derived from the constructed CLT and Portmanteau, including
the Gaussian null-boundary check. -/
theorem finite_iid_centered_cdf (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (f : ι → ℝ) (hv : 0 < finiteVariance p f) (y : ℝ) :
    Tendsto (fun n : ℕ => (iidMeasure p hp hs).real
      {w | (Real.sqrt n)⁻¹ *
        ((∑ j ∈ Finset.range n, f (w j)) - n * finiteMean p f) ≤ y})
      atTop (𝓝 ((gaussianReal 0 (finiteVariance p f).toNNReal).real (Set.Iic y))) := by
  have h := finite_iid_central_limit p hp hs f
  haveI : NullSingletonClass (gaussianReal 0 (finiteVariance p f).toNNReal) :=
    nullSingletonClass_gaussianReal (ne_of_gt (Real.toNNReal_pos.mpr hv))
  have hfront : (gaussianReal 0 (finiteVariance p f).toNNReal) (frontier (Set.Iic y)) = 0 := by
    rw [frontier_Iic]
    exact measure_singleton y
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    h.tendsto (E := Set.Iic y) (by simpa only [ProbabilityMeasure.coe_mk, Measure.map_id] using hfront)
  have htr := (ENNReal.tendsto_toReal (measure_ne_top
    (gaussianReal 0 (finiteVariance p f).toNNReal) (Set.Iic y))).comp
    (show Tendsto (fun n : ℕ =>
      ((iidMeasure p hp hs).map (fun w => (Real.sqrt n)⁻¹ *
        ((∑ j ∈ Finset.range n, f (w j)) - n * finiteMean p f))) (Set.Iic y))
        atTop (𝓝 ((gaussianReal 0 (finiteVariance p f).toNNReal) (Set.Iic y))) by
      simpa only [ProbabilityMeasure.coe_mk, Measure.map_id] using ht)
  convert htr using 1
  · ext n
    dsimp only [Function.comp_apply]
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) measurableSet_Iic]
    rfl
  · rfl

def selfInformation (p : ι → ℝ) (i : ι) : ℝ := -Real.log (p i)

def entropy (p : ι → ℝ) : ℝ := finiteMean p (selfInformation p)

def varentropy (p : ι → ℝ) : ℝ := finiteVariance p (selfInformation p)

/-- The strong law for the constructed finite iid process, with finite
integrability and independence supplied by the construction. -/
theorem finite_iid_strong_law (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (f : ι → ℝ) :
    ∀ᵐ w ∂iidMeasure p hp hs,
      Tendsto (fun n : ℕ => (∑ j ∈ Finset.range n, f (w j)) / n)
        atTop (𝓝 (finiteMean p f)) := by
  let X : ℕ → (ℕ → ι) → ℝ := fun j w => f (w j)
  have hi : iIndepFun X (iidMeasure p hp hs) :=
    iIndepFun_infinitePi fun _ => measurable_of_countable f
  have hid : ∀ j, IdentDistrib (X j) (X 0) (iidMeasure p hp hs) (iidMeasure p hp hs) :=
    fun j => (iid_coordinate_identDistrib p hp hs f j).trans
      (iid_coordinate_identDistrib p hp hs f 0).symm
  have hmean : (iidMeasure p hp hs)[X 0] = finiteMean p f :=
    (iid_coordinate_identDistrib p hp hs f 0).integral_eq.trans (finiteMeasure_integral p hp hs f)
  have hint : Integrable (X 0) (iidMeasure p hp hs) :=
    (iid_coordinate_identDistrib p hp hs f 0).integrable_iff.mpr Integrable.of_finite
  have h := strong_law_ae_real X hint (fun _ _ hij => hi.indepFun hij) hid
  rwa [hmean] at h

omit [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Portmanteau at a finite real CDF threshold, with the null boundary explicit. -/
theorem distribution_cdf_real {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Y (fun _ => P) P') (c : ℝ)
    (hfront : (P'.map Y) (frontier (Set.Iic c)) = 0) :
    Tendsto (fun n => P.real {w | X n w ≤ c}) atTop
      (𝓝 ((P'.map Y).real (Set.Iic c))) := by
  have ht := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    h.tendsto (E := Set.Iic c) hfront
  have htr := (ENNReal.tendsto_toReal (measure_ne_top
    (P'.map Y) (Set.Iic c))).comp
    (show Tendsto (fun n : ℕ => (P.map (X n)) (Set.Iic c))
      atTop (𝓝 ((P'.map Y) (Set.Iic c))) from ht)
  convert htr using 1
  · ext n
    dsimp only [Function.comp_apply]
    rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) measurableSet_Iic]
    rfl
  · rfl

/-- A direct finite iid weak-law tail, derived from the actual strong law rather
than supplied as an asymptotic probability assumption. -/
theorem finite_iid_average_lower_tail (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (f : ι → ℝ) (c : ℝ) (hc : c < finiteMean p f) :
    Tendsto (fun n : ℕ => (iidMeasure p hp hs).real
      {w | (∑ j ∈ Finset.range n, f (w j)) / n ≤ c}) atTop (𝓝 0) := by
  have hm : ∀ n : ℕ, AEMeasurable
      (fun w : ℕ → ι => (∑ j ∈ Finset.range n, f (w j)) / n) (iidMeasure p hp hs) := by
    intro n
    exact ((Finset.measurable_sum _ fun j _ =>
      (measurable_of_countable f).comp (measurable_pi_apply j)).div_const n).aemeasurable
  have h := tendstoInDistribution_of_ae_tendsto hm measurable_const.aemeasurable
    (finite_iid_strong_law p hp hs f)
  have ht := distribution_cdf_real h c (by simp [frontier_Iic, Measure.map_const,
    ne_of_gt hc, ne_of_lt hc])
  simpa [Measure.map_const, Measure.real, Measure.dirac_apply', not_le_of_gt hc] using ht

/-- The direct-law counterpart: any fixed threshold above the actual entropy
captures asymptotically all iid spectral mass. -/
theorem finite_iid_average_upper_tail (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (f : ι → ℝ) (c : ℝ) (hc : finiteMean p f < c) :
    Tendsto (fun n : ℕ => (iidMeasure p hp hs).real
      {w | (∑ j ∈ Finset.range n, f (w j)) / n ≤ c}) atTop (𝓝 1) := by
  have hm : ∀ n : ℕ, AEMeasurable
      (fun w : ℕ → ι => (∑ j ∈ Finset.range n, f (w j)) / n) (iidMeasure p hp hs) := by
    intro n
    exact ((Finset.measurable_sum _ fun j _ =>
      (measurable_of_countable f).comp (measurable_pi_apply j)).div_const n).aemeasurable
  have h := tendstoInDistribution_of_ae_tendsto hm measurable_const.aemeasurable
    (finite_iid_strong_law p hp hs f)
  have ht := distribution_cdf_real h c (by simp [frontier_Iic, Measure.map_const,
    ne_of_gt hc, ne_of_lt hc])
  simpa [Measure.map_const, Measure.real, Measure.dirac_apply', hc.le] using ht

/-- The sharp strict weak-law alternatives for the finite self-information
probability in the physical converse. -/
theorem iidInformationEvent_law_of_large_numbers (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (c : ℝ) (hc : c ≠ entropy p) :
    Tendsto (fun n : ℕ => iidInformationEvent p n ((n : ℝ) * c)) atTop
      (𝓝 (if entropy p < c then 1 else 0)) := by
  have he (n : ℕ) (hn : 0 < n) : iidInformationEvent p n ((n : ℝ) * c) =
      (iidMeasure p hp hs).real {w | (∑ j ∈ Finset.range n, selfInformation p (w j)) / n ≤ c} := by
    rw [iidInformationEvent_eq_measure p hp hs]
    congr 2
    apply Set.ext
    intro w
    change ((∑ j ∈ Finset.range n, selfInformation p (w j)) ≤ (n : ℝ) * c) ↔
      (∑ j ∈ Finset.range n, selfInformation p (w j)) / (n : ℝ) ≤ c
    rw [div_le_iff₀ (show (0 : ℝ) < n from Nat.cast_pos.mpr hn)]
    constructor <;> intro hh <;> nlinarith
  by_cases hgt : entropy p < c
  · simp only [hgt, ite_true]
    apply (finite_iid_average_upper_tail p hp hs (selfInformation p) c hgt).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (he n hn).symm
  · have hlt : c < entropy p := lt_of_le_of_ne (le_of_not_gt hgt) hc
    simp only [hgt, ite_false]
    apply (finite_iid_average_lower_tail p hp hs (selfInformation p) c hlt).congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact (he n hn).symm

/-- The Gaussian limit for exactly the finite iid self-information event used
by the physical finite-block theorem. Zero eigenvalues remain allowed. -/
theorem iidInformationEvent_gaussian (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hv : 0 < varentropy p) (y : ℝ) :
    Tendsto (fun n : ℕ => iidInformationEvent p n
      ((n : ℝ) * entropy p + y * Real.sqrt n)) atTop
      (𝓝 ((gaussianReal 0 (varentropy p).toNNReal).real (Set.Iic y))) := by
  have h := finite_iid_centered_cdf p hp hs (selfInformation p) hv y
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [iidInformationEvent_eq_measure p hp hs]
  have hn' : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  congr 1
  apply Set.ext
  intro w
  change ((Real.sqrt (n : ℝ))⁻¹ *
    ((∑ j ∈ Finset.range n, -Real.log (p (w j))) - (n : ℝ) * entropy p) ≤ y) ↔ _
  rw [inv_mul_le_iff₀ hn']
  change (∑ j ∈ Finset.range n, -Real.log (p (w j))) - (n : ℝ) * entropy p ≤
    Real.sqrt (n : ℝ) * y ↔ _
  change _ ↔ (∑ j ∈ Finset.range n, -Real.log (p (w j))) ≤
    (n : ℝ) * entropy p + y * Real.sqrt n
  constructor <;> intro hh <;> nlinarith

/-- The finite iid Gaussian CDF limit also holds for every moving threshold
with the stated second-order expansion. Slutsky is applied to a constructed
constant perturbation; no Gaussian probability limit is an assumption. -/
theorem iidInformationEvent_gaussian_moving (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (hv : 0 < varentropy p) (x : ℕ → ℝ) (y : ℝ)
    (hx : Tendsto (fun n : ℕ => (x n - n * entropy p) / Real.sqrt n) atTop (𝓝 y)) :
    Tendsto (fun n : ℕ => iidInformationEvent p n (x n)) atTop
      (𝓝 ((gaussianReal 0 (varentropy p).toNNReal).real (Set.Iic y))) := by
  let a : ℕ → ℝ := fun n => (x n - n * entropy p) / Real.sqrt n
  have hclt := finite_iid_central_limit p hp hs (selfInformation p)
  have hconst : TendstoInMeasure (iidMeasure p hp hs)
      (fun n : ℕ => fun _ : ℕ → ι => -a n) atTop (fun _ => -y) := by
    apply tendstoInMeasure_of_tendsto_ae (fun _ => measurable_const.aestronglyMeasurable)
    exact Eventually.of_forall fun _ => hx.neg
  have hshift := hclt.add_of_tendstoInMeasure_const hconst (fun _ => measurable_const.aemeasurable)
  haveI : NullSingletonClass (gaussianReal 0 (varentropy p).toNNReal) :=
    nullSingletonClass_gaussianReal (ne_of_gt (Real.toNNReal_pos.mpr hv))
  have hfront : ((gaussianReal 0 (varentropy p).toNNReal).map
      (fun z : ℝ => z + -y)) (frontier (Set.Iic 0)) = 0 := by
    rw [frontier_Iic, Measure.map_apply (by fun_prop) (measurableSet_singleton 0)]
    have he : (fun z : ℝ => z + -y) ⁻¹' {0} = {y} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor <;> intro h <;> linarith
    rw [he]
    exact measure_singleton y
  have ht := distribution_cdf_real hshift 0 hfront
  have hCDF : ((gaussianReal 0 (varentropy p).toNNReal).map
      (fun z : ℝ => z + -y)).real (Set.Iic 0) =
      (gaussianReal 0 (varentropy p).toNNReal).real (Set.Iic y) := by
    unfold Measure.real
    rw [Measure.map_apply (by fun_prop) measurableSet_Iic]
    congr 2
    apply Set.ext
    intro z
    change z + -y ≤ 0 ↔ z ≤ y
    constructor <;> intro h <;> linarith
  change Tendsto (fun n : ℕ => (iidMeasure p hp hs).real
      {w | (Real.sqrt n)⁻¹ *
        ((∑ j ∈ Finset.range n, selfInformation p (w j)) - (n : ℝ) * entropy p) + -a n ≤ 0})
      atTop (𝓝 (((gaussianReal 0 (varentropy p).toNNReal).map
        (fun z : ℝ => z + -y)).real (Set.Iic 0))) at ht
  rw [hCDF] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [iidInformationEvent_eq_measure p hp hs]
  have hn' : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)
  congr 1
  apply Set.ext
  intro w
  change ((Real.sqrt n)⁻¹ *
    ((∑ j ∈ Finset.range n, -Real.log (p (w j))) - (n : ℝ) * entropy p) + -a n ≤ 0) ↔
    (∑ j ∈ Finset.range n, -Real.log (p (w j))) ≤ x n
  have he : (Real.sqrt n)⁻¹ *
      ((∑ j ∈ Finset.range n, -Real.log (p (w j))) - (n : ℝ) * entropy p) + -a n =
      ((∑ j ∈ Finset.range n, -Real.log (p (w j))) - x n) / Real.sqrt n := by
    dsimp [a]
    field_simp
    ring
  rw [he, div_le_iff₀ hn', zero_mul, sub_nonpos]

end
end ExtractionSpectrum
