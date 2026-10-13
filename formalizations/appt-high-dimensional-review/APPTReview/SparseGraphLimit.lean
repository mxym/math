import APPTReview.SparseLocalization
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

open scoped BigOperators NNReal Topology
open MeasureTheory Filter
namespace APPTReview

theorem sparseScaleError_tendsto (η e : ℝ) (hη : 0<η) :
    Tendsto (fun L : ℝ => sparseScaleError L η e) atTop (𝓝 (0:ℝ)) := by
  have hx : Tendsto (fun L : ℝ => Real.exp (-η*L)) atTop (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_def,neg_mul,id_eq] using Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop hη (tendsto_id : Tendsto (fun x : ℝ => x) atTop atTop))
  have ha := hx.const_mul (3*Real.sqrt e)
  have hb := (hx.const_mul (4*e)).sqrt
  simpa [sparseScaleError] using ha.add hb

theorem sqrt_two_energy (e q : ℝ) : Real.sqrt (2*e*q)=2*Real.sqrt (e*q/2) := by
  rw [show 2*e*q=4*(e*q/2) by ring,Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
  rw [show Real.sqrt (4:ℝ)=2 by
    rw [show (4:ℝ)=2^2 by norm_num,Real.sqrt_sq (by norm_num : (0:ℝ)≤2)]]

/-- All levels are coupled through the same actual amplitude probability. -/
theorem sparse_multiscale_localization {m : ℕ} (L η : ℝ) (hL : 0<L) (hη : 0≤η)
    (ds : List ℝ) (e : ℝ → ℝ) (he : ∀ d∈ds,0≤e d)
    (hm : (m:ℝ)≤Real.exp L)
    (s : Fin m → ℝ) (hs0 : ∀ i,0≤s i) (hs : (∑ i,(s i)^2)=1)
    (w : ℝ → Fin m × Fin m → ℝ)
    (hw : ∀ d∈ds,∀ z,0≤w d z) (hw1 : ∀ d∈ds,∀ z,w d z≤1)
    (hwr : ∀ d∈ds,(∑ z,w d z)≤2*sparseScaleRank L d) :
    (∑ d∈ds.toFinset,sparseScaleCoefficient L d (e d)*(∑ z,w d z*(s z.1*s z.2))) ≤
      scaleBandEnergy (scaleLift (unitAmplitudeProbability L s hL hs0 hs)) ds e (4*η)+
      ∑ d∈ds.toFinset,sparseScaleError L η (e d) := by
  have hh := Finset.sum_le_sum (s:=ds.toFinset) (fun d hd =>
    sparse_scale_localization L d η (e d) hL hη (he d (List.mem_toFinset.mp hd))
      (by simpa using hm) s hs0 hs (w d) (hw d (List.mem_toFinset.mp hd))
      (hw1 d (List.mem_toFinset.mp hd)) (hwr d (List.mem_toFinset.mp hd)))
  simp only [Finset.sum_add_distrib,sqrt_two_energy,← Finset.mul_sum] at hh
  exact hh

/-- A single scale-size threshold controls every finite dimension, all
fractional sparse matrices, and all nonnegative unit test vectors. -/
theorem lacunary_fractional_uniform (ds : List ℝ) (hds : LacunaryScales ds)
    (e : ℝ → ℝ) (B : ℝ) (hB : 0≤B) (he : ∀ d∈ds,0≤e d)
    (heB : ∀ d∈ds,e d≤B) (ε : ℝ) (hε : 0<ε) :
    ∃ T : ℝ, 0<T ∧ ∀ (L : ℝ), T≤L → ∀ m : ℕ, (m:ℝ)≤Real.exp L →
      ∀ (s : Fin m → ℝ), (∀ i,0≤s i) → (∑ i,(s i)^2)=1 →
      ∀ (w : ℝ → Fin m × Fin m → ℝ),
      (∀ d∈ds,∀ z,0≤w d z) → (∀ d∈ds,∀ z,w d z≤1) →
      (∀ d∈ds,(∑ z,w d z)≤2*sparseScaleRank L d) →
      (∑ d∈ds.toFinset,sparseScaleCoefficient L d (e d)*(∑ z,w d z*(s z.1*s z.2))) ≤
        scaleEnergyBound ds e B+ε := by
  have heps : 0<ε/2 := by linarith
  obtain ⟨η,hη,hband⟩ := lacunary_uniform_all_smaller_bands ds hds e B hB he heB (ε/2) heps
  have hη4 : 0<η/4 := by linarith
  have hlim : Tendsto (fun L : ℝ => ∑ d∈ds.toFinset,sparseScaleError L (η/4) (e d))
      atTop (𝓝 (0:ℝ)) := by
    simpa using tendsto_finsetSum ds.toFinset (fun d _ => sparseScaleError_tendsto (η/4) (e d) hη4)
  have hevent : ∀ᶠ L : ℝ in atTop, (∑ d∈ds.toFinset,sparseScaleError L (η/4) (e d))<ε/2 :=
    (tendsto_order.mp hlim).2 (ε/2) heps
  obtain ⟨T,hT⟩ := hevent.exists_forall_of_atTop
  refine ⟨max 1 T,lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (le_max_left _ _),?_⟩
  intro L hTL m hm s hs0 hs w hw hw1 hwr
  have hLP : 0<L := lt_of_lt_of_le (by norm_num : (0:ℝ)<1) ((le_max_left _ _).trans hTL)
  have hsmall := hT L ((le_max_right _ _).trans hTL)
  have hbound := hband (unitAmplitudeProbability L s hLP hs0 hs) (4*(η/4)) (by linarith)
  have hh := sparse_multiscale_localization L (η/4) hLP hη4.le ds e he hm s hs0 hs w hw hw1 hwr
  linarith

/-- The sparse-graph limit in actual integer dimension. Each level has at
most m^(2-d) undirected edges (or twice that total fractional ordered weight).
This is a proved uniform Rayleigh bound, not an assumed graph-limit premise. -/
theorem lacunary_fractional_graph_limit (ds : List ℝ) (hds : LacunaryScales ds)
    (e : ℝ → ℝ) (B : ℝ) (hB : 0≤B) (he : ∀ d∈ds,0≤e d)
    (heB : ∀ d∈ds,e d≤B) (ε : ℝ) (hε : 0<ε) :
    ∃ M : ℕ, ∀ m : ℕ, M≤m →
      ∀ (s : Fin m → ℝ), (∀ i,0≤s i) → (∑ i,(s i)^2)=1 →
      ∀ (w : ℝ → Fin m × Fin m → ℝ),
      (∀ d∈ds,∀ z,0≤w d z) → (∀ d∈ds,∀ z,w d z≤1) →
      (∀ d∈ds,(∑ z,w d z)≤2*sparseScaleRank (Real.log m) d) →
      (∑ d∈ds.toFinset,sparseScaleCoefficient (Real.log m) d (e d)*(∑ z,w d z*(s z.1*s z.2))) ≤
        scaleEnergyBound ds e B+ε := by
  obtain ⟨T,hTP,hT⟩ := lacunary_fractional_uniform ds hds e B hB he heB ε hε
  obtain ⟨M,hM⟩ := exists_nat_gt (max (2:ℝ) (Real.exp T))
  refine ⟨M,?_⟩
  intro m hm s hs0 hs w hw hw1 hwr
  have hMm : (M:ℝ)≤m := by exact_mod_cast hm
  have hmP : (0:ℝ)<m := lt_of_lt_of_le (by norm_num : (0:ℝ)<2)
    ((le_max_left _ _).trans (hM.le.trans hMm))
  have hlog := Real.log_le_log (Real.exp_pos T) ((le_max_right _ _).trans (hM.le.trans hMm))
  rw [Real.log_exp] at hlog
  exact hT (Real.log m) hlog m (by rw [Real.exp_log hmP]) s hs0 hs w hw hw1 hwr

end APPTReview
