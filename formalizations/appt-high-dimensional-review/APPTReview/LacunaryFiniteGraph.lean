import APPTReview.SchmidtLocalization
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

open scoped BigOperators NNReal Topology
open MeasureTheory Filter
namespace APPTReview

/-- A single scale width controls every finite unit Schmidt vector and every
fractional sparse layer, with explicit localization error. -/
theorem lacunary_finite_bound_with_error (ds : List ℝ) (hds : LacunaryScales ds)
    (e : ℝ → ℝ) (B : ℝ) (hB : 0≤B)
    (he : ∀ d∈ds,0≤e d) (heB : ∀ d∈ds,e d≤B)
    (ε : ℝ) (hε : 0<ε) :
    ∃ η : ℝ, 0<η ∧ ∀ (m : ℕ) (s : Fin m → ℝ)
      (hn : ∀ i,0≤s i) (hs : (∑ i,(s i)^2)=1)
      (L : ℝ) (hL : 0<L), Real.exp L=(m:ℝ) →
      ∀ w : ℝ → UpperPair m → ℝ,
      (∀ d∈ds,∀ q,0≤w d q) → (∀ d∈ds,∀ q,w d q≤1) →
      (∀ d∈ds,(∑ q,w d q)≤Real.exp ((2-d)*L)) →
      2*(∑ d∈ds.toFinset,Real.sqrt (e d)*Real.exp ((d/2-1)*L)*
        (∑ q,w d q*(s q.val.1*s q.val.2))) ≤
      scaleEnergyBound ds e B+ε+
        2*(∑ d∈ds.toFinset,Real.sqrt (e d))*(2*Real.exp (-η*L)+Real.sqrt (Real.exp (-η*L))) := by
  classical
  obtain ⟨δ,hδ,hδbound⟩ := lacunary_uniform_band_energy ds hds e B hB he heB ε hε
  refine ⟨δ/4,by positivity,?_⟩
  intro m s hn hs L hL hM w hw hw1 hrank
  let μ := scaleLift (schmidtEmpirical s hn hs L hL)
  let E := 2*Real.exp (-(δ/4)*L)+Real.sqrt (Real.exp (-(δ/4)*L))
  have hband := hδbound (schmidtEmpirical s hn hs L hL)
  have hd4 : 4*(δ/4)=δ := by ring
  have hlevel (d : ℝ) (hd : d∈ds.toFinset) :
      Real.sqrt (e d)*Real.exp ((d/2-1)*L)*(∑ q,w d q*(s q.val.1*s q.val.2)) ≤
      Real.sqrt (e d)*E+Real.sqrt (e d*(μ.prod μ).toMeasure.real (scaleBand d δ)/2) := by
    have hmem := List.mem_toFinset.mp hd
    have h := schmidt_level_localization s hn hs L hL hM d (δ/4) (by positivity)
      (w d) (hw d hmem) (hw1 d hmem) (hrank d hmem)
    rw [hd4] at h
    have hm := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg (e d))
    have heq : Real.sqrt (e d*(μ.prod μ).toMeasure.real (scaleBand d δ)/2)=
        Real.sqrt (e d)*Real.sqrt ((μ.prod μ).toMeasure.real (scaleBand d δ)/2) := by
      rw [mul_div_assoc,Real.sqrt_mul (he d hmem)]
    rw [heq]
    dsimp only [E,μ] at *
    nlinarith
  have hsum := Finset.sum_le_sum hlevel
  rw [Finset.sum_add_distrib,← Finset.sum_mul] at hsum
  have htw := mul_le_mul_of_nonneg_left hsum (by norm_num : (0:ℝ)≤2)
  change 2*(∑ d∈ds.toFinset,Real.sqrt (e d*(μ.prod μ).toMeasure.real (scaleBand d δ)/2))≤_ at hband
  change _≤scaleEnergyBound ds e B+ε+2*(∑ d∈ds.toFinset,Real.sqrt (e d))*E
  linarith

/-- Uniform finite-dimensional weighted graph estimate. All small-mass, product
localization, empirical measure and compactness dependencies are discharged. -/
theorem lacunary_weighted_graph_eventual (ds : List ℝ) (hds : LacunaryScales ds)
    (e : ℝ → ℝ) (B : ℝ) (hB : 0≤B)
    (he : ∀ d∈ds,0≤e d) (heB : ∀ d∈ds,e d≤B)
    (ε : ℝ) (hε : 0<ε) :
    ∃ M : ℕ, ∀ m : ℕ, M≤m → ∀ s : Fin m → ℝ,
      (∀ i,0≤s i) → (∑ i,(s i)^2)=1 → ∀ w : ℝ → UpperPair m → ℝ,
      (∀ d∈ds,∀ q,0≤w d q) → (∀ d∈ds,∀ q,w d q≤1) →
      (∀ d∈ds,(∑ q,w d q)≤Real.exp ((2-d)*Real.log (m:ℝ))) →
      2*(∑ d∈ds.toFinset,Real.sqrt (e d)*Real.exp ((d/2-1)*Real.log (m:ℝ))*
        (∑ q,w d q*(s q.val.1*s q.val.2))) ≤scaleEnergyBound ds e B+ε := by
  obtain ⟨η,hη,hbound⟩ := lacunary_finite_bound_with_error ds hds e B hB he heB (ε/2) (by positivity)
  let H := ∑ d∈ds.toFinset,Real.sqrt (e d)
  have hlog : Tendsto (fun m : ℕ => Real.log (m:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hexp : Tendsto (fun m : ℕ => Real.exp (-η*Real.log (m:ℝ))) atTop (𝓝 (0:ℝ)) :=
    Real.tendsto_exp_atBot.comp (hlog.const_mul_atTop_of_neg (by linarith : -η<0))
  have herr : Tendsto (fun m : ℕ => 2*H*(2*Real.exp (-η*Real.log (m:ℝ))+
      Real.sqrt (Real.exp (-η*Real.log (m:ℝ))))) atTop (𝓝 (0:ℝ)) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hexp
    simpa using ((hexp.const_mul 2).add hsqrt).const_mul (2*H)
  obtain ⟨M,hM⟩ := eventually_atTop.mp (herr.eventually_lt_const (by linarith : (0:ℝ)<ε/2))
  refine ⟨max M 2,?_⟩
  intro m hm s hn hs w hw hw1 hrank
  have hm2 : 2≤m := (le_max_right M 2).trans hm
  have hLm : 0<Real.log (m:ℝ) := Real.log_pos (by exact_mod_cast (show 1<m by omega))
  have hEM : Real.exp (Real.log (m:ℝ))=(m:ℝ) := Real.exp_log (by exact_mod_cast (show 0<m by omega))
  have h := hbound m s hn hs (Real.log (m:ℝ)) hLm hEM w hw hw1 hrank
  have herrm := hM m ((le_max_left M 2).trans hm)
  dsimp only [H] at herrm
  linarith

end APPTReview
