import APPTReview.SpikeDecoupling
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

open scoped BigOperators Topology
open Matrix Filter
namespace APPTReview

noncomputable def sparseSpikeError (ds : List ℝ) (e : ℝ → ℝ) (M : ℝ) : ℝ :=
  ∑ d∈ds.toFinset,4*Real.sqrt (e d)*M^((d-1)/2)

theorem sparseSpikeError_tendsto (ds : List ℝ) (e : ℝ → ℝ)
    (hd : ∀ d∈ds,d<1) : Tendsto (sparseSpikeError ds e) atTop (nhds (0:ℝ)) := by
  have heach (d : ℝ) (hmem : d∈ds.toFinset) :
      Tendsto (fun M : ℝ => 4*Real.sqrt (e d)*M^((d-1)/2)) atTop (nhds (0:ℝ)) := by
    have hpos : 0<(1-d)/2 := by have h:=hd d (List.mem_toFinset.mp hmem); linarith
    have he : (d-1)/2 = -((1-d)/2) := by ring
    rw [he]
    simpa using (tendsto_rpow_neg_atTop hpos).const_mul (4*Real.sqrt (e d))
  change Tendsto (fun M : ℝ => ∑ d∈ds.toFinset,4*Real.sqrt (e d)*M^((d-1)/2)) atTop (nhds (0:ℝ))
  simpa using tendsto_finsetSum ds.toFinset heach

theorem sparseSpikeError_identity (ds : List ℝ) (e : ℝ → ℝ) (M : ℝ) (hM : 0<M) :
    4*(∑ d∈ds.toFinset,Real.sqrt (e d)*M^(d/2-1))*Real.sqrt M=sparseSpikeError ds e M := by
  unfold sparseSpikeError
  rw [mul_assoc,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Real.sqrt_eq_rpow M]
  have hp : M^(d/2-1)*M^(1/2:ℝ)=M^((d-1)/2) := by
    rw [← Real.rpow_add hM]
    congr 1
    ring
  calc
    4*(Real.sqrt (e d)*M^(d/2-1)*M^(1/2:ℝ)) = 4*Real.sqrt (e d)*(M^(d/2-1)*M^(1/2:ℝ)) := by ring
    _ = _ := by rw [hp]

/-- The threshold controls every admissible weight family and every chosen spike pair.
The fixed scales are strictly below one; no coupling error is dropped at finite m. -/
theorem lacunary_single_spike_unit_bound (ds : List ℝ) (hds : LacunaryScales ds)
    (hd1 : ∀ d∈ds,d<1) (e : ℝ → ℝ) (B : ℝ) (hB : 0≤B)
    (he : ∀ d∈ds,0≤e d) (heB : ∀ d∈ds,e d≤B)
    (a ε : ℝ) (ha : 0≤a) (hε : 0<ε) :
    ∃ M : ℕ, ∀ m : ℕ, M≤m →
      ∀ w : ℝ → Fin m × Fin m → ℝ,
      (∀ d∈ds,∀ z,0≤w d z) → (∀ d∈ds,∀ z,w d z≤1) →
      (∀ d∈ds,(∑ z,w d z)≤2*(m:ℝ)^(2-d)) →
      ∀ (s : Fin m → ℝ), (∀ i,0≤s i) → (∑ i,(s i)^2)=1 →
      ∀ i j : Fin m, i≠j →
      realRayleigh (lacunarySparseMatrix m ds e w) s+2*a*s i*s j ≤
        max (scaleEnergyBound ds e B) a+ε := by
  obtain ⟨M,hM⟩ := lacunary_fractional_graph_limit ds hds e B hB he heB (ε/2) (by linarith)
  have hlim := (sparseSpikeError_tendsto ds e hd1).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop)
  obtain ⟨N,hN⟩ := ((tendsto_order.mp hlim).2 (ε/2) (by linarith)).exists_forall_of_atTop
  refine ⟨max 2 (max M N),?_⟩
  intro m hm w hw hw1 hwr s hs0 hs i j hij
  have hmM : M≤m := (le_max_left M N).trans ((le_max_right _ _).trans hm)
  have hmN : N≤m := (le_max_right M N).trans ((le_max_right _ _).trans hm)
  have hmP : (0:ℝ)<m := by exact_mod_cast (show 0<m from lt_of_lt_of_le (by decide : 0<2) ((le_max_left _ _).trans hm))
  let A := lacunarySparseMatrix m ds e w
  let c : ℝ := ∑ d∈ds.toFinset,Real.sqrt (e d)*(m:ℝ)^(d/2-1)
  have hc0 (d : ℝ) : 0≤Real.sqrt (e d)*(m:ℝ)^(d/2-1) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos hmP _).le
  have hc : 0≤c := Finset.sum_nonneg (fun d _ => hc0 d)
  have hA (i j : Fin m) : 0≤A i j := Finset.sum_nonneg (fun d hd =>
    mul_nonneg (hc0 d) (hw d (List.mem_toFinset.mp hd) _))
  have hAc (i j : Fin m) : A i j≤c := by
    apply Finset.sum_le_sum
    intro d hd
    exact (mul_le_mul_of_nonneg_left (hw1 d (List.mem_toFinset.mp hd) _) (hc0 d)).trans_eq (mul_one _)
  have hunit (t : Fin m → ℝ) (ht0 : ∀ i,0≤t i) (ht : (∑ i,(t i)^2)=1) :
      realRayleigh A t≤scaleEnergyBound ds e B+ε/2 := by
    rw [lacunarySparseMatrix_rayleigh]
    have hbudget : ∀ d∈ds,(∑ z,w d z)≤2*sparseScaleRank (Real.log m) d := by
      intro d hd
      rw [sparseScaleRank_log _ _ hmP]
      exact hwr d hd
    have hh := hM m hmM t ht0 ht w hw hw1 hbudget
    simpa only [sparseScaleCoefficient_log _ _ _ hmP] using hh
  have hcap := rayleigh_le_of_nonnegative_unit A hA _ hunit
  have hfin := rayleigh_single_spike_bound A c (scaleEnergyBound ds e B+ε/2) a hc ha hA hAc hcap s hs0 hs i j hij
  have herr : 4*c*Real.sqrt (m:ℝ)<ε/2 := by
    rw [show c=∑ d∈ds.toFinset,Real.sqrt (e d)*(m:ℝ)^(d/2-1) by rfl,
      sparseSpikeError_identity ds e (m:ℝ) hmP]
    exact hN m hmN
  have hmax : max (scaleEnergyBound ds e B+ε/2) a≤max (scaleEnergyBound ds e B) a+ε/2 := by
    apply max_le
    · linarith [le_max_left (scaleEnergyBound ds e B) a]
    · linarith [le_max_right (scaleEnergyBound ds e B) a]
  simp only [Fintype.card_fin] at hfin
  linarith

end APPTReview
