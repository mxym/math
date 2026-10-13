import APPTReview.LacunaryPurityFinite

open scoped BigOperators Topology ComplexOrder
open Matrix Filter
namespace APPTReview

theorem lacunaryTraceError_tendsto (ds : List ℝ) (e : ℝ → ℝ) (a : ℝ)
    (hd : ∀ d∈ds,0<d) : Tendsto (lacunaryTraceError ds e a) atTop (nhds (0:ℝ)) := by
  have hfirst : Tendsto (fun M : ℝ => a*M^(-1:ℝ)) atTop (nhds (0:ℝ)) := by
    simpa using (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1)).const_mul a
  have hterm (d : ℝ) (hdS : d∈ds.toFinset) :
      Tendsto (fun M : ℝ => Real.sqrt (e d)*M^(-d/2)) atTop (nhds (0:ℝ)) := by
    have hpos : 0<d/2 := by have hh:=hd d (List.mem_toFinset.mp hdS); linarith
    have hh := (tendsto_rpow_neg_atTop hpos).const_mul (Real.sqrt (e d))
    simpa only [neg_div,mul_zero] using hh
  have hsum := tendsto_finsetSum ds.toFinset hterm
  change Tendsto (fun M : ℝ => a*M^(-1:ℝ)+∑ d∈ds.toFinset,Real.sqrt (e d)*M^(-d/2)) atTop (nhds (0:ℝ))
  simpa using hfirst.add hsum

theorem lacunaryMomentError_tendsto (ds : List ℝ) (e : ℝ → ℝ)
    (hd : ∀ d∈ds,d<2) : Tendsto (lacunaryMomentError ds e) atTop (nhds (0:ℝ)) := by
  have hterm (d : ℝ) (hdS : d∈ds.toFinset) :
      Tendsto (fun M : ℝ => e d*M^(d-2)) atTop (nhds (0:ℝ)) := by
    have hpos : 0<2-d := by have hh:=hd d (List.mem_toFinset.mp hdS); linarith
    have he : d-2=-(2-d) := by ring
    rw [he]
    simpa using (tendsto_rpow_neg_atTop hpos).const_mul (e d)
  change Tendsto (fun M : ℝ => ∑ d∈ds.toFinset,e d*M^(d-2)) atTop (nhds (0:ℝ))
  simpa using tendsto_finsetSum ds.toFinset hterm

/-- The explicit finite loss tends to zero for every fixed finite scale list. -/
theorem lacunaryPurityLower_tendsto (ds : List ℝ) (e : ℝ → ℝ) (a : ℝ)
    (hd0 : ∀ d∈ds,0<d) (hd2 : ∀ d∈ds,d<2) :
    Tendsto (lacunaryPurityLower ds e a) atTop (nhds (a^2+∑ d∈ds.toFinset,e d)) := by
  let E := a^2+∑ d∈ds.toFinset,e d
  have ht := lacunaryTraceError_tendsto ds e a hd0
  have he := lacunaryMomentError_tendsto ds e hd2
  have hnum := (tendsto_const_nhds : Tendsto (fun _ : ℝ => E) atTop (nhds E)).sub he
  have hden := ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1:ℝ)) atTop (nhds 1)).add ht).pow 2
  have hdiv := hnum.div hden (by norm_num : ((1:ℝ)+0)^2≠0)
  have hh := hdiv.sub (ht.pow 2)
  change Tendsto (fun M : ℝ => (E-lacunaryMomentError ds e M)/(1+lacunaryTraceError ds e a M)^2-
    (lacunaryTraceError ds e a M)^2) atTop (nhds E)
  simpa only [Pi.div_apply,add_zero,one_pow,sub_zero,div_one,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true] using hh

/-- A complete uniform physical lower construction at every fixed admissible
energy allocation. No projection, Schmidt or graph-limit premise is left open. -/
theorem canonical_lacunary_energy_lower (ds : List ℝ) (hds : LacunaryScales ds)
    (hd1 : ∀ d∈ds,d<1) (e : ℝ → ℝ) (B a : ℝ) (hB : 0≤B)
    (he : ∀ d∈ds,0≤e d) (heB : ∀ d∈ds,e d≤B)
    (ha : 0≤a) (ha2 : a<2) (henergy : scaleEnergyBound ds e B<2)
    (ε : ℝ) (hε : 0<ε) :
    ∃ M : ℕ, 2≤M ∧ ∀ m n : ℕ, M≤m → m≤n →
      ∃ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
      a^2+(∑ d∈ds.toFinset,e d)-ε≤((m:ℝ)*n)^2*(APPT.Quantum.purity A-1/((m:ℝ)*n)) := by
  obtain ⟨M,hM2,hM⟩ := canonical_lacunary_states_appt ds hds hd1 e B a hB he heB ha ha2 henergy
  have hlim := (lacunaryPurityLower_tendsto ds e a hds.1
    (fun d hd => (hd1 d hd).trans (by norm_num : (1:ℝ)<2))).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m:ℝ)) atTop atTop)
  obtain ⟨N,hN⟩ := ((tendsto_order.mp hlim).1 (a^2+(∑ d∈ds.toFinset,e d)-ε) (by linarith)).exists_forall_of_atTop
  refine ⟨max M N,hM2.trans (le_max_left _ _),?_⟩
  intro m n hm hmn
  have hmM : M≤m := (le_max_left _ _).trans hm
  have hmN : N≤m := (le_max_right _ _).trans hm
  have hm0 : 0<m := by omega
  have hn0 : 0<n := by omega
  have hp := hM m n hm0 hn0 hmM hmn
  refine ⟨canonicalLacunaryState ds e a m n hm0 hn0,hp.1,hp.2,?_⟩
  exact (hN m hmN).le.trans (canonical_lacunary_purity_finite hm0 hn0 hmn ds
    (fun d hd => (hds.1 d hd).le) e he a ha)

end APPTReview
