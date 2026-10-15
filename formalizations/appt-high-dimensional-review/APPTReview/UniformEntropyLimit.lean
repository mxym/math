import APPTReview.UniformEntropyBound

open scoped BigOperators ComplexOrder Topology
open Matrix Filter
namespace APPTReview

/-- All error parameters depend on the first dimension alone and vanish at
infinity. No boundedness or convergence of the aspect ratio is required. -/
theorem entropy_uniform_parameters_tendsto :
    Tendsto entropyBulkRadius atTop (𝓝 (0:ℝ)) ∧
    Tendsto entropyUniformMeanRadius atTop (𝓝 (0:ℝ)) ∧
    Tendsto entropyUniformFactor atTop (𝓝 (1:ℝ)) := by
  have hs : Tendsto (fun k : ℕ => k+1) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with k hk
    omega
  have hi : Tendsto (fun k : ℕ => (((k+1:ℕ):ℝ))⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hs)
  have hδbase : Tendsto (fun k : ℕ => 8/((k+1:ℕ):ℝ)) atTop (𝓝 (0:ℝ)) := by
    simpa only [div_eq_mul_inv,mul_zero] using hi.const_mul 8
  have hδ : Tendsto entropyBulkRadius atTop (𝓝 (0:ℝ)) := by
    change Tendsto (fun k : ℕ => Real.sqrt (8/((k+1:ℕ):ℝ))) atTop (𝓝 (0:ℝ))
    simpa only [Function.comp_def,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hδbase
  have hν : Tendsto entropyUniformMeanRadius atTop (𝓝 (0:ℝ)) := by
    change Tendsto (fun k : ℕ => 3/((k+1:ℕ):ℝ)) atTop (𝓝 (0:ℝ))
    simpa only [div_eq_mul_inv,mul_zero] using hi.const_mul 3
  have hq : Tendsto (fun k : ℕ => ((k+2:ℕ):ℝ)/((k+1:ℕ):ℝ)) atTop (𝓝 (1:ℝ)) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).add hi
    convert hh using 1
    · funext k
      have hp : ((k+1:ℕ):ℝ)≠0 := by positivity
      push_cast;field_simp;ring
    · norm_num
  have hdenδ := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub hδ
  have hdenν := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub hν
  have hfrac := (hδ.const_mul 10).div hdenδ (by norm_num : (1:ℝ)-0≠0)
  have hnum := (hfrac.const_add 1).add (hν.const_mul 10)
  have hfactor := (hq.pow 2).mul (hnum.div hdenν (by norm_num : (1:ℝ)-0≠0))
  refine ⟨hδ,hν,?_⟩
  change Tendsto (fun k : ℕ => (((k+2:ℕ):ℝ)/((k+1:ℕ):ℝ))^2*((1+10*entropyBulkRadius k/(1-entropyBulkRadius k)+10*entropyUniformMeanRadius k)/(1-entropyUniformMeanRadius k))) atTop (𝓝 (1:ℝ))
  simpa only [Pi.div_apply,mul_zero,sub_zero,zero_div,add_zero,div_one,one_pow,mul_one] using hfactor

/-- Uniform upper half of the full von Neumann entropy law. One threshold
works for EVERY n>=m and every actual APPT density matrix, even when n/m has
no finite bound. This statement makes no entropy-attainment claim. -/
theorem appt_vonNeumann_uniform_upper (ε : ℝ) (hε : 0<ε) :
    ∃ M : ℕ, 2≤M ∧ ∀ m n : ℕ, M≤m → m≤n →
    ∀ (A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)
      (hρ : APPT.Quantum.IsDensity A), APPT.Quantum.AbsolutelyPPT A →
      2*(Fintype.card (Fin m × Fin n):ℝ)*vonNeumannDeficit hρ≤
        (1+ε)*max 8 (4+(n:ℝ)/(m:ℝ)) := by
  obtain ⟨hδ,hν,hF⟩:=entropy_uniform_parameters_tendsto
  have hev := ((tendsto_order.mp hδ).2 1 (by norm_num)).and
    (((tendsto_order.mp hν).2 1 (by norm_num)).and
      ((tendsto_order.mp hF).2 (1+ε) (by linarith)))
  obtain ⟨L,hL⟩:=hev.exists_forall_of_atTop
  refine ⟨L+2,by omega,?_⟩
  intro m n hm hmn A hρ hP
  obtain ⟨k,rfl⟩ : ∃ k,m=k+2 := ⟨m-2,by omega⟩
  obtain ⟨hkδ,hkν,hkF⟩:=hL k (by omega)
  have hbound:=density_appt_uniform_dimension_entropy_bound hmn hρ hP hkδ hkν
  have hK : 0≤max (8:ℝ) (4+(n:ℝ)/((k+2:ℕ):ℝ)) := (by norm_num : (0:ℝ)≤8).trans (le_max_left _ _)
  have hh:=hbound.trans (mul_le_mul_of_nonneg_left hkF.le hK)
  simpa only [mul_comm] using hh

end APPTReview
