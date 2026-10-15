import APPTReview.DimensionEntropyBound
import Mathlib.Topology.Instances.Real.Lemmas

open scoped BigOperators Topology
open Filter
namespace APPTReview

/-- All dimension-only error terms vanish at every fixed finite aspect ratio.
This is independent of which APPT state is chosen at each dimension. -/
theorem entropy_dimension_limits (k n : ℕ → ℕ) (γ : ℝ)
    (hk : Tendsto k atTop atTop)
    (hratio : Tendsto (fun j => (n j:ℝ)/((k j+2:ℕ):ℝ)) atTop (𝓝 γ)) :
    Tendsto (fun j => (Fintype.card (Fin (k j+2) × Fin (n j)):ℝ)/((k j+1:ℕ):ℝ)^2) atTop (𝓝 γ) ∧
    Tendsto (fun j => entropyVarianceCap (k j) (n j)) atTop (𝓝 (max 8 (4+γ))) ∧
    Tendsto (fun j => entropyBulkRadius (k j)) atTop (𝓝 (0:ℝ)) ∧
    Tendsto (fun j => entropyMeanRadius (k j) (n j)) atTop (𝓝 (0:ℝ)) ∧
    Tendsto (fun j => entropyTaylorError (k j) (n j)) atTop (𝓝 (0:ℝ)) := by
  have hnat (c : ℕ) : Tendsto (fun j => k j+c) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro N
    filter_upwards [(Filter.tendsto_atTop.1 hk) N] with j hj
    omega
  have hcast (c : ℕ) : Tendsto (fun j => ((k j+c:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (hnat c)
  have hinvM : Tendsto (fun j => (((k j+2:ℕ):ℝ))⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (hcast 2)
  have hinvH : Tendsto (fun j => (((k j+1:ℕ):ℝ))⁻¹) atTop (𝓝 (0:ℝ)) :=
    tendsto_inv_atTop_zero.comp (hcast 1)
  have hrat : Tendsto (fun j => ((k j+2:ℕ):ℝ)/((k j+1:ℕ):ℝ)) atTop (𝓝 (1:ℝ)) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).add hinvH
    convert hh using 1
    · funext j
      have hden : ((k j+1:ℕ):ℝ)≠0 := by positivity
      push_cast
      field_simp
      ring
    · norm_num
  have hd : Tendsto (fun j => (Fintype.card (Fin (k j+2) × Fin (n j)):ℝ)/((k j+1:ℕ):ℝ)^2) atTop (𝓝 γ) := by
    have hh := hratio.mul (hrat.pow 2)
    convert hh using 1
    · funext j
      have hm : ((k j+2:ℕ):ℝ)≠0 := by positivity
      have ht : ((k j+1:ℕ):ℝ)≠0 := by positivity
      simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
      field_simp
    · norm_num
  have hC : Tendsto (fun j => entropyVarianceCap (k j) (n j)) atTop (𝓝 (max 8 (4+γ))) := by
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (8:ℝ)) atTop (𝓝 8)).max (hd.const_add 4)
  have hδbase : Tendsto (fun j => 8/((k j+1:ℕ):ℝ)) atTop (𝓝 (0:ℝ)) := by
    simpa only [div_eq_mul_inv,mul_zero] using hinvH.const_mul 8
  have hδ : Tendsto (fun j => entropyBulkRadius (k j)) atTop (𝓝 (0:ℝ)) := by
    simpa only [entropyBulkRadius,Function.comp_def,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hδbase
  have hνbase : Tendsto (fun j => 4*entropyVarianceCap (k j) (n j)/((k j+2:ℕ):ℝ)^2) atTop (𝓝 (0:ℝ)) := by
    have hh := (hC.const_mul 4).mul (hinvM.pow 2)
    simpa only [div_eq_mul_inv,inv_pow,zero_pow,ne_eq,OfNat.ofNat_ne_zero,not_false_eq_true,mul_zero] using hh
  have hν : Tendsto (fun j => entropyMeanRadius (k j) (n j)) atTop (𝓝 (0:ℝ)) := by
    simpa only [entropyMeanRadius,Function.comp_def,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hνbase
  have hQ : Tendsto (fun j => entropyMomentCap (k j) (n j)) atTop (𝓝 ((1+4*γ)*max 8 (4+γ))) := by
    have hh := ((hratio.const_mul 4).const_add 1).mul hC
    convert hh using 1
    funext j
    unfold entropyMomentCap
    simp only [Fintype.card_prod,Fintype.card_fin,Nat.cast_mul]
    have hm : ((k j+2:ℕ):ℝ)≠0 := by positivity
    congr 1
    field_simp
  have hden := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)).sub hδ).const_mul 2
  have hfrac := hδ.div hden (by norm_num : (2:ℝ)*(1-0)≠0)
  have herr := (hfrac.add (hν.div_const 2)).mul hQ
  refine ⟨hd,hC,hδ,hν,?_⟩
  simpa only [entropyTaylorError,Pi.div_apply,sub_zero,mul_one,zero_div,add_zero,zero_mul] using herr

end APPTReview
