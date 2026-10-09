import CofactorEntropyProduct
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! The exact entropy constant tends to the sharp endpoint; one real parameter selects all lower data. -/
set_option autoImplicit false
open scoped Topology
open Filter
namespace CofactorSpectral
noncomputable section

theorem entropyConstant_log_tendsto :
    Tendsto (fun x : ℝ => entropyConstant (1+x)*Real.log (1+x)) (𝓝[>] 0) (𝓝 (Real.exp 1)) := by
  have hx : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hRatio : Tendsto (fun x : ℝ => Real.log (1+x)/x) (𝓝[>] 0) (𝓝 1) := by
    simpa only [inv_one,Real.log_one,sub_zero,smul_eq_mul,div_eq_mul_inv,mul_comm] using
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope_zero_right
  have hOne : Tendsto (fun x : ℝ => 1+x) (𝓝[>] 0) (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds.add hx :
      Tendsto (fun x : ℝ => 1+x) (𝓝[>] 0) (𝓝 ((1 : ℝ)+0)))
  have hArg := hOne.mul hRatio
  have hExp : Tendsto (fun x : ℝ => Real.exp ((1+x)*(Real.log (1+x)/x)))
      (𝓝[>] 0) (𝓝 (Real.exp 1)) := by
    simpa only [mul_one,Function.comp_def] using Real.continuous_exp.continuousAt.tendsto.comp hArg
  have h := hExp.mul hRatio
  have he : (fun x : ℝ => entropyConstant (1+x)*Real.log (1+x)) =ᶠ[𝓝[>] 0]
      (fun x => Real.exp ((1+x)*(Real.log (1+x)/x))*(Real.log (1+x)/x)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx0
    have hx0 : 0 < x := hx0
    have hs : 1+x-1 = x := by ring
    unfold entropyConstant
    rw [hs,Real.rpow_def_of_pos (by linarith : 0 < 1+x)]
    have ha : Real.log (1+x)*((1+x)/x) = (1+x)*(Real.log (1+x)/x) := by ring
    rw [ha]
    ring
  exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm he) (by simpa only [mul_one] using h)

def lowerParameterC (t : ℝ) : ℝ := (1+t)*entropyConstant (1+t)/(Real.exp 1*(1-t))

theorem lowerParameterC_pos (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) : 0 < lowerParameterC t :=
  div_pos (mul_pos (by linarith) (entropyConstant_pos _ (by linarith)))
    (mul_pos (Real.exp_pos _) (by linarith))

theorem lowerParameterC_theta (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    entropyConstant (1+t)/(lowerParameterC t*Real.exp 1*(1-t)) = 1/(1+t) := by
  have hE := (entropyConstant_pos (1+t) (by linarith)).ne'
  have hp : 1+t ≠ 0 := by linarith
  have hm : 1-t ≠ 0 := by linarith
  unfold lowerParameterC
  field_simp [hE,hp,hm,Real.exp_ne_zero]

theorem lowerParameterC_theta_lt_one (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    entropyConstant (1+t)/(lowerParameterC t*Real.exp 1*(1-t)) < 1 := by
  rw [lowerParameterC_theta t ht0 ht1]
  apply (div_lt_iff₀ (by linarith : 0 < 1+t)).2
  linarith

theorem sharp_lower_coefficient_tendsto :
    Tendsto (fun t : ℝ => 1/(lowerParameterC t*(1+t)*Real.log (1+t))) (𝓝[>] 0) (𝓝 1) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hOne : Tendsto (fun t : ℝ => 1+t) (𝓝[>] 0) (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds.add ht :
      Tendsto (fun t : ℝ => 1+t) (𝓝[>] 0) (𝓝 ((1 : ℝ)+0)))
  have hnum : Tendsto (fun t : ℝ => Real.exp 1*(1-t)) (𝓝[>] 0) (𝓝 (Real.exp 1)) := by
    simpa only [sub_zero,mul_one] using
      (tendsto_const_nhds.mul (tendsto_const_nhds.sub ht) :
        Tendsto (fun t : ℝ => Real.exp 1*(1-t)) (𝓝[>] 0) (𝓝 (Real.exp 1*((1 : ℝ)-0))))
  have hden := (hOne.pow 2).mul entropyConstant_log_tendsto
  have h := hnum.div hden (by simpa only [one_pow,one_mul] using Real.exp_ne_zero 1)
  have he : (fun t : ℝ => 1/(lowerParameterC t*(1+t)*Real.log (1+t))) =ᶠ[𝓝[>] 0]
      (fun t => Real.exp 1*(1-t)/((1+t)^2*(entropyConstant (1+t)*Real.log (1+t)))) := by
    have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 := ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
    filter_upwards [self_mem_nhdsWithin,hsmall] with t ht0 ht1
    have ht0 : 0 < t := ht0
    have hE := (entropyConstant_pos (1+t) (by linarith)).ne'
    have hp : 1+t ≠ 0 := by linarith
    have hm : 1-t ≠ 0 := by linarith
    have hl := (Real.log_pos (by linarith : 1 < 1+t)).ne'
    unfold lowerParameterC
    field_simp [hE,hp,hm,hl,Real.exp_ne_zero]
    <;> ring
  exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm he)
    (by
      convert h using 1 <;> simp only [one_pow,one_mul,div_self (Real.exp_ne_zero 1)]
      )

theorem exists_sharp_lower_parameters (ε : ℝ) (hε : 0 < ε) :
    ∃ C b δ η : ℝ, 0 < C ∧ 1 < b ∧ 0 < δ ∧ δ < 1 ∧ 0 < η ∧
      entropyConstant b/(C*Real.exp 1*(1-δ)) < 1 ∧
      1-ε ≤ 1/(C*(1+η)*Real.log b) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 := ht.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hgood := sharp_lower_coefficient_tendsto.eventually (eventually_ge_nhds (by linarith : 1-ε < 1))
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t,ht0,ht1,hval⟩ := Filter.Eventually.exists (Filter.Eventually.and hpos
    (Filter.Eventually.and hsmall hgood))
  have ht0 : 0 < t := ht0
  exact ⟨lowerParameterC t,1+t,t,t,lowerParameterC_pos t ht0 ht1,by linarith,
    ht0,ht1,ht0,lowerParameterC_theta_lt_one t ht0 ht1,hval⟩

end
end CofactorSpectral
