import Mathlib.Tactic

/-! Partial scalar algebra for the written Gaussian theorem. No Gaussian
measure, perimeter, facet continuity or deformation theorem is formalized.
Every hypothesis here is explicit; these exports are not Theorem 1. -/
namespace BalancedFourGlobal

theorem spectral_residual_bound (μ l₁ l₂ l₃ ε : ℝ)
    (hμ : 0 ≤ μ) (hε : 0 ≤ ε)
    (h₁ : 0 ≤ l₁ ∧ l₁ ≤ μ) (h₂ : 0 ≤ l₂ ∧ l₂ ≤ μ)
    (h₃ : 0 ≤ l₃ ∧ l₃ ≤ μ) :
    ε / 3 * ((l₁-μ)^2+(l₂-μ)^2+(l₃-μ)^2) ≤ ε*μ^2 := by
  have hsq₁ : (l₁-μ)^2 ≤ μ^2 := by nlinarith
  have hsq₂ : (l₂-μ)^2 ≤ μ^2 := by nlinarith
  have hsq₃ : (l₃-μ)^2 ≤ μ^2 := by nlinarith
  have ht : (l₁-μ)^2+(l₂-μ)^2+(l₃-μ)^2 ≤ 3*μ^2 := by linarith
  nlinarith [mul_nonneg hε (sub_nonneg.mpr ht)]

theorem euler_upper_bound (μ ε tr value : ℝ)
    (hε : 0 ≤ ε) (hε1 : ε < 1) (htr : 0 ≤ tr)
    (hv : value = (1-ε)*μ+ε*tr/3) : μ ≤ value/(1-ε) := by
  apply (le_div_iff₀ (by linarith : 0 < 1-ε)).2
  nlinarith [mul_nonneg hε htr]

theorem uniform_separation (k μ cap ell small δ : ℝ)
    (hμ : 0 ≤ μ) (hcap : 0 < cap) (hμcap : μ ≤ cap)
    (hell : 0 ≤ ell) (hsmall : 0 ≤ small) (hsmallδ : small ≤ δ)
    (hδ : 0 < δ) (hk : 2*cap*δ ≤ k)
    (hpair : k ≤ μ*(ell+small)) : δ ≤ ell := by
  by_contra h
  have hellδ : ell < δ := lt_of_not_ge h
  have hprod : μ*(ell+small) ≤ cap*(ell+small) := by
    exact mul_le_mul_of_nonneg_right hμcap (add_nonneg hell hsmall)
  nlinarith

theorem rank_one_trace_contradiction (a b w tr : ℝ)
    (hb : 0 < b) (hab : a < b) (ha : 3*b/4 < a)
    (hw : 2*(b-a)*w = b) (htr : 2*w ≤ tr) (hupper : tr ≤ 3) : False := by
  have hd : 0 < b-a := sub_pos.mpr hab
  have hw2 : 2 < w := by nlinarith
  linarith

theorem critical_perimeter_bound (c cstar S factor : ℝ)
    (hf : 0 < factor) (hlower : cstar*factor ≤ S)
    (hupper : S ≤ c*factor) : cstar ≤ c := by nlinarith

theorem local_diagonal_identity (a c u v s ρ : ℝ)
    (ht : u+v+s=3*ρ) :
    4*a^2*((c*(u-(v+s)/2)-(v+s)/2)*(v+s)
      +(c*(v-(u+s)/2)-(u+s)/2)*(u+s)
      +(c*(s-(u+v)/2)-(u+v)/2)*(u+v))
    = -24*a^2*ρ^2-2*a^2*(3*c+1)*
      ((u-ρ)^2+(v-ρ)^2+(s-ρ)^2) := by
  have hs : s=3*ρ-u-v := by linarith
  rw [hs]
  ring

theorem local_hessian_strict (a c h diag off : ℝ)
    (ha : 0 < a) (hc : 0 < c) (hc1 : c < 1)
    (hd : 0 ≤ diag) (ho : 0 ≤ off) (hn : 0 < diag+off) :
    -2*a^2*(3*c+1)*diag-8*a^2*(1+h^2-c)*off < 0 := by
  have ha2 : 0 < a^2 := sq_pos_of_pos ha
  have hcpos : 0 < 3*c+1 := by linarith
  have hother : 0 < 1+h^2-c := by nlinarith [sq_nonneg h]
  have hA : 0 < 2*a^2*(3*c+1) := by positivity
  have hB : 0 < 8*a^2*(1+h^2-c) := by positivity
  rcases lt_or_eq_of_le hd with hdp | hdz
  · have hfirst := mul_pos hA hdp
    have hsecond := mul_nonneg (le_of_lt hB) ho
    nlinarith
  · have hop : 0 < off := by linarith
    have hsecond := mul_pos hB hop
    nlinarith

theorem profile_margin :
    (1 : ℚ)-9/16+(9/16)^2/2-(9/16)^3/6-9/16=29/8192 := by norm_num

#print axioms spectral_residual_bound
#print axioms euler_upper_bound
#print axioms uniform_separation
#print axioms rank_one_trace_contradiction
#print axioms critical_perimeter_bound
#print axioms local_diagonal_identity
#print axioms local_hessian_strict
#print axioms profile_margin
end BalancedFourGlobal
