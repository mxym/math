import BapatLaplace
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
open Filter
open scoped Topology

namespace BapatRealExistence

/-- Exact rank-four prefactor limit with the base size fixed before repetition.
The two degree factors are N+3 and N+2, as in the sphere normalization. -/
theorem rank_four_prefactor_limit {n : ℕ} (hn : 0 < n) :
    Tendsto (fun L : ℕ => (L : ℝ)^4 /
      (((n*L).choose 2 : ℝ) * ((n*L : ℕ) + 3) * ((n*L : ℕ) + 2)))
      atTop (𝓝 (2 / (n : ℝ)^4)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hI : Tendsto (fun L : ℕ => (L : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hc : Tendsto (fun _ : ℕ => (n : ℝ)) atTop (𝓝 (n : ℝ)) := tendsto_const_nhds
  have hd := ((hc.mul (hc.sub hI)).mul (hc.add (hI.const_mul 3))).mul
    (hc.add (hI.const_mul 2))
  have hd0 : (n : ℝ) * (n - 0) * (n + 3*0) * (n + 2*0) ≠ 0 := by
    simpa using mul_ne_zero (mul_ne_zero (mul_ne_zero hn0 hn0) hn0) hn0
  have h := (tendsto_const_nhds (x := (2 : ℝ))).div hd hd0
  have hnorm : Tendsto (fun L : ℕ => 2 /
      ((n : ℝ) * (n - (L : ℝ)⁻¹) * (n + 3*(L : ℝ)⁻¹) * (n + 2*(L : ℝ)⁻¹)))
      atTop (𝓝 (2 / (n : ℝ)^4)) := by
    convert h using 1 <;> congr 1 <;> ring
  apply hnorm.congr'
  filter_upwards [eventually_ge_atTop 1] with L hL
  have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast (show L ≠ 0 by omega)
  rw [Nat.cast_choose_two]
  push_cast
  field_simp
  <;> ring

end BapatRealExistence
