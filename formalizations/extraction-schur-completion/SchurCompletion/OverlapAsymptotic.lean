import SchurCompletion.OverlapMoments

open scoped BigOperators Topology
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
noncomputable section

theorem affineStep_cutoff_lt_one (s N : ℕ) (hs : 0 < s) :
    affineStep s (powerCutoff N) < 1 := by
  unfold affineStep
  apply (div_lt_one (by exact_mod_cast hs : (0 : ℝ) < s)).mpr
  linarith [(powerCutoff_bounds N).2]

/-- The actual normalized projection-overlap moments have the sharp all-rank
constant, deduced from the actual principal-minor moments. -/
theorem haarOverlapMoment_scaled_limit (s t : ℕ) (hs : 0 < s) :
    Tendsto (fun k : ℕ => (k : ℝ)^(s*t)*haarOverlapMoment (t+s) s k (by omega))
      atTop (𝓝 ((s : ℝ)^(s*t)*weylCrossDenominator s t)) := by
  let g := s*t
  let A := weylCrossDenominator s t
  let M := fun k => (haarMinorMoment (t+s) s k (by omega)).re
  let c := 1/(s : ℝ)
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hc : c ≠ 0 := by dsimp [c]; positivity
  have hM : Tendsto (fun k : ℕ => (k : ℝ)^g*M k) atTop (𝓝 A) :=
    haarMinorMoment_scaled_limit s t
  let ell := fun k : ℕ => ⌈(k : ℝ)/(s : ℝ)⌉₊
  have hell : Tendsto ell atTop atTop :=
    tendsto_nat_ceil_atTop.comp (tendsto_natCast_atTop_atTop.atTop_div_const hsR)
  have hL := power_moment_reindex_limit g M A c hM ell hell (nat_ceil_ratio_limit s hs) hc
  let cN := fun N : ℕ => (N : ℝ)/((s : ℝ)*((N : ℝ)+1))
  let U := fun N k : ℕ => (k : ℝ)^g * (M (N*(k/(s*(N+1)))) +
    affineStep s (powerCutoff N)^((s*(N+1))*(k/(s*(N+1)))))
  have hU (N : ℕ) (hN : 0 < N) : Tendsto (U N) atTop (𝓝 (A/(cN N)^g)) := by
    have hb : 0 < s*(N+1) := by positivity
    have hm : Tendsto (fun k : ℕ => N*(k/(s*(N+1)))) atTop atTop :=
      Tendsto.const_mul_atTop' hN (Nat.tendsto_div_const_atTop hb.ne')
    have hmratio : Tendsto (fun k : ℕ => ((N*(k/(s*(N+1))) : ℕ) : ℝ)/(k : ℝ))
        atTop (𝓝 (cN N)) := by
      have h := (nat_div_ratio_limit (s*(N+1)) hb).const_mul (N : ℝ)
      simpa only [cN, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_one_div, mul_div_assoc] using h
    have hcN : cN N ≠ 0 := by dsimp [cN]; positivity
    have hmain := power_moment_reindex_limit g M A (cN N) hM _ hm hmratio hcN
    have htail := geometric_floor_tail_limit g (s*(N+1)) hb (affineStep s (powerCutoff N))
      (affineStep_bounds s hs _ (powerCutoff_bounds N).1.le (powerCutoff_bounds N).2.le).1
      (affineStep_cutoff_lt_one s N hs)
    simpa only [U, mul_add, add_zero] using hmain.add htail
  have hcn : Tendsto cN atTop (𝓝 c) := by
    have h := (tendsto_natCast_div_add_atTop (1 : ℝ)).div_const (s : ℝ)
    convert h using 1 <;> dsimp [cN, c] <;> field_simp <;> ring
  have hB := (tendsto_const_nhds (x := A)).div (hcn.pow g) (pow_ne_zero _ hc)
  have h := tendsto_of_parameter_squeeze
    (fun k : ℕ => (k : ℝ)^g*haarOverlapMoment (t+s) s k (by omega))
    (fun k : ℕ => (k : ℝ)^g*M (ell k)) U (A/c^g) (fun N => A/(cN N)^g) hL hU hB
    (fun k => mul_le_mul_of_nonneg_left (haarOverlapMoment_lower (t+s) s k hs (by omega))
      (pow_nonneg (Nat.cast_nonneg k) _))
    (fun N hN k => mul_le_mul_of_nonneg_left (haarOverlapMoment_upper (t+s) s N k hs (by omega) hN)
      (pow_nonneg (Nat.cast_nonneg k) _))
  have he : A/c^g = (s : ℝ)^g*A := by dsimp [c]; simp [div_pow, div_eq_mul_inv, mul_comm]
  rwa [he] at h

end
end ExtractionSchur
