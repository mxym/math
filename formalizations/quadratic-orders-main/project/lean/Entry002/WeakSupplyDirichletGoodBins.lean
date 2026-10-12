import Entry002.WeakSupplyDirichletCutoff

/-! Positive upper Dirichlet supply yields the actual cofinal logarithmic
mass of fixed-density good dyadic prime bins. -/

namespace Entry002

open scoped BigOperators Classical

/-- The upper-density bridge for actual rational primes. Its conclusion is
cofinal logarithmic good-bin mass, with one fixed positive local threshold. -/
theorem positiveUpperLogGoodBinSupply_of_positiveUpperDirichletSupply
    (P : Set ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hD : PositiveUpperDirichletSupply P) : PositiveUpperLogGoodBinSupply P := by
  obtain ⟨d, hd, hD⟩ := hD
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let δ : ℝ := d * Real.log 2 / 4
  let β : ℝ := d / 64
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hβ : 0 < β := by dsimp [β]; positivity
  refine ⟨δ, hδ, β, hβ, ?_⟩
  intro J₀
  let M : ℕ := max J₀ 2
  let T : ℝ := 256 / d + 4
  let η : ℝ := min (1 / ((M : ℝ) + 1)) (Real.exp (-T))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨ε, hε, hεlt, hlo⟩ := hD η hη
  have hεhi : ε < 1 / 2 := hεlt.trans_le (min_le_right _ _)
  have hεη : ε < η := hεlt.trans_le (min_le_left _ _)
  have hεM : ε < 1 / ((M : ℝ) + 1) := hεη.trans_le (min_le_left _ _)
  have hεT : ε < Real.exp (-T) := hεη.trans_le (min_le_right _ _)
  let J : ℕ := ⌈1 / ε⌉₊
  have hceil : 1 / ε ≤ (J : ℝ) := Nat.le_ceil _
  have hinv : (M : ℝ) + 1 < 1 / ε := by
    apply (lt_div_iff₀ hε).mpr
    have hh := (lt_div_iff₀ (by positivity : (0 : ℝ) < (M : ℝ) + 1)).mp hεM
    nlinarith only [hh]
  have hMJ : M ≤ J := by
    have hh : (M : ℝ) ≤ (J : ℝ) := by linarith only [hinv, hceil]
    exact_mod_cast hh
  have hJ : 2 ≤ J := (le_max_right J₀ 2).trans hMJ
  have hcut : 1 ≤ ε * ((J : ℝ) + 1) := by
    have hh := mul_le_mul_of_nonneg_left hceil hε.le
    have he : ε * (1 / ε) = 1 := by field_simp
    rw [he] at hh
    nlinarith only [hh, hε]
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (by omega : 0 < J)
  have hJupper : (J : ℝ) ≤ 2 / ε := by
    have hh : (J : ℝ) < 1 / ε + 1 := Nat.ceil_lt_add_one (by positivity)
    have hinvone : (1 : ℝ) ≤ 1 / ε := by
      apply (le_div_iff₀ hε).mpr
      linarith only [hεhi]
    have he : (2 : ℝ) / ε = 2 * (1 / ε) := by ring
    rw [he]
    linarith only [hh, hinvone]
  have hloginv : Real.log (1 / ε) = -Real.log ε := by
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hε.ne', Real.log_one, zero_sub]
  have hlogJ : Real.log (J : ℝ) ≤ Real.log (1 / ε) + 1 := by
    have hh := Real.log_le_log hJpos hJupper
    rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hε.ne'] at hh
    rw [hloginv]
    linarith only [hh, weakSupply_log_two_bounds.2]
  have hlarge : 256 + 4 * d ≤ d * Real.log (1 / ε) := by
    have hh := Real.log_lt_log hε hεT
    rw [Real.log_exp] at hh
    have hT : T ≤ Real.log (1 / ε) := by rw [hloginv]; linarith only [hh]
    have hmul := mul_le_mul_of_nonneg_left hT hd.le
    dsimp [T] at hmul
    have he : d * (256 / d + 4) = 256 + 4 * d := by field_simp
    rwa [he] at hmul
  have hδratio : δ / Real.log 2 = d / 4 := by dsimp [δ]; field_simp
  have hu := supplyPrimeDirichletSeries_le_good_bin_cutoff P hP δ hδ.le
    hε hεhi J hJ hcut
  rw [hδratio] at hu
  have hlogscaled := mul_le_mul_of_nonneg_left hlogJ hd.le
  refine ⟨J, hMJ, ?_⟩
  dsimp [β]
  nlinarith only [hlo, hu, hlogscaled, hlarge, hd]

end Entry002
