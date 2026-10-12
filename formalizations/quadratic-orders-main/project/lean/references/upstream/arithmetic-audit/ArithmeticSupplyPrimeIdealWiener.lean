import PrimeNumberTheoremAnd.Wiener
import Entry002.PrimeIdealNaturalPNTBridge

/-! A conditional Wiener--Ikehara application to the genuine number-field
coefficients. Every elementary input is proved. The continuous boundary
function and its equality to the pole-subtracted true L-series are explicit
premises, not an axiom or a claimed analytic construction. The original
universal PNT premise and MainTarget remain unchanged and open. -/

set_option autoImplicit false
open Filter
open scoped NumberField Topology Classical

namespace Entry002

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

theorem primeIdeal_wiener_chebyshev :
    ∃ C : ℝ, ∀ n : ℕ,
      cumsum (fun k : ℕ => ‖(primeIdealVonMangoldt K k : ℂ)‖) n ≤ C * n := by
  obtain ⟨C, hC⟩ := vonMangoldt_cheby
  refine ⟨(Module.finrank ℚ K : ℝ) * C, fun n => ?_⟩
  calc
    _ ≤ (Module.finrank ℚ K : ℝ) *
        cumsum (fun k : ℕ => ‖(ArithmeticFunction.vonMangoldt k : ℂ)‖) n := by
      unfold cumsum
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro k _
      simpa only [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (primeIdealVonMangoldt_nonneg K k),
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using
        primeIdealVonMangoldt_le_degree_mul K k
    _ ≤ (Module.finrank ℚ K : ℝ) * (C * n) :=
      mul_le_mul_of_nonneg_left (hC n) (by positivity)
    _ = _ := by ring

theorem primeIdeal_wiener_norm_summable (s : ℝ) (hs : 1 < s) :
    Summable (nterm (fun n => (primeIdealVonMangoldt K n : ℂ)) s) := by
  simpa only [← nterm_eq_norm_term] using
    (primeIdealLSeriesSummable K (s := (s : ℂ)) (by simpa using hs)).norm

theorem primeIdealPsi_nat_eq_cumsum_add (n : ℕ) :
    primeIdealPsi K n = cumsum (primeIdealVonMangoldt K) n + primeIdealVonMangoldt K n := by
  unfold primeIdealPsi
  rw [Nat.floor_natCast]
  have hsum : (∑ k ∈ Finset.Ioc 0 n, primeIdealVonMangoldt K k) =
      ∑ k ∈ Finset.Icc 0 n, primeIdealVonMangoldt K k := by
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Ioc, Finset.mem_Icc] at hk ⊢
      omega
    · intro k hk hknot
      have hkzero : k = 0 := by
        simp only [Finset.mem_Ioc, Finset.mem_Icc] at hk hknot
        omega
      subst k
      exact primeIdealVonMangoldt_eq_zero_of_lt_two K 0 (by omega)
  rw [hsum, ← Nat.range_succ_eq_Icc_zero, Finset.sum_range_succ]
  rfl

theorem primeIdeal_coefficient_div_nat_tendsto_zero :
    Tendsto (fun n : ℕ => primeIdealVonMangoldt K n / (n : ℝ)) atTop (nhds 0) := by
  apply squeeze_zero (g := fun n : ℕ =>
    (Module.finrank ℚ K : ℝ) * Real.log (n : ℝ) / (n : ℝ))
  · intro n
    exact div_nonneg (primeIdealVonMangoldt_nonneg K n) (Nat.cast_nonneg _)
  · intro n
    exact div_le_div_of_nonneg_right ((primeIdealVonMangoldt_le_degree_mul K n).trans
      (mul_le_mul_of_nonneg_left ArithmeticFunction.vonMangoldt_le_log (by positivity))
      ) (Nat.cast_nonneg _)
  · have h := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_natCast_atTop_atTop).const_mul (Module.finrank ℚ K : ℝ)
    simpa only [mul_zero, Function.comp_def, id_eq, ← mul_div_assoc] using h

/-- Actual weighted PNT follows from the displayed analytic boundary
premises. No coefficient, convergence, or Chebyshev premise remains. -/
theorem primeIdeal_psi_asymptotic_of_wiener_boundary (G : ℂ → ℂ)
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s : ℂ =>
      LSeries (fun n => (primeIdealVonMangoldt K n : ℂ)) s - 1 / (s - 1))
      {s : ℂ | 1 < s.re}) :
    Tendsto (fun x : ℝ => primeIdealPsi K x / x) atTop (nhds 1) := by
  have hcum : Tendsto (fun n : ℕ => cumsum (primeIdealVonMangoldt K) n / (n : ℝ))
      atTop (nhds 1) := WienerIkeharaTheorem'
    (primeIdealVonMangoldt_nonneg K) (primeIdeal_wiener_norm_summable K)
    (primeIdeal_wiener_chebyshev K) hG hG'
  have hnat := hcum.add (primeIdeal_coefficient_div_nat_tendsto_zero K)
  have hnat' : Tendsto (fun n : ℕ => primeIdealPsi K n / (n : ℝ)) atTop (nhds 1) := by
    simpa only [primeIdealPsi_nat_eq_cumsum_add, add_div, add_zero] using hnat
  have h := (hnat'.comp tendsto_nat_floor_atTop).mul
    (tendsto_nat_floor_div_atTop :
      Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ) / x) atTop (nhds 1))
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hf : (⌊x⌋₊ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.floor_pos.mpr hx).ne'
  have hpsi : primeIdealPsi K (⌊x⌋₊ : ℝ) = primeIdealPsi K x := by
    simp [primeIdealPsi]
  dsimp only [Function.comp_def]
  rw [hpsi]
  field_simp

/-- Literal natural counting PNT follows from the same explicit boundary
premises through the proved weighted/unweighted bridge. The boundary is open. -/
theorem primeIdealNaturalPNT_of_wiener_boundary (G : ℂ → ℂ)
    (hG : ContinuousOn G {s : ℂ | 1 ≤ s.re})
    (hG' : Set.EqOn G (fun s : ℂ =>
      LSeries (fun n => (primeIdealVonMangoldt K n : ℂ)) s - 1 / (s - 1))
      {s : ℂ | 1 < s.re}) : PrimeIdealNaturalPNT K :=
  primeIdealNaturalPNT_of_psi K (primeIdeal_psi_asymptotic_of_wiener_boundary K G hG hG')

end

end Entry002
