import SchurCompletion.HaarMinorMoments
import SchurCompletion.CodimensionOneRank
import SchurCompletion.WeylCrossRatio
import Mathlib.Data.Nat.Factorial.BigOperators

open scoped BigOperators Topology
open Matrix MeasureTheory Filter Asymptotics

namespace ExtractionSchur
open SymmetricSupport ExtractionSpectrum ExtractionRankSupport
noncomputable section

theorem choose_shift_div_pow_limit (i : ℕ) :
    Tendsto (fun k : ℕ => ((i+k).choose i : ℝ)/(k : ℝ)^i) atTop
      (𝓝 ((i.factorial : ℝ)⁻¹)) := by
  have h := symmetricProjector_rank_scaled_limit (i+1) (by omega)
  have hh (k : ℕ) : (symmetricProjector (i+1) k).rank = (i+k).choose i := by
    rw [symmetricProjector_rank_choose_complement (i+1) k (by omega)]
    congr 1 <;> omega
  simpa only [hh, Nat.add_sub_cancel, one_div] using h

theorem minor_moment_factor_scaled_limit (t i : ℕ) :
    Tendsto (fun k : ℕ => (k : ℝ)^t *
      (((i+k).choose k : ℝ)/((t+i+k).choose k : ℝ))) atTop
      (𝓝 (((t+i).factorial : ℝ)/(i.factorial : ℝ))) := by
  have h := (choose_shift_div_pow_limit i).div (choose_shift_div_pow_limit (t+i)) (by positivity)
  have hc : (i.factorial : ℝ)⁻¹ / ((t+i).factorial : ℝ)⁻¹ =
      ((t+i).factorial : ℝ)/(i.factorial : ℝ) := by simp [div_eq_mul_inv, mul_comm]
  rw [hc] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hden : ((t+i+k).choose (t+i) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (show t+i ≤ t+i+k by omega)
  simp only [Pi.div_apply]
  rw [← Nat.choose_symm_add (a := i) (b := k), ← Nat.choose_symm_add (a := t+i) (b := k)]
  rw [pow_add]
  field_simp

theorem haarMinorMoment_product_re (t s k : ℕ) :
    (haarMinorMoment (t+s) s k (by omega)).re =
      ∏ i ∈ Finset.range s, (((i+k).choose k : ℝ)/((t+i+k).choose k : ℝ)) := by
  rw [haarMinorMoment_product]
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_div, ← Complex.ofReal_prod,
    Complex.ofReal_re]

theorem weylCrossDenominator_eq_factorial_product (s t : ℕ) :
    weylCrossDenominator s t =
      ∏ i ∈ Finset.range s, (((t+i).factorial : ℝ)/(i.factorial : ℝ)) := by
  let e : Equiv.Perm (Fin s) := ⟨Fin.rev, Fin.rev, Fin.rev_rev, Fin.rev_rev⟩
  calc
    _ = ∏ i : Fin s, ∏ j : Fin t, (crossShift s t (Fin.rev i) j : ℝ) :=
      (Equiv.prod_comp e (fun i : Fin s => ∏ j : Fin t, (crossShift s t i j : ℝ))).symm
    _ = ∏ i : Fin s, (((t+i.val).factorial : ℝ)/(i.val.factorial : ℝ)) := by
      apply Finset.prod_congr rfl
      intro i hi
      have he (j : Fin t) : crossShift s t (Fin.rev i) j = i.val+1+j.val := by
        simp only [crossShift, Fin.val_rev]
        omega
      simp_rw [he]
      rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => ((i.val+1+j : ℕ) : ℝ)) t]
      have hn := Nat.factorial_mul_ascFactorial i.val t
      rw [Nat.ascFactorial_eq_prod_range] at hn
      have hf : (i.val.factorial : ℝ) ≠ 0 := by positivity
      apply (eq_div_iff hf).mpr
      have hR : (i.val.factorial : ℝ) *
          (∏ j ∈ Finset.range t, ((i.val+1+j : ℕ) : ℝ)) = ((i.val+t).factorial : ℝ) := by
        exact_mod_cast hn
      simpa only [Nat.add_comm, mul_comm] using hR
    _ = _ := Fin.prod_univ_eq_prod_range
      (fun i : ℕ => (((t+i).factorial : ℝ)/(i.factorial : ℝ))) s

/-- The actual all-rank principal-minor moment has exactly the cross-gap
polynomial constant needed for the manuscript's Haar purity. -/
theorem haarMinorMoment_scaled_limit (s t : ℕ) :
    Tendsto (fun k : ℕ => (k : ℝ)^(s*t) * (haarMinorMoment (t+s) s k (by omega)).re)
      atTop (𝓝 (weylCrossDenominator s t)) := by
  have h := tendsto_finsetProd (Finset.range s)
    (fun i hi => minor_moment_factor_scaled_limit t i)
  rw [← weylCrossDenominator_eq_factorial_product] at h
  apply h.congr'
  filter_upwards [] with k
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← pow_mul,
    Nat.mul_comm t s, haarMinorMoment_product_re]

end
end ExtractionSchur
