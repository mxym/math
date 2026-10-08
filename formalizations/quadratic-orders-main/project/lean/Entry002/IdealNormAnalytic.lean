import Entry002.IdealNormCoefficient
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.Positivity

/-!
Analytic facts about the actual ideal-norm coefficients. The linear partial-sum
bound comes from the asymptotics for the number of nonzero integral ideals.
The pole statement is the proved real-axis right limit for mathlib's actual
Dedekind zeta function; it does not assert a complex meromorphic continuation.
-/

namespace Entry002

open NumberField Ideal Finset Filter Asymptotics nonZeroDivisors
open scoped NumberField Classical Topology ComplexOrder

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

/-- Counting norms from one through `n` counts exactly the nonzero ideals of
norm at most `n`. The raw coefficient at zero is left intact. -/
theorem idealNormCount_sum_Icc (n : ℕ) :
    ∑ k ∈ Icc 1 n, idealNormCount K k =
      Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) ≤ n} := by
  classical
  symm
  unfold idealNormCount
  rw [← add_left_inj 1, ← card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // absNorm I = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc (n.zero_le),
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ ↦ finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

/-- The actual ideal-count partial sums have the class-number residue as
their asymptotic slope. -/
theorem idealNormCoefficient_tendsto_sum_div :
    Tendsto (fun n : ℕ ↦ (∑ k ∈ Icc 1 n, idealNormCoefficient K k) / (n : ℝ))
      atTop (𝓝 (dedekindZeta_residue K)) := by
  change Tendsto _ atTop (𝓝
    ((2 ^ InfinitePlace.nrRealPlaces K * (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces K *
      Units.regulator K * classNumber K) /
      (Units.torsionOrder K * Real.sqrt |discr K|)))
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr
    fun n ↦ ?_
  simp only [Function.comp_apply, Nat.cast_le]
  rw [← idealNormCount_sum_Icc K n]
  simp [idealNormCoefficient, Nat.cast_sum]

/-- The partial sums of the genuine ideal-count coefficients grow at most
linearly. -/
theorem idealNormCoefficient_sum_isBigO :
    (fun n : ℕ ↦ ∑ k ∈ Icc 1 n, idealNormCoefficient K k) =O[atTop]
      (fun n ↦ (n : ℝ) ^ (1 : ℝ)) := by
  exact isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    (by simpa using idealNormCoefficient_tendsto_sum_div K)

/-- Absolute convergence for the actual Dedekind ideal coefficients. -/
theorem idealNormCoefficient_LSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (idealNormCoefficient K n : ℂ)) s := by
  exact LSeriesSummable_of_sum_norm_bigO_and_nonneg
    (idealNormCoefficient_sum_isBigO K)
    (fun n ↦ by simp [idealNormCoefficient]) zero_le_one hs

/-- The abscissa of absolute convergence is at most one. -/
theorem idealNormCoefficient_abscissaOfAbsConv_le_one :
    LSeries.abscissaOfAbsConv (fun n ↦ (idealNormCoefficient K n : ℂ)) ≤ (1 : ℝ) := by
  apply LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable
  intro y hy
  exact idealNormCoefficient_LSeriesSummable K (by simpa using hy)

/-- Mathlib's Dedekind zeta function is the L-series of these raw counts. -/
theorem dedekindZeta_eq_idealNormCoefficient_LSeries (s : ℂ) :
    dedekindZeta K s = LSeries (fun n ↦ (idealNormCoefficient K n : ℂ)) s := by
  simp [dedekindZeta, idealNormCoefficient, idealNormCount]

/-- The actual ideal-coefficient series is holomorphic on `Re(s) > 1`. -/
theorem idealNormCoefficient_LSeries_analyticOnNhd :
    AnalyticOnNhd ℂ (LSeries (fun n ↦ (idealNormCoefficient K n : ℂ)))
      {s : ℂ | 1 < s.re} := by
  apply (LSeries_analyticOnNhd _).mono
  intro s hs
  exact (idealNormCoefficient_abscissaOfAbsConv_le_one K).trans_lt (by exact_mod_cast hs)

/-- Holomorphy of mathlib's actual Dedekind zeta function in its convergent
half-plane. -/
theorem dedekindZeta_analyticOnNhd_re_gt_one :
    AnalyticOnNhd ℂ (dedekindZeta K) {s : ℂ | 1 < s.re} := by
  simpa only [funext (dedekindZeta_eq_idealNormCoefficient_LSeries K)] using
    idealNormCoefficient_LSeries_analyticOnNhd K

/-- On the real line to the right of one, the actual Dedekind zeta value
is a positive real number. -/
theorem actualDedekindZeta_pos_real {x : ℝ} (hx : 1 < x) :
    0 < dedekindZeta K (x : ℂ) := by
  rw [dedekindZeta_eq_idealNormCoefficient_LSeries K]
  apply LSeries.positive
  · intro n
    simp [idealNormCoefficient]
  · have h : idealNormCoefficient K 1 = 1 := by
      simp [idealNormCoefficient, idealNormCount, Ideal.absNorm_eq_one_iff]
    simp [h]
  · exact (idealNormCoefficient_abscissaOfAbsConv_le_one K).trans_lt
      (by exact_mod_cast hx)

/-- Real-axis nonvanishing follows from the positive actual coefficients. -/
theorem actualDedekindZeta_ne_zero_real {x : ℝ} (hx : 1 < x) :
    dedekindZeta K (x : ℂ) ≠ 0 :=
  (actualDedekindZeta_pos_real K hx).ne'

/-- The actual residue is strictly positive. -/
theorem actualDedekindZeta_residue_pos : 0 < dedekindZeta_residue K :=
  NumberField.dedekindZeta_residue_pos K

/-- The actual Dedekind zeta function has the proved positive real-axis
right-pole asymptotic at one. -/
theorem actualDedekindZeta_tendsto_sub_one_mul_nhdsGT :
    Tendsto (fun s : ℝ ↦ (s - 1) * dedekindZeta K s) (𝓝[>] 1)
      (𝓝 (dedekindZeta_residue K : ℂ)) :=
  NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K

/-- The same right-pole asymptotic in the explicit ideal-coefficient series. -/
theorem idealNormCoefficient_LSeries_tendsto_sub_one_mul_nhdsGT :
    Tendsto (fun s : ℝ ↦ (s - 1) * LSeries (fun n ↦ (idealNormCoefficient K n : ℂ)) s)
      (𝓝[>] 1) (𝓝 (dedekindZeta_residue K : ℂ)) := by
  simpa only [dedekindZeta_eq_idealNormCoefficient_LSeries K] using
    actualDedekindZeta_tendsto_sub_one_mul_nhdsGT K

/-- The positive real-axis pole excludes absolute convergence to the left
of one, so the actual ideal series has abscissa exactly one. -/
theorem idealNormCoefficient_abscissaOfAbsConv_eq_one :
    LSeries.abscissaOfAbsConv (fun n ↦ (idealNormCoefficient K n : ℂ)) = (1 : ℝ) := by
  apply le_antisymm (idealNormCoefficient_abscissaOfAbsConv_le_one K)
  by_contra h
  have habs : LSeries.abscissaOfAbsConv (fun n ↦ (idealNormCoefficient K n : ℂ)) <
      (1 : ℝ) := lt_of_not_ge h
  have hc : ContinuousAt (LSeries (fun n ↦ (idealNormCoefficient K n : ℂ))) (1 : ℂ) :=
    (LSeries_hasDerivAt (by simpa using habs)).continuousAt
  have hz : Tendsto
      (fun s : ℝ ↦ (s - 1) * LSeries (fun n ↦ (idealNormCoefficient K n : ℂ)) s)
      (𝓝[>] 1) (𝓝 (0 : ℂ)) := by
    have hp : ContinuousAt
        (fun s : ℝ ↦ (s - 1) * LSeries (fun n ↦ (idealNormCoefficient K n : ℂ)) s) 1 :=
      (Complex.continuous_ofReal.continuousAt.sub continuousAt_const).mul
        (hc.comp_of_eq (f := Complex.ofReal) (x := (1 : ℝ))
          Complex.continuous_ofReal.continuousAt (by simp))
    simpa using hp.tendsto.mono_left nhdsWithin_le_nhds
  exact (Complex.ofReal_ne_zero.mpr (actualDedekindZeta_residue_pos K).ne')
    (tendsto_nhds_unique hz (idealNormCoefficient_LSeries_tendsto_sub_one_mul_nhdsGT K)).symm

end

end Entry002
