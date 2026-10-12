import CofactorExtremaUpper
import Mathlib.Analysis.Complex.Basic

/-! Positive definite correlation matrices approximate the actual PSD Rayleigh ratios.
No rank constraint is asserted after perturbation. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder Topology
open Filter
namespace CofactorSpectral
noncomputable section

def positiveDefinitePerturbation {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (1+t)⁻¹ • (A+t • (1 : Matrix (Fin N) (Fin N) ℂ))

theorem positiveDefinitePerturbation_zero {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    positiveDefinitePerturbation A 0 = A := by simp [positiveDefinitePerturbation]

theorem positiveDefinitePerturbation_posDef {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : A.PosSemidef) (t : ℝ) (ht : 0 < t) :
    (positiveDefinitePerturbation A t).PosDef := by
  have hI : (t • (1 : Matrix (Fin N) (Fin N) ℂ)).PosDef := Matrix.PosDef.one.smul ht
  exact (Matrix.PosDef.posSemidef_add hA hI).smul (inv_pos.mpr (by linarith : 0 < 1+t))

theorem positiveDefinitePerturbation_diagonal {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : ∀ i, A i i = 1) (t : ℝ) (ht : 0 < t) :
    ∀ i, positiveDefinitePerturbation A t i i = 1 := by
  intro i
  simp only [positiveDefinitePerturbation,Matrix.smul_apply,Matrix.add_apply,Matrix.one_apply_eq,hA,
    Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_add,Complex.ofReal_one,mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast (show (1+t : ℝ) ≠ 0 by linarith))

theorem continuous_permanent_matrix (N : ℕ) :
    Continuous (fun A : Matrix (Fin N) (Fin N) ℂ => A.permanent) := by
  unfold Matrix.permanent
  fun_prop

theorem continuous_compound_entry (N : ℕ) (i j : Fin N) :
    Continuous (fun A : Matrix (Fin N) (Fin N) ℂ => compound A i j) := by
  unfold compound firstCofactor BapatFischer.mixedPermanent
  fun_prop

theorem continuousAt_cofactorRayleighRatio {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (w : Fin N → ℂ) (hP : 0 < A.permanent.re) (hw : 0 < vectorNormSq w) :
    ContinuousAt (fun B : Matrix (Fin N) (Fin N) ℂ => cofactorRayleighRatio B w) A := by
  unfold cofactorRayleighRatio
  apply ContinuousAt.div
  · apply Complex.continuous_re.continuousAt.comp
    apply Continuous.continuousAt
    apply continuous_finsetSum
    intro i hi
    apply continuous_finsetSum
    intro j hj
    exact (continuous_const.mul (continuous_compound_entry N i j)).mul continuous_const
  · exact (Complex.continuous_re.comp (continuous_permanent_matrix N)).continuousAt.mul continuousAt_const
  · exact (mul_pos hP hw).ne'

theorem continuousAt_positiveDefinitePerturbation {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    ContinuousAt (positiveDefinitePerturbation A) 0 := by
  unfold positiveDefinitePerturbation
  have hi : ContinuousAt (fun t : ℝ => (1+t)⁻¹) 0 := by
    apply ContinuousAt.inv₀
    · fun_prop
    · norm_num
  have hb : ContinuousAt (fun t : ℝ => A+t • (1 : Matrix (Fin N) (Fin N) ℂ)) 0 := by fun_prop
  convert hi.smul hb using 1

theorem exists_pd_correlation_above_ratio {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ)
    (hA : psdAdmissible A) (hdiag : ∀ i, A i i = 1) (w : Fin N → ℂ)
    (hw : 0 < vectorNormSq w) (c : ℝ) (hc : c < cofactorRayleighRatio A w) :
    ∃ B : Matrix (Fin N) (Fin N) ℂ, pdCorrelationAdmissible B ∧ c < cofactorRayleighRatio B w := by
  have hpert := continuousAt_positiveDefinitePerturbation A
  have hper : Tendsto (fun t : ℝ => (positiveDefinitePerturbation A t).permanent.re)
      (𝓝[>] 0) (𝓝 A.permanent.re) := by
    have h := ((Complex.continuous_re.comp (continuous_permanent_matrix N)).continuousAt.comp hpert).tendsto
    simpa only [Function.comp_def,positiveDefinitePerturbation_zero] using tendsto_nhdsWithin_of_tendsto_nhds h
  have hratio : Tendsto (fun t : ℝ => cofactorRayleighRatio (positiveDefinitePerturbation A t) w)
      (𝓝[>] 0) (𝓝 (cofactorRayleighRatio A w)) := by
    have ha : ContinuousAt (fun B : Matrix (Fin N) (Fin N) ℂ => cofactorRayleighRatio B w)
        (positiveDefinitePerturbation A 0) := by
      rw [positiveDefinitePerturbation_zero]
      exact continuousAt_cofactorRayleighRatio A w hA.2 hw
    have h := (ha.comp hpert).tendsto
    simpa only [Function.comp_def,positiveDefinitePerturbation_zero] using tendsto_nhdsWithin_of_tendsto_nhds h
  have hp := hper.eventually (eventually_gt_nhds hA.2)
  have hr := hratio.eventually (eventually_gt_nhds hc)
  have ht : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  obtain ⟨t,ht,hp,hr⟩ := Filter.Eventually.exists (Filter.Eventually.and ht (Filter.Eventually.and hp hr))
  exact ⟨positiveDefinitePerturbation A t,
    ⟨positiveDefinitePerturbation_posDef A hA.1 t ht,hp,positiveDefinitePerturbation_diagonal A hdiag t ht⟩,hr⟩

end
end CofactorSpectral
