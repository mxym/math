import GaussianFluxCalibration
import GaussianJunctionBalanceGlobal

/-!
# Rigidity of a saturated Gaussian simplex flux calibration

For full equal-mass winning simplex clusters with strictly positive actual
facet weights, equality in the unit-diameter Lipschitz calibration forces
each label-vector difference to coincide with the corresponding unit facet
normal. Triple junction normal-balance then yields a regular Gram matrix
under centering and trace-one normalization.

This is conditional on *calibration equality*, not on the unproved sharp
multi-bubble perimeter bound, and does not assert existence of a saturating
calibration for arbitrary equal-mass Gaussian clusters.
-/

open MeasureTheory ProbabilityTheory Module Set Matrix
open scoped RealInnerProductSpace

namespace GaussianMeasureBridge

variable {d e : ℕ}

/-- A norm-at-most-one vector which saturates the inner product with a
nonzero vector is the corresponding unit normal. -/
theorem unit_normal_of_inner_saturation (a b : Space e)
    (hb : b ≠ 0) (ha : ‖a‖ ≤ 1) (he : ⟪a,b⟫ = ‖b‖) :
    a = ‖b‖⁻¹ • b := by
  have hp : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hcs := real_inner_le_norm a b
  rw [he] at hcs
  have ha1 : 1 ≤ ‖a‖ := by
    have hh : ‖b‖ / ‖b‖ ≤ ‖a‖ := (div_le_iff₀ hp).mpr (by simpa using hcs)
    simpa [div_self hp.ne'] using hh
  have hnorm : ‖a‖ = 1 := le_antisymm ha ha1
  have hcs_eq : ⟪a,b⟫ = ‖a‖*‖b‖ := by
    simpa only [hnorm, one_mul] using he
  have hvec : ‖b‖ • a = ‖a‖ • b :=
    (inner_eq_norm_mul_iff_real).mp hcs_eq
  rw [hnorm,one_smul] at hvec
  calc
    a = ‖b‖⁻¹ • (‖b‖ • a) := by
      rw [smul_smul, inv_mul_cancel₀ hp.ne',one_smul]
    _ = ‖b‖⁻¹ • b := by rw [hvec]

/-- At equality in the actual intrinsic-perimeter flux calibration, each
nonzero oriented edge difference has exactly its unit-normal direction. -/
theorem actual_simplicial_saturated_flux_unit_edges
    (v : Fin (d+2) → Space (d+1)) (hv : AffineIndependent ℝ v)
    (q : Fin (d+2) → Space (d+1))
    (hq : ∀ i j, ‖q i-q j‖ ≤ 1)
    (heq : (∑ i,⟪q i,balancedMoment v i⟫) =
      (∑ i,gaussianInnerPerimeter (winningCell v (canonicalPrices v) i))/2) :
    ∀ i j, i ≠ j →
      q i-q j = ‖v i-v j‖⁻¹ • (v i-v j) := by
  obtain ⟨w,h0,hp,hs,hf,_⟩ := actual_balanced_flux_energy v hv
  have hw (i j : Fin (d+2)) : 0 ≤ w i j := by
    by_cases hij : i=j
    · subst j
      rw [h0 i]
    · exact (hp i j hij).le
  have hraw (i : Fin (d+2)) :
      rawWinningMoment v (canonicalPrices v) i = ∑ j,w i j • (v i-v j) := hf i
  have heqf := heq
  rw [actual_simplicial_cluster_inner_perimeter v _ hv w hraw] at heqf
  intro i j hij
  have hinner := symmetric_flux_calibration_equality_edges v q (balancedMoment v)
    w hw hp hs hf hq heqf i j hij
  have hne : v i-v j ≠ 0 := by
    intro hz
    exact hij (hv.injective (sub_eq_zero.mp hz))
  exact unit_normal_of_inner_saturation (q i-q j) (v i-v j)
    hne (hq i j) hinner

/-- Saturation by a common set of calibrated label vectors forces all
actual oriented triple unit normals to balance. -/
theorem actual_simplicial_saturated_triple_normal_balance
    (v : Fin (d+2) → Space (d+1)) (hv : AffineIndependent ℝ v)
    (q : Fin (d+2) → Space (d+1))
    (hq : ∀ i j, ‖q i-q j‖ ≤ 1)
    (heq : (∑ i,⟪q i,balancedMoment v i⟫) =
      (∑ i,gaussianInnerPerimeter (winningCell v (canonicalPrices v) i))/2) :
    ∀ i j l : Fin (d+2), i ≠ j → j ≠ l → l ≠ i →
      ‖v i-v j‖⁻¹ • (v i-v j) +
      ‖v j-v l‖⁻¹ • (v j-v l) +
      ‖v l-v i‖⁻¹ • (v l-v i) = 0 := by
  have hunit := actual_simplicial_saturated_flux_unit_edges v hv q hq heq
  intro i j l hij hjl hli
  have hc : (q i-q j)+(q j-q l)+(q l-q i)=0 := by abel
  rw [hunit i j hij,hunit j l hjl,hunit l i hli] at hc
  exact hc

/-- In the k >= 3 regime, a centered trace-one full simplex whose *actual*
balanced winning cluster saturates one unit-diameter calibration must be
regular. The perimeter lower bound itself is not assumed or proved. -/
theorem regular_gram_of_saturated_simplicial_calibration
    (d : ℕ) (hd : 1 ≤ d)
    (v : Fin (d+2) → Space (d+1)) (hv : AffineIndependent ℝ v)
    (hz : ∑ i,v i = 0) (ht : ∑ i,‖v i‖^2 = 1)
    (q : Fin (d+2) → Space (d+1))
    (hq : ∀ i j, ‖q i-q j‖ ≤ 1)
    (heq : (∑ i,⟪q i,balancedMoment v i⟫) =
      (∑ i,gaussianInnerPerimeter (winningCell v (canonicalPrices v) i))/2) :
    scoreGram v = regularCovariance (d+2) := by
  cases d with
  | zero => omega
  | succ d =>
    exact all_triple_balances_regular_gram v hv hz ht
      (actual_simplicial_saturated_triple_normal_balance v hv q hq heq)

#print axioms unit_normal_of_inner_saturation
#print axioms actual_simplicial_saturated_flux_unit_edges
#print axioms actual_simplicial_saturated_triple_normal_balance
#print axioms regular_gram_of_saturated_simplicial_calibration

end GaussianMeasureBridge
