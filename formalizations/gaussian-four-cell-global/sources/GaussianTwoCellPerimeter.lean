import GaussianTwoCellBVBridge
import GaussianRegularPerimeter

/-! The simplicial perimeter comparison in dimension one is unconditional.
Balancing forces each of the two winning halfspaces to have zero offset, since
the actual Gaussian tail is strictly decreasing. -/
open MeasureTheory ProbabilityTheory Set Module Matrix
open scoped Topology ENNReal RealInnerProductSpace

namespace GaussianMeasureBridge

theorem balanced_two_cell_inner_perimeter
    (v : Fin 2 → Space 1) (hv : Function.Injective v) (i : Fin 2) :
    gaussianInnerPerimeter (winningCell v (canonicalPrices v) i) =
      standardDensity 0 := by
  let p : Equiv.Perm (Fin 2) := Equiv.swap 0 i
  obtain ⟨u,a,hu,hS⟩ :=
    two_winning_cell_zero_halfspace (v ∘ p) (canonicalPrices v ∘ p)
      (hv.comp p.injective)
  rw [winningCell_reindex] at hS
  simp only [p, Equiv.swap_apply_left] at hS
  have hmass : standardTail a = (1 : ℝ) / 2 := by
    rw [← gaussian_unit_halfspace_mass u hu a, ← hS]
    simpa [uniformMass] using canonicalPrices_balanced v hv i
  have ha : a = 0 := (standardTail_eq_half_iff a).mp hmass
  rw [hS, gaussianInnerPerimeter_unit_halfspace u hu a, ha]

theorem equalMassSimplicialPerimeterBound_zero :
    EqualMassSimplicialPerimeterBound 0 := by
  intro v hv
  let r : Fin 2 → Space 1 := minimalCovarianceRows (regularCovariance 2)
  have hR := regularCovariance_normalized (k := 2) (by omega)
  have hr : AffineIndependent ℝ r :=
    minimalCovarianceRows_affineIndependent _ regular_principal_posDef
  have hz : ∑ i, r i = 0 := minimalCovarianceRows_sum _
  have hg : scoreGram r = regularCovariance 2 :=
    scoreGram_minimalCovarianceRows _ hR.1 hR.2.1
  have hreg := regular_intrinsic_cluster_perimeter_squared r hr hz hg
  have hsame : (∑ i, gaussianInnerPerimeter
      (winningCell v (canonicalPrices v) i)) =
      (∑ i, gaussianInnerPerimeter
        (winningCell r (canonicalPrices r) i)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [balanced_two_cell_inner_perimeter v hv.injective i,
      balanced_two_cell_inner_perimeter r hr.injective i]
  have hh : simplexConstant 2 ^ 2 / 2 ≤
      ((∑ i, gaussianInnerPerimeter
        (winningCell v (canonicalPrices v) i)) / 2) ^ 2 := by
    rw [hsame]
    simpa using hreg.symm.le
  simpa using hh

end GaussianMeasureBridge
