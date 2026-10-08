import GaussianTwoCellBVBridge
import GaussianTailCalculus
import GaussianRegularPerimeter

/-! Unconditional two-label instance of the sharp simplicial Gaussian
perimeter comparison. No unproved isoperimetric hypothesis is introduced.

For two affine scores, winning cells are halfspaces. Their actual Gaussian
mass determines the boundary offset uniquely because the one-dimensional
Gaussian tail is strictly decreasing. Hence equal-mass two-score clusters
have exactly the same intrinsic perimeter, in any positive ambient
dimension. The exact sharp constant is identified with the already proved
regular model value.
-/
open MeasureTheory ProbabilityTheory Set Module Matrix
open scoped Topology RealInnerProductSpace

namespace GaussianMeasureBridge

theorem standardTail_strictAnti : StrictAnti standardTail := by
  apply strictAnti_of_deriv_neg
  intro a
  rw [(standardTail_hasDerivAt a).deriv]
  exact neg_lt_zero.mpr (standardDensity_pos a)

/-- Two injective two-score families with the same winning probabilities have
equal intrinsic Gaussian boundary perimeter for each corresponding label.
The proof works in every positive ambient dimension. -/
theorem two_winning_cell_inner_perimeter_eq_of_mass
    {d : ℕ} (v w : Fin 2 → Space (d+1)) (b c : Fin 2 → ℝ)
    (hv : Function.Injective v) (hw : Function.Injective w)
    (hmass : ∀ i, (gaussian (d+1)).real (winningCell v b i) =
        (gaussian (d+1)).real (winningCell w c i))
    (i : Fin 2) :
    gaussianInnerPerimeter (winningCell v b i) =
        gaussianInnerPerimeter (winningCell w c i) := by
  let p : Equiv.Perm (Fin 2) := Equiv.swap 0 i
  obtain ⟨u, a, hu, hSu⟩ :=
    two_winning_cell_zero_halfspace (v ∘ p) (b ∘ p) (hv.comp p.injective)
  obtain ⟨z, t, hz, hSz⟩ :=
    two_winning_cell_zero_halfspace (w ∘ p) (c ∘ p) (hw.comp p.injective)
  rw [winningCell_reindex] at hSu hSz
  have hVu : winningCell v b i = {x | a < ⟪u,x⟫} := by
    simpa only [p, Equiv.swap_apply_left] using hSu
  have hWz : winningCell w c i = {x | t < ⟪z,x⟫} := by
    simpa only [p, Equiv.swap_apply_left] using hSz
  have hm := hmass i
  rw [hVu, hWz, gaussian_unit_halfspace_mass u hu a,
    gaussian_unit_halfspace_mass z hz t] at hm
  have hat : a = t := standardTail_strictAnti.injective hm
  rw [hVu, hWz, gaussianInnerPerimeter_unit_halfspace u hu a,
    gaussianInnerPerimeter_unit_halfspace z hz t, hat]

/-- The sharp simplicial Gaussian perimeter comparison is unconditional for
d=0 (two cells in the one-dimensional minimal realization). This discharges
the exact EqualMassSimplicialPerimeterBound 0, not a weaker proxy. -/
theorem equal_mass_simplicial_perimeter_bound_zero :
    EqualMassSimplicialPerimeterBound 0 := by
  intro v hv
  let r : Fin 2 → Space 1 := minimalCovarianceRows (regularCovariance 2)
  have hR : NormalizedCovariance (regularCovariance 2) :=
    regularCovariance_normalized (k := 2) (by omega)
  have hr : AffineIndependent ℝ r :=
    minimalCovarianceRows_affineIndependent _ regular_principal_posDef
  have hz : (∑ i, r i) = 0 := minimalCovarianceRows_sum _
  have hg : scoreGram r = regularCovariance 2 :=
    scoreGram_minimalCovarianceRows _ hR.1 hR.2.1
  have hmv (i : Fin 2) :
      (gaussian 1).real (winningCell v (canonicalPrices v) i) = uniformMass 2 i :=
    canonicalPrices_balanced v hv.injective i
  have hmr (i : Fin 2) :
      (gaussian 1).real (winningCell r (canonicalPrices r) i) = uniformMass 2 i :=
    canonicalPrices_balanced r hr.injective i
  have hi (i : Fin 2) :
      gaussianInnerPerimeter (winningCell v (canonicalPrices v) i) =
        gaussianInnerPerimeter (winningCell r (canonicalPrices r) i) :=
    two_winning_cell_inner_perimeter_eq_of_mass v r
      (canonicalPrices v) (canonicalPrices r) hv.injective hr.injective
      (fun j => (hmv j).trans (hmr j).symm) i
  have hsum :
      (∑ i, gaussianInnerPerimeter (winningCell v (canonicalPrices v) i)) =
        ∑ i, gaussianInnerPerimeter (winningCell r (canonicalPrices r) i) :=
    Finset.sum_congr rfl (fun i _ => hi i)
  rw [hsum]
  exact le_of_eq
    (regular_intrinsic_cluster_perimeter_squared (d := 0) r hr hz hg).symm

#print axioms standardTail_strictAnti
#print axioms two_winning_cell_inner_perimeter_eq_of_mass
#print axioms equal_mass_simplicial_perimeter_bound_zero

end GaussianMeasureBridge
