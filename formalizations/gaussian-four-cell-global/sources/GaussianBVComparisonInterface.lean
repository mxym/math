import GaussianUnitHalfspacePerimeter
import GaussianPerimeterComparisonReduction

/-! The remaining geometric obligations are separated precisely: the genuine
Gaussian BV cluster lower bound, and only the needed direction of the
simplicial BV/erosion bridge. Neither obligation is asserted as a theorem.
Actual balanced winning cells are proved to satisfy the cluster interface. -/
open MeasureTheory ProbabilityTheory Set Module
open scoped Topology ENNReal RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

structure BalancedGaussianCluster (d k : ℕ) where
  cell : Fin k → Set (Space d)
  measurable : ∀ i,MeasurableSet (cell i)
  disjoint : ∀ i j,i ≠ j → Disjoint (cell i) (cell j)
  cover : ∀ᵐ x ∂gaussian d,∃ i,x ∈ cell i
  mass : ∀ i,(gaussian d).real (cell i) = uniformMass k i

noncomputable def BalancedGaussianCluster.perimeter (C : BalancedGaussianCluster d k) : ℝ≥0∞ :=
  (∑ i,gaussianBVPerimeter (C.cell i))/2

noncomputable def canonicalWinningCluster (v : Fin k → Space d) (hv : Function.Injective v) :
    BalancedGaussianCluster d k :=
  { cell := winningCell v (canonicalPrices v)
    measurable := measurableSet_winningCell _ _
    disjoint := fun i j hij => by
      apply Set.disjoint_left.mpr
      intro x hi hj
      have h1 := hi j (Ne.symm hij)
      have h2 := hj i hij
      linarith
    cover := ae_unique_winner v _ hv
    mass := canonicalPrices_balanced v hv }

/-- This natural Gaussian multi-bubble statement remains an explicit proof
obligation. Its constant is the actual iid-normal maximum normalization. -/
def GaussianBalancedBVLowerBound (d : ℕ) : Prop :=
  ∀ C : BalancedGaussianCluster (d+1) (d+2),
    ENNReal.ofReal (simplexConstant (d+2)*Real.sqrt ((d+1:ℕ)/2)) ≤ C.perimeter

/-- Only this direction of the BV bridge is necessary for the comparison
proof. The proposition is not yet proved for general simplicial cells. -/
def SimplicialBVUpperBound (d : ℕ) : Prop :=
  ∀ v : Fin (d+2) → Space (d+1),AffineIndependent ℝ v → ∀ i,
    gaussianBVPerimeter (winningCell v (canonicalPrices v) i) ≤
      ENNReal.ofReal (gaussianInnerPerimeter (winningCell v (canonicalPrices v) i))

lemma canonical_simplicial_inner_perimeter_nonneg
    (v : Fin (d+2) → Space (d+1)) (hv : AffineIndependent ℝ v) (i : Fin (d+2)) :
    0 ≤ gaussianInnerPerimeter (winningCell v (canonicalPrices v) i) := by
  obtain ⟨w,hw,hp,hs,hf,hc⟩ := actual_balanced_flux_energy v hv
  have hraw (j : Fin (d+2)) : rawWinningMoment v (canonicalPrices v) j =
      ∑ l,w j l • (v j-v l) := hf j
  rw [actual_simplicial_cell_inner_perimeter v _ hv w hraw]
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg _ (norm_nonneg _)
  by_cases hij : i=j
  · subst j; rw [hw i]
  · exact (hp i j hij).le

theorem perimeter_comparison_of_BV_interfaces
    (hBV : GaussianBalancedBVLowerBound d) (hbridge : SimplicialBVUpperBound d) :
    EqualMassSimplicialPerimeterBound d := by
  intro v hv
  let C := canonicalWinningCluster v hv.injective
  let S : ℝ := (∑ i,gaussianInnerPerimeter (winningCell v (canonicalPrices v) i))/2
  have hp (i : Fin (d+2)) := canonical_simplicial_inner_perimeter_nonneg v hv i
  have hS : 0 ≤ S := div_nonneg (Finset.sum_nonneg (fun i _ => hp i)) (by norm_num)
  have hupper : C.perimeter ≤ ENNReal.ofReal S := by
    change (∑ i,gaussianBVPerimeter (winningCell v (canonicalPrices v) i))/2 ≤
      ENNReal.ofReal ((∑ i,gaussianInnerPerimeter (winningCell v (canonicalPrices v) i))/2)
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0:ℝ)<2),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i)]
    simpa using ENNReal.div_le_div_right (Finset.sum_le_sum (fun i _ => hbridge v hv i)) (2 : ℝ≥0∞)
  have hl := (hBV C).trans hupper
  have hreal : simplexConstant (d+2)*Real.sqrt ((d+1:ℕ)/2) ≤ S :=
    (ENNReal.ofReal_le_ofReal_iff hS).mp hl
  have hn : 0 ≤ ((d+1:ℕ):ℝ)/2 := by positivity
  have hsqrt := Real.sq_sqrt hn
  have hc := simplexConstant_nonneg (k := d+2)
  have hsqrt0 := Real.sqrt_nonneg (((d+1:ℕ):ℝ)/2)
  have hsq : (simplexConstant (d+2)*Real.sqrt ((d+1:ℕ)/2))^2 ≤ S^2 := by
    exact (sq_le_sq₀ (mul_nonneg hc hsqrt0) hS).mpr hreal
  rw [mul_pow,hsqrt] at hsq
  dsimp only [S] at hsq
  nlinarith

end GaussianMeasureBridge
