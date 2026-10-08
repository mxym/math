import GaussianPerimeterComparisonReduction
import GaussianRadialEquality
import GaussianFacetRigidity

/-! Conditional rigidity with precisely the same explicit perimeter
obligation as the comparison reduction. Positivity of all actual facets
supplies the equality step; no perimeter uniqueness theorem is assumed. -/
open MeasureTheory ProbabilityTheory Module Matrix Set Filter
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d : ℕ}

theorem covariance_equality_regular_of_perimeter
    (hper : EqualMassSimplicialPerimeterBound d)
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ) (hQ : NormalizedCovariance Q)
    (he : covarianceValue Q = simplexConstant (d+2)) :
    Q = regularCovariance (d+2) := by
  let H : ℝ → ℝ := fun t => covarianceValue (covarianceSegment Q t)^2-simplexConstant (d+2)^2
  obtain ⟨h0,hd0,hd,hi,hend⟩ := covariance_squared_radial_data Q hQ
  have hD := covarianceRadialDeficit_nonneg_of_perimeter hper Q hQ
  have h1 : H 1 = 0 := by simp [H,covarianceSegment_one,he]
  obtain ⟨hH,hzD⟩ := GaussianRadialComparison.radial_equality_forces_zero_deficit
    H (deriv H) (covarianceRadialDeficit Q) h0 hd0 hd hi hD hend h1
  have ht : (1/2:ℝ) ∈ Ioo 0 1 := by norm_num
  obtain ⟨r,w,hr,hg,hw,hp,hs,hf,hder,hrad⟩ :=
    actual_covarianceSegment_radial_differential Q hQ (1/2) ht
  have hraw (i : Fin (d+2)) : rawWinningMoment r (canonicalPrices r) i =
      ∑ j,w i j • (r i-r j) := hf i
  have hl := hper r hr
  rw [actual_simplicial_cluster_inner_perimeter r _ hr w hraw] at hl
  have hn (i j : Fin (d+2)) : 0 ≤ w i j := by
    by_cases h : i=j
    · subst j; rw [hw i]
    · exact (hp i j h).le
  have hc : covarianceValue (covarianceSegment Q (1/2)) =
      (∑ i,∑ j,w i j*‖r i-r j‖^2)/2 := by
    rw [← hg,covarianceValue_scoreGram,← balancedMoment_value r hr.injective]
    exact symmetric_flux_energy _ _ w hs hf
  have hcs := actual_flux_cauchy r w hn
  rw [← hc] at hcs
  have hdef := hzD (1/2) ht
  rw [covarianceRadialDeficit,actual_radial_trace Q (1/2) _ _ hder hrad] at hdef
  have hneq : ((d+1:ℕ):ℝ) ≠ 0 := by positivity
  have hprod : covarianceValue (covarianceSegment Q (1/2))*fluxTrace w =
      (d+1:ℕ)*simplexConstant (d+2)^2 := by
    rw [mul_comm ((d+1:ℕ):ℝ)]
    apply (div_eq_iff hneq).mp
    linarith [hdef]
  have heq : (fluxPerimeter r w)^2 = fluxTrace w *
      ((∑ i,∑ j,w i j*‖r i-r j‖^2)/2)/2 := by
    rw [← hc]
    exact le_antisymm hcs (by nlinarith [hl,hprod])
  have hQt := covarianceSegment_normalized Q hQ ⟨ht.1.le,ht.2.le⟩
  have hz : ∑ i,r i = 0 := sum_rows_zero_of_gram_centered r (by simpa only [hg] using hQt.2.1)
  have htrace : (∑ i,‖r i‖^2) = 1 := by
    rw [← hQt.2.2,← hg]
    simp only [Matrix.trace,Matrix.diag,scoreGram,real_inner_self_eq_norm_sq]
  have hreg := flux_cauchy_equality_regular (by omega : 2 ≤ d+2) r w hw hp hz htrace heq
  rw [hg] at hreg
  ext i j
  have hij := congrFun (congrFun hreg i) j
  simp only [covarianceSegment,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul] at hij
  linarith

theorem covariance_strict_comparison_of_perimeter
    (hper : EqualMassSimplicialPerimeterBound d)
    (Q : Matrix (Fin (d+2)) (Fin (d+2)) ℝ) (hQ : NormalizedCovariance Q)
    (hneq : Q ≠ regularCovariance (d+2)) :
    covarianceValue Q < simplexConstant (d+2) := by
  apply lt_of_le_of_ne (covariance_comparison_of_perimeter hper Q hQ).1
  intro he
  exact hneq (covariance_equality_regular_of_perimeter hper Q hQ he)

theorem momentEnergy_bound_of_perimeter {e : ℕ}
    (hper : EqualMassSimplicialPerimeterBound d) (F : FractionalPartition e (d+2))
    (hF : ∀ i,F.mass i = uniformMass (d+2) i) :
    F.momentEnergy ≤ simplexConstant (d+2)^2 :=
  F.momentEnergy_bound_of_normalized_covariance_bound hF _ simplexConstant_nonneg
    (fun Q hQ => (covariance_comparison_of_perimeter hper Q hQ).1)

end GaussianMeasureBridge
