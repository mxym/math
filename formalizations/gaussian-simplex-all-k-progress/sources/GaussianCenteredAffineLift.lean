import GaussianPositiveAffineLift
import GaussianCenteredCovarianceBlock

/-! Every centered affine covariance path with a positive principal block
has an actual differentiable minimal-dimensional simplicial score lift. -/
open MeasureTheory ProbabilityTheory Set Module Matrix Filter
open scoped RealInnerProductSpace Topology
namespace GaussianMeasureBridge
variable {d : ℕ}

theorem centered_affine_covariance_score_lift
    (Q D : Matrix (Fin (d+2)) (Fin (d+2)) ℝ)
    (hQ : Q.IsHermitian) (hD : D.IsHermitian)
    (hzQ : ∀ i, (∑ j,Q i j) = 0) (hzD : ∀ i, (∑ j,D i j) = 0)
    (hp : (principalCovariance Q).PosDef) :
    ∃ v : ℝ → Fin (d+2) → Space (d+1), ∃ h : Fin (d+2) → Space (d+1),
      HasDerivAt v h 0 ∧ AffineIndependent ℝ (v 0) ∧ scoreGram (v 0) = Q ∧
      (fun t : ℝ => scoreGram (v t)) =ᶠ[𝓝 (0:ℝ)] (fun t : ℝ => Q+t•D) := by
  obtain ⟨r,h,hd,hr,hg,ht⟩ := positive_covariance_affine_score_lift
    (principalCovariance Q) (principalCovariance D) hp (hD.submatrix Fin.succ)
  let v : ℝ → Fin (d+2) → Space (d+1) := fun t => centeredRowFamily (r t)
  have hcenter (t : ℝ) (i : Fin (d+2)) : (∑ j,(Q+t•D) i j) = 0 := by
    simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Finset.sum_add_distrib,
      ← Finset.mul_sum,hzQ,hzD,mul_zero,add_zero]
  have hherm (t : ℝ) : (Q+t•D).IsHermitian := hQ.add (hD.smul (by simp [IsSelfAdjoint]))
  have hv0 : scoreGram (v 0) = Q := by
    apply centered_covariance_ext _ _ (scoreGram_posSemidef _).isHermitian hQ
      (centeredRowFamily_gram_centered _) hzQ
    rw [centeredRowFamily_gram_principal,hg]
  refine ⟨v,centeredRowFamily h,centeredRowFamily_path_hasDerivAt r h 0 hd,
    centeredRowFamily_affineIndependent _ hr,hv0,?_⟩
  filter_upwards [ht] with t hgt
  apply centered_covariance_ext _ _ (scoreGram_posSemidef _).isHermitian (hherm t)
    (centeredRowFamily_gram_centered _) (hcenter t)
  rw [centeredRowFamily_gram_principal,hgt]
  ext i j
  rfl

end GaussianMeasureBridge
