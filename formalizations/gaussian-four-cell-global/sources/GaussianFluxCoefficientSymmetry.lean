import GaussianNormalCoordinates
import GaussianRotationalMomentIdentity

/-! Symmetry of the true winning moments in normal-basis coordinates. The
proof uses Gaussian rotation invariance and Riesz dual vectors; it does not
assume a price Hessian or a symmetric flux matrix. -/
open MeasureTheory ProbabilityTheory Set Module
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d k : ℕ} [NeZero k]

theorem gaussian_score_moment_inner_symmetric (v : Fin k → Space d)
    (b : Fin k → ℝ) (hv : Function.Injective v) (x y : Space d) :
    (∑ i, ⟪v i,x⟫ * ⟪(winningPartition v b hv).moment i,y⟫) =
      ∑ i, ⟪v i,y⟫ * ⟪(winningPartition v b hv).moment i,x⟫ := by
  let h : Fin k → Space d := fun i => ⟪v i,x⟫ • y - ⟪v i,y⟫ • x
  have hs (i j : Fin k) : ⟪h i,v j⟫ + ⟪v i,h j⟫ = 0 := by
    simp only [h,inner_sub_left,inner_sub_right,real_inner_smul_left,real_inner_smul_right]
    rw [real_inner_comm y (v j), real_inner_comm x (v j)]
    ring
  have hh := gaussian_skew_moment_identity v h b hv hs
  have ht (i : Fin k) : ⟪h i,(winningPartition v b hv).moment i⟫ =
      ⟪v i,x⟫ * ⟪(winningPartition v b hv).moment i,y⟫ -
        ⟪v i,y⟫ * ⟪(winningPartition v b hv).moment i,x⟫ := by
    simp only [h,inner_sub_left,real_inner_smul_left]
    rw [real_inner_comm y ((winningPartition v b hv).moment i),
      real_inner_comm x ((winningPartition v b hv).moment i)]
  simp only [ht,Finset.sum_sub_distrib] at hh
  exact sub_eq_zero.mp hh

theorem gaussian_normal_moment_inner_symmetric
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (hv : Function.Injective v) (x y : Space (d+1)) :
    (∑ i : Fin (d+1), ⟪v 0 - v i.succ,x⟫ * ⟪rawWinningMoment v b i.succ,y⟫) =
      ∑ i : Fin (d+1), ⟪v 0 - v i.succ,y⟫ * ⟪rawWinningMoment v b i.succ,x⟫ := by
  let m := (winningPartition v b hv).moment
  have hz (z : Space (d+1)) : (∑ i, ⟪m i,z⟫) = 0 := by
    rw [← sum_inner, (winningPartition v b hv).sum_moment, inner_zero_left]
  have ht (z t : Space (d+1)) :
      (∑ i : Fin (d+1), ⟪v 0 - v i.succ,z⟫ * ⟪m i.succ,t⟫) =
        -(∑ i : Fin (d+2), ⟪v i,z⟫ * ⟪m i,t⟫) := by
    have hzt := hz t
    rw [Fin.sum_univ_succ] at hzt
    simp only [inner_sub_left, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    conv_rhs => rw [Fin.sum_univ_succ]
    nlinarith [congrArg (fun a : ℝ => ⟪v 0,z⟫ * a) hzt]
  simp_rw [rawWinningMoment_eq _ _ hv]
  rw [ht,ht, gaussian_score_moment_inner_symmetric v b hv x y]

/-- The coordinate matrix of the actual non-base moments in the full normal
basis is symmetric. This will force common weights on each shared face. -/
theorem gaussian_normal_coefficients_symmetric
    (v : Fin (d+2) → Space (d+1)) (b : Fin (d+2) → ℝ)
    (hv : Function.Injective v) (B : Basis (Fin (d+1)) ℝ (Space (d+1)))
    (hB : ∀ i, B i = v 0 - v i.succ) (p q : Fin (d+1)) :
    B.repr (rawWinningMoment v b p.succ) q =
      B.repr (rawWinningMoment v b q.succ) p := by
  classical
  obtain ⟨x,hx⟩ := basis_inner_interpolate B (fun i => if i = p then 1 else 0)
  obtain ⟨y,hy⟩ := basis_inner_interpolate B (fun i => if i = q then 1 else 0)
  have hx' (i : Fin (d+1)) : ⟪B i,x⟫ = if i = p then 1 else 0 :=
    (real_inner_comm _ _).trans (hx i)
  have hy' (i : Fin (d+1)) : ⟪B i,y⟫ = if i = q then 1 else 0 :=
    (real_inner_comm _ _).trans (hy i)
  have hcoord (u : Space (d+1)) : ⟪u,x⟫ = B.repr u p ∧ ⟪u,y⟫ = B.repr u q := by
    constructor
    · conv_lhs => rw [← B.sum_repr u]
      simp only [sum_inner,real_inner_smul_left]
      simp_rw [hx']
      simp
    · conv_lhs => rw [← B.sum_repr u]
      simp only [sum_inner,real_inner_smul_left]
      simp_rw [hy']
      simp
  have hh := gaussian_normal_moment_inner_symmetric v b hv x y
  simp_rw [← hB, hx',hy'] at hh
  simpa [ (hcoord _).1, (hcoord _).2] using hh

end GaussianMeasureBridge
