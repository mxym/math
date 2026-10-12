import GaussianMinimalCovarianceRows
import GaussianRegularValue
import GaussianSimplexAlgebra

/-! The regular centered covariance has a positive-definite principal block.
The proof is the finite Cauchy inequality with k=n+1, not an eigenvalue or
rank assumption. -/
open MeasureTheory ProbabilityTheory Set Module Matrix
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {n : ℕ} [NeZero n]

theorem regular_principal_posDef : (principalCovariance (regularCovariance (n+1))).PosDef := by
  classical
  have hn : (0:ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  have hk : (0:ℝ) < n+1 := by positivity
  have hc : ((n+1:ℕ):ℝ) = (n:ℝ)+1 := by norm_cast
  have hA : principalCovariance (regularCovariance (n+1)) =
      (n:ℝ)⁻¹ • ((1 : Matrix (Fin n) (Fin n) ℝ) -
        ((n:ℝ)+1)⁻¹ • Matrix.vecMulVec (fun _ => (1:ℝ)) (fun _ => (1:ℝ))) := by
    ext i j
    simp [principalCovariance,regularCovariance_apply,Matrix.submatrix_apply,
      Matrix.one_apply,Matrix.vecMulVec_apply,hc,Fin.succ_inj]
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  refine ⟨(scoreGram_posSemidef (regularRows (n+1))).submatrix Fin.succ |>.isHermitian,?_⟩
  intro x hx
  have hsum : 0 < ∑ i : Fin n, x i^2 := by
    obtain ⟨i,hi⟩ := Function.ne_iff.mp hx
    exact Finset.sum_pos' (fun j _ => sq_nonneg (x j))
      ⟨i,Finset.mem_univ _,sq_pos_of_ne_zero hi⟩
  have hcs := GaussianSimplexAlgebra.weighted_cauchy (Finset.univ : Finset (Fin n))
    (fun _ => 1) x (fun _ _ => by norm_num)
  simp only [one_mul,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at hcs
  have hcalc : star x ⬝ᵥ (principalCovariance (regularCovariance (n+1)) *ᵥ x) =
      (n:ℝ)⁻¹ * ((∑ i, x i^2) - ((n:ℝ)+1)⁻¹ * (∑ i,x i)^2) := by
    rw [hA]
    simp only [Matrix.smul_mulVec,Matrix.sub_mulVec,Matrix.one_mulVec,Matrix.vecMulVec_mulVec,
      dotProduct_smul,dotProduct_sub,star_trivial,Pi.one_apply,one_mul,smul_eq_mul,
      dotProduct,mul_one]
    simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,op_smul_eq_smul,mul_one]
    have ht (i : Fin n) : x i * ((n:ℝ)⁻¹ * (x i - ((n:ℝ)+1)⁻¹ * (∑ j,x j))) =
        (n:ℝ)⁻¹ * x i^2 - ((n:ℝ)⁻¹ * ((n:ℝ)+1)⁻¹ * (∑ j,x j)) * x i := by ring
    simp_rw [ht,Finset.sum_sub_distrib,← Finset.mul_sum]
    ring
  rw [hcalc]
  apply mul_pos (inv_pos.mpr hn)
  have hgap : 0 < ((n:ℝ)+1) * (∑ i,x i^2) - (∑ i,x i)^2 := by nlinarith
  have hpos : 0 < ((n:ℝ)+1)⁻¹ *
      (((n:ℝ)+1)*(∑ i,x i^2) - (∑ i,x i)^2) := mul_pos (inv_pos.mpr hk) hgap
  rw [mul_sub,← mul_assoc,inv_mul_cancel₀ hk.ne',one_mul] at hpos
  exact hpos

end GaussianMeasureBridge
