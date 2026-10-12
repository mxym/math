import GaussianRegularValue
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! An actual score family with positive regular Gram covariance needs at
least k-1 ambient dimensions. This proves the rank obstruction independently
of any moment bound. -/
open MeasureTheory ProbabilityTheory Set Module Matrix
open scoped RealInnerProductSpace
namespace GaussianMeasureBridge
variable {d n : ℕ}

lemma regular_difference_gram
    (v : Fin (n+2) → Space d) (s : ℝ)
    (hv : scoreGram v = s • regularCovariance (n+2)) :
    Matrix.gram ℝ (fun i : Fin (n+1) => v 0 - v i.succ) =
      (s / (n+1:ℝ)) •
        ((1 : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) +
          Matrix.vecMulVec (fun _ => (1:ℝ)) (fun _ => (1:ℝ))) := by
  ext i j
  have hg (p q : Fin (n+2)) : ⟪v p,v q⟫ =
      s * (((n+1:ℕ):ℝ)⁻¹ * ((if p = q then 1 else 0) - ((n+2:ℕ):ℝ)⁻¹)) := by
    have hh := congrArg (fun A => A p q) hv
    simpa only [scoreGram,Matrix.smul_apply,smul_eq_mul,regularCovariance_apply,
      show n+2-1 = n+1 by omega] using hh
  simp only [Matrix.gram_apply,inner_sub_left,inner_sub_right,hg,ite_true,
    Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero i),Ne.symm (Fin.succ_ne_zero j),ite_false,
    Fin.succ_inj,Matrix.smul_apply,smul_eq_mul,Matrix.add_apply,Matrix.one_apply,
    Matrix.vecMulVec_apply,mul_one,div_eq_mul_inv,Nat.cast_add,Nat.cast_one]
  ring

theorem regular_gram_dimension_lower_bound
    (v : Fin (n+2) → Space d) (s : ℝ) (hs : 0 < s)
    (hv : scoreGram v = s • regularCovariance (n+2)) : n+1 ≤ d := by
  have hpos : (Matrix.gram ℝ (fun i : Fin (n+1) => v 0-v i.succ)).PosDef := by
    rw [regular_difference_gram v s hv]
    exact (Matrix.PosDef.one.add_posSemidef
      (by simpa only [Pi.star_apply,star_trivial] using
        Matrix.posSemidef_vecMulVec_self_star (fun _ : Fin (n+1) => (1:ℝ)))).smul
      (div_pos hs (by positivity : (0:ℝ) < n+1))
  have hi := (Matrix.linearIndependent_of_posDef_gram hpos).fintype_card_le_finrank
  simpa [Space] using hi

end GaussianMeasureBridge
