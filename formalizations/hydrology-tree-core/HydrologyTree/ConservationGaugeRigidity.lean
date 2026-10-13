import HydrologyTree.DiagonalGauge
import HydrologyTree.GraphMassBalance

/-! A single specified leak and invertibility remove diagonal gauge freedom.
This is an all-real matrix theorem; positivity of a competing gauge is not needed. -/
open Matrix
noncomputable section
namespace HydrologyTree
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Conservation fixes the entire matrix inside a nonzero diagonal similarity
class when the leak site is fixed. Both leakage magnitudes are recovered. -/
theorem single_leak_diagonal_gauge_rigid (A B : Matrix V V ℝ) (ell : V)
    (a b : ℝ) (hb : b ≠ 0) (hB : B.det ≠ 0)
    (h : V → ℝ) (hh : ∀ v,h v ≠ 0)
    (hAcols : ∀ j,(∑ i,A i j)=if j=ell then -a else 0)
    (hBcols : ∀ j,(∑ i,B i j)=if j=ell then -b else 0)
    (hAB : A=diagonalGauge h B) : A=B ∧ a=b ∧ ∀ v,h v=h ell := by
  have hw (j : V) : (∑ i,h i*B i j)=if j=ell then -a*h ell else 0 := by
    have he := congrArg (fun z : ℝ => z*h j) (hAcols j)
    rw [hAB] at he
    simp only [diagonalGauge_apply,Finset.sum_mul,mul_assoc,inv_mul_cancel₀ (hh j),mul_one] at he
    by_cases hj : j=ell
    · simpa only [hj,ite_true] using he
    · simpa only [if_neg hj,zero_mul] using he
  letI : Invertible B := Matrix.invertibleOfIsUnitDet B (isUnit_iff_ne_zero.mpr hB)
  have he : Matrix.vecMul (fun i => b*h i) B=Matrix.vecMul (fun _ => a*h ell) B := by
    funext j
    simp only [Matrix.vecMul,dotProduct,mul_assoc,← Finset.mul_sum]
    rw [hw j,hBcols j]
    by_cases hj : j=ell <;> simp [hj] <;> ring
  have hr := Matrix.vecMul_injective_of_invertible B he
  have hell := congrFun hr ell
  have hba : b=a := mul_right_cancel₀ (hh ell) hell
  have hconst (v : V) : h v=h ell := by
    have hv := congrFun hr v
    rw [← hba] at hv
    exact mul_left_cancel₀ hb hv
  refine ⟨?_,hba.symm,hconst⟩
  rw [hAB]
  ext i j
  rw [diagonalGauge_apply,hconst i,hconst j]
  field_simp [hh ell]

/-- Actual graph models with a fixed leakage site have no residual diagonal
similarity ambiguity once a nonzero invertible reference is supplied. -/
theorem graph_same_leak_gauge_unique {G : SimpleGraph V} [DecidableRel G.Adj]
    (ell : V) (x y : GraphRates G) (hy : y.1 ≠ 0)
    (hB : (graphCompartmentMatrix G ell y).det ≠ 0)
    (h : V → ℝ) (hh : ∀ v,h v ≠ 0)
    (he : graphCompartmentMatrix G ell x=diagonalGauge h (graphCompartmentMatrix G ell y)) :
    graphCompartmentMatrix G ell x=graphCompartmentMatrix G ell y :=
  (single_leak_diagonal_gauge_rigid _ _ ell x.1 y.1 hy hB h hh
    (graphCompartment_column_sum ell x) (graphCompartment_column_sum ell y) he).1

end HydrologyTree
