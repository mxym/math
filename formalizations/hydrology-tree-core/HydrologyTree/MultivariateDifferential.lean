import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! The actual Frechet differential of multivariate polynomial evaluation,
with its formally differentiated coefficients. No automatic or external
symbolic-differentiation oracle is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace HydrologyTree

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Continuous linear differential with the actual formal partial derivatives. -/
def multivariateDifferential (p : MvPolynomial ι ℝ) (x : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i : ι, MvPolynomial.eval x (MvPolynomial.pderiv i p) • ContinuousLinearMap.proj i

lemma multivariateDifferential_apply (p : MvPolynomial ι ℝ) (x h : ι → ℝ) :
    multivariateDifferential p x h = ∑ i : ι, MvPolynomial.eval x (MvPolynomial.pderiv i p) * h i := by
  simp [multivariateDifferential]

lemma multivariateDifferential_constant (a : ℝ) (x : ι → ℝ) :
    multivariateDifferential (MvPolynomial.C a) x = 0 := by
  simp [multivariateDifferential,MvPolynomial.pderiv_C]

lemma multivariateDifferential_variable (j : ι) (x : ι → ℝ) :
    multivariateDifferential (MvPolynomial.X j) x = ContinuousLinearMap.proj j := by
  apply ContinuousLinearMap.ext
  intro h
  rw [multivariateDifferential_apply]
  simp [MvPolynomial.pderiv_X,Pi.single_apply,ite_mul,apply_ite,eq_comm]

lemma multivariateDifferential_add (p q : MvPolynomial ι ℝ) (x : ι → ℝ) :
    multivariateDifferential (p+q) x = multivariateDifferential p x + multivariateDifferential q x := by
  apply ContinuousLinearMap.ext
  intro h
  simp [multivariateDifferential_apply,map_add,add_mul,Finset.sum_add_distrib]

lemma multivariateDifferential_mul (p q : MvPolynomial ι ℝ) (x : ι → ℝ) :
    multivariateDifferential (p*q) x =
      MvPolynomial.eval x p • multivariateDifferential q x +
        MvPolynomial.eval x q • multivariateDifferential p x := by
  apply ContinuousLinearMap.ext
  intro h
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    multivariateDifferential_apply,MvPolynomial.pderiv_mul,map_add,map_mul,add_mul,
    Finset.sum_add_distrib,Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- Formal partial differentiation agrees with the actual Frechet derivative
for every finite set of real coordinates and every polynomial. -/
theorem hasFDerivAt_multivariate_eval (p : MvPolynomial ι ℝ) (x : ι → ℝ) :
    HasFDerivAt (fun y => MvPolynomial.eval y p) (multivariateDifferential p x) x := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa only [MvPolynomial.eval_C,multivariateDifferential_constant] using
      (hasFDerivAt_const a x)
  | add p q hp hq =>
    have h := hp.add hq
    simpa only [map_add,multivariateDifferential_add,Pi.add_def] using h
  | mul_X p j hp =>
    have hj : HasFDerivAt (fun y : ι → ℝ => y j) (ContinuousLinearMap.proj j) x :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j).hasFDerivAt
    simpa only [map_mul,MvPolynomial.eval_X,multivariateDifferential_mul,
      multivariateDifferential_variable,Pi.mul_def] using hp.mul hj

/-- Applying the differential to a standard coordinate vector gives exactly
the evaluation of the corresponding formal partial derivative. -/
theorem multivariateDifferential_basis (p : MvPolynomial ι ℝ) (x : ι → ℝ) (j : ι) :
    multivariateDifferential p x (Pi.single j 1) = MvPolynomial.eval x (MvPolynomial.pderiv j p) := by
  rw [multivariateDifferential_apply]
  simp [Pi.single_apply,mul_ite]

end HydrologyTree
