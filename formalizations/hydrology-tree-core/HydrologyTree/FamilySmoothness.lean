import HydrologyTree.FamilyProduct
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Smoothness of the actual monic factor product; differentiating its derivative
is justified rather than assumed as a hidden Hessian input. -/
open Polynomial
noncomputable section
namespace HydrologyTree

lemma contDiff_monicPoly (n : ℕ) : ContDiff ℝ 2 (monicPoly (n := n)) :=
  contDiff_const.add (liftCLM n).contDiff

lemma contDiff_monicMultiply (m n : ℕ) : ContDiff ℝ 2 (monicMultiply (m := m) (n := n)) := by
  have ha := (contDiff_monicPoly m).comp
    (ContinuousLinearMap.fst ℝ (Coeff m) (Coeff n)).contDiff
  have hb := (contDiff_monicPoly n).comp
    (ContinuousLinearMap.snd ℝ (Coeff m) (Coeff n)).contDiff
  exact ((mulCLM (m+1) (n+1) (m+n)).contDiff.comp ha).clm_apply hb

/-- Every finite factor product has the differentiability needed by the tangent lift. -/
theorem contDiff_familyProduct (ms : List ℕ) : ContDiff ℝ 2 (familyProduct ms) := by
  induction ms with
  | nil => exact contDiff_const
  | cons m ms ih =>
    change ContDiff ℝ 2 (fun x : Coeff m × ProductInput ms =>
      monicMultiply (x.1, familyProduct ms x.2))
    have ha : ContDiff ℝ 2 (fun x : Coeff m × ProductInput ms => x.1) :=
      (ContinuousLinearMap.fst ℝ (Coeff m) (ProductInput ms)).contDiff
    have hb : ContDiff ℝ 2 (fun x : Coeff m × ProductInput ms => familyProduct ms x.2) :=
      ih.comp (ContinuousLinearMap.snd ℝ (Coeff m) (ProductInput ms)).contDiff
    exact (contDiff_monicMultiply m ms.sum).comp (ha.prodMk hb)

lemma familyProductDerivative_eq_fderiv (ms : List ℕ) :
    familyProductDerivative ms = fderiv ℝ (familyProduct ms) := by
  funext x
  exact (hasFDerivAt_familyProduct ms x).fderiv.symm

/-- The derivative-valued map is itself differentiable everywhere. -/
theorem differentiable_familyProductDerivative (ms : List ℕ) :
    Differentiable ℝ (familyProductDerivative ms) := by
  rw [familyProductDerivative_eq_fderiv]
  exact ((contDiff_familyProduct ms).fderiv_right (m := 1) (by norm_num)).differentiable_one

end HydrologyTree
