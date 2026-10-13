import HydrologyTree.EndJacobian
import HydrologyTree.Scaling
import HydrologyTree.FamilyProduct

/-! Actual simultaneous scaling of every child numerator, including all zero
scales. This is one component of the full branching-tree Jacobian chain. -/
open Module Polynomial
noncomputable section
namespace HydrologyTree

instance productInputFiniteDimensional (ms : List ℕ) : FiniteDimensional ℝ (ProductInput ms) :=
  Module.Finite.of_basis (familyBasis ms)

section Products
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def productEndMap (f : E → E) (g : F → F) (z : E × F) : E × F := (f z.1,g z.2)

lemma hasFDerivAt_productEndMap (f : E → E) (g : F → F) (z : E × F)
    (hf : DifferentiableAt ℝ f z.1) (hg : DifferentiableAt ℝ g z.2) :
    HasFDerivAt (productEndMap f g)
      ((fderiv ℝ f z.1).prodMap (fderiv ℝ g z.2)) z := by
  exact (hf.hasFDerivAt.comp z (ContinuousLinearMap.fst ℝ E F).hasFDerivAt).prodMk
    (hg.hasFDerivAt.comp z (ContinuousLinearMap.snd ℝ E F).hasFDerivAt)

lemma endJacobian_productEndMap [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (f : E → E) (g : F → F) (z : E × F)
    (hf : DifferentiableAt ℝ f z.1) (hg : DifferentiableAt ℝ g z.2) :
    endJacobian (productEndMap f g) z = endJacobian f z.1 * endJacobian g z.2 := by
  rw [endJacobian_of_hasFDerivAt (hasFDerivAt_productEndMap f g z hf hg)]
  exact LinearMap.det_prodMap _ _

end Products

/-- Interpret the leading coefficient as an independent scale, and lower
coefficients as those of a monic polynomial, then carry out actual multiplication. -/
def scaleLeading (n : ℕ) (q : Coeff (n+1)) : Coeff (n+1) :=
  leadingEquiv n (scaleChart ((leadingEquiv n).symm q))

lemma scaleLeading_actual (n : ℕ) (q : Coeff (n+1)) :
    scaleLeading n q = (q : ℝ[X]).coeff n • monicPoly (cut n (q : ℝ[X])) := by
  have h := congrFun (scaleMonic_eq_comp (n := n)) ((leadingEquiv n).symm q)
  exact h.symm

lemma differentiable_scaleLeading (n : ℕ) : Differentiable ℝ (scaleLeading n) := by
  intro q
  exact (leadingEquiv n).toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt.comp q
    ((hasFDerivAt_scaleChart ((leadingEquiv n).symm q)).differentiableAt.comp q
      (leadingEquiv n).symm.toContinuousLinearEquiv.toContinuousLinearMap.differentiableAt)

lemma endJacobian_scaleChart (n : ℕ) (q : ℝ × Coeff n) :
    endJacobian scaleChart q = q.1 ^ n := by
  rw [endJacobian_of_hasFDerivAt (hasFDerivAt_scaleChart q),
    ← LinearMap.det_toMatrix ((Basis.singleton Unit ℝ).prod (degreeLT.basis ℝ n)),
    det_scaleChartDerivative]
  simp

/-- The actual scaling determinant is proved with no division by the scale. -/
theorem endJacobian_scaleLeading (n : ℕ) (q : Coeff (n+1)) :
    endJacobian (scaleLeading n) q = (q : ℝ[X]).coeff n ^ n := by
  have h := endJacobian_conjugate (leadingEquiv n).toContinuousLinearEquiv
    scaleChart q (hasFDerivAt_scaleChart _).differentiableAt
  rw [endJacobian_scaleChart] at h
  exact h

/-- A child with n internal edges has a cofactor of degree n and denominator
of degree n+1. This list transformation reflects those actual dimensions. -/
abbrev ChildFactorDegrees (ms : List ℕ) := ms.map (fun n => n+1)
abbrev ScaledFamilyInput (ms : List ℕ) := ProductInput (ChildFactorDegrees ms)

def scaleFamily : (ms : List ℕ) → ScaledFamilyInput ms → ScaledFamilyInput ms
  | [], q => q
  | m :: ms, q => (scaleLeading m q.1, scaleFamily ms q.2)

def scaleFamilyWeight : (ms : List ℕ) → ScaledFamilyInput ms → ℝ
  | [], _ => 1
  | m :: ms, q => (q.1 : ℝ[X]).coeff m ^ m * scaleFamilyWeight ms q.2

lemma differentiable_scaleFamily (ms : List ℕ) : Differentiable ℝ (scaleFamily ms) := by
  induction ms with
  | nil => exact differentiable_id
  | cons m ms ih =>
    intro q
    exact (hasFDerivAt_productEndMap (scaleLeading m) (scaleFamily ms) q
      (differentiable_scaleLeading m q.1) (ih q.2)).differentiableAt

/-- Exact product of all monic numerator-scaling factors at an arbitrary root. -/
theorem endJacobian_scaleFamily (ms : List ℕ) (q : ScaledFamilyInput ms) :
    endJacobian (scaleFamily ms) q = scaleFamilyWeight ms q := by
  induction ms with
  | nil => change endJacobian id q = 1; simp [endJacobian]
  | cons m ms ih =>
    change endJacobian (productEndMap (scaleLeading m) (scaleFamily ms)) q = _
    rw [endJacobian_productEndMap _ _ _ (differentiable_scaleLeading m q.1)
      (differentiable_scaleFamily ms q.2), endJacobian_scaleLeading, ih]
    rfl

end HydrologyTree
