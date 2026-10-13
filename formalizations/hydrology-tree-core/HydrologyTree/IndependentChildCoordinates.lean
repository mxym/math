import HydrologyTree.ScaledSerialization
import HydrologyTree.CanonicalTree

/-! Exact bijective preparation of independent physical child coefficient arrays,
connector scales, and a root diagonal for the proved all-arity local coefficient
map. No independence or dimension matching is postulated. -/
open Polynomial
noncomputable section
namespace HydrologyTree

variable {I : Type*} [Fintype I]

abbrev IndependentChildData (m : I → ℕ) := ((i : I) → TreeRates (m i)) × (ℝ × (I → ℝ))
abbrev IndependentChildPolynomials (m : I → ℕ) :=
  ((i : I) → PathCoefficients (m i)) × (ℝ × (I → ℝ))
abbrev IndependentSlots (m : I → ℕ) :=
  (((i : I) → Coeff (m i+1)) × ((i : I) → Coeff (m i+1))) × ℝ

/-- Only regrouping, before the independent leading-coefficient equivalences. -/
def childSlotRegroup (m : I → ℕ) : IndependentChildPolynomials m ≃ₗ[ℝ]
    ((((i : I) → Coeff (m i+1)) × ((i : I) → ℝ × Coeff (m i))) × ℝ) where
  toFun z := ((fun i => (z.1 i).1,fun i => (z.2.2 i,(z.1 i).2)),z.2.1)
  invFun z := (fun i => (z.1.1 i,(z.1.2 i).2),(z.2,fun i => (z.1.2 i).1))
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Pair child lower cofactor coefficients with their independent connector scale. -/
def childPolynomialSlots (m : I → ℕ) : IndependentChildPolynomials m ≃ₗ[ℝ] IndependentSlots m :=
  (childSlotRegroup m).trans
    (((LinearEquiv.refl ℝ ((i : I) → Coeff (m i+1))).prodCongr
      (LinearEquiv.piCongrRight (fun i => leadingEquiv (m i)))).prodCongr (LinearEquiv.refl ℝ ℝ))

/-- Fixed-rate-independent equivalence into the actual gluing/root coefficient spaces. -/
def prepareFamilyEquiv (m : I → ℕ) : IndependentChildData m ≃ₗ[ℝ] BranchStepInputs (degreeSequence m) :=
  (((LinearEquiv.piCongrRight (fun i => (coefficientArrayEquiv (m i)).symm)).prodCongr
    (LinearEquiv.refl ℝ (ℝ × (I → ℝ)))).trans (childPolynomialSlots m)) |>.trans
      (((piScaledEquiv m).prodCongr (piScaledEquiv m)).prodCongr (LinearEquiv.refl ℝ ℝ))

lemma prepareFamilyEquiv_apply (m : I → ℕ) (z : IndependentChildData m) :
    prepareFamilyEquiv m z =
      ((piScaledEquiv m (fun i => ((coefficientArrayEquiv (m i)).symm (z.1 i)).1),
        piScaledEquiv m (fun i => leadingEquiv (m i)
          (z.2.2 i,((coefficientArrayEquiv (m i)).symm (z.1 i)).2))),z.2.1) := rfl

/-- Root coordinates and every child coordinate are serialized without rescaling. -/
def independentChildDot (m : I → ℕ) (x y : IndependentChildData m) : ℝ :=
  (∑ i : I, physicalRateDot (m i) (x.1 i) (y.1 i)) + x.2.1*y.2.1 + ∑ i : I, x.2.2 i*y.2.2 i

def branchInputDot (ms : List ℕ) (x y : BranchStepInputs ms) : ℝ :=
  familyCoordinateDot (ChildFactorDegrees ms) x.1.1 y.1.1 +
    familyCoordinateDot (ChildFactorDegrees ms) x.1.2 y.1.2 + x.2*y.2

lemma coefficientArrayEquiv_symm_dot (n : ℕ) (x y : TreeRates n) :
    pathCoefficientDot n ((coefficientArrayEquiv n).symm x) ((coefficientArrayEquiv n).symm y) =
      physicalRateDot n x y := by
  have h := coefficientArrayEquiv_dot n ((coefficientArrayEquiv n).symm x)
    ((coefficientArrayEquiv n).symm y)
  rw [LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply] at h
  exact h.symm

/-- Coordinate preparation is an unscaled permutation in the actual coefficient
Euclidean bilinear form. This later certifies determinant magnitude one. -/
theorem prepareFamilyEquiv_dot (m : I → ℕ) (x y : IndependentChildData m) :
    branchInputDot (degreeSequence m) (prepareFamilyEquiv m x) (prepareFamilyEquiv m y) =
      independentChildDot m x y := by
  rw [branchInputDot,prepareFamilyEquiv_apply,prepareFamilyEquiv_apply,piScaled_dot,piScaled_dot]
  simp only [leadingEquiv_dot,Finset.sum_add_distrib]
  unfold independentChildDot
  have h : (∑ i : I, physicalRateDot (m i) (x.1 i) (y.1 i)) =
      (∑ i : I, coefficientDot (m i+1)
        ((coefficientArrayEquiv (m i)).symm (x.1 i)).1
        ((coefficientArrayEquiv (m i)).symm (y.1 i)).1) +
      (∑ i : I, coefficientDot (m i)
        ((coefficientArrayEquiv (m i)).symm (x.1 i)).2
        ((coefficientArrayEquiv (m i)).symm (y.1 i)).2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact (coefficientArrayEquiv_symm_dot (m i) (x.1 i) (y.1 i)).symm
  rw [h]
  ring

/-- The local scaling factors are exactly the given connector products, not
coefficients introduced by an unproved change of basis. -/
theorem prepareFamilyEquiv_scaleWeight (m : I → ℕ) (z : IndependentChildData m) :
    scaleFamilyWeight (degreeSequence m) (prepareFamilyEquiv m z).1.2 = ∏ i : I, (z.2.2 i) ^ m i := by
  rw [prepareFamilyEquiv_apply,piScaled_weight]
  apply Finset.prod_congr rfl
  intro i _
  have h := split_joinLeading (z.2.2 i,((coefficientArrayEquiv (m i)).symm (z.1 i)).2)
  exact congrArg (fun c : ℝ => c ^ m i) (congrArg Prod.fst h)

end HydrologyTree
