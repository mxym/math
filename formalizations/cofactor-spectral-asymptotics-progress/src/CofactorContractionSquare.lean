import CofactorTensorArrays

/-! The two-block partial swap has a nonnegative matrix coefficient:
it is exactly a sum of squared finite coordinate contractions. -/
set_option autoImplicit false
open scoped BigOperators ComplexOrder
namespace CofactorSpectral
variable {A B J C : Type*} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype J] [DecidableEq J]
  [Fintype C] [DecidableEq C]
noncomputable section

theorem finite_contraction_square (u : A → J → ℂ) (v : B → J → ℂ) :
    (∑ a, ∑ b, ∑ x, ∑ y, u a x * v b y * star (u a y * v b x)) =
      ∑ a, ∑ b, ((Complex.normSq (∑ x, u a x * star (v b x))) : ℂ) := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [← Complex.star_def, star_sum, star_mul, star_star, Finset.sum_mul,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

def partialSwap : Equiv.Perm ((A ⊕ J) ⊕ (B ⊕ J)) where
  toFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inr j)
    | Sum.inr (Sum.inl b) => Sum.inr (Sum.inl b)
    | Sum.inr (Sum.inr j) => Sum.inl (Sum.inr j)
  invFun
    | Sum.inl (Sum.inl a) => Sum.inl (Sum.inl a)
    | Sum.inl (Sum.inr j) => Sum.inr (Sum.inr j)
    | Sum.inr (Sum.inl b) => Sum.inr (Sum.inl b)
    | Sum.inr (Sum.inr j) => Sum.inl (Sum.inr j)
  left_inv x := by rcases x with (a|j)|(b|j) <;> rfl
  right_inv x := by rcases x with (a|j)|(b|j) <;> rfl

def fourAssignmentsEquiv :
    (((A ⊕ J) ⊕ (B ⊕ J)) → C) ≃ ((A → C) × (J → C)) × ((B → C) × (J → C)) :=
  (Equiv.sumArrowEquivProdArrow (A ⊕ J) (B ⊕ J) C).trans
    ((Equiv.sumArrowEquivProdArrow A J C).prodCongr (Equiv.sumArrowEquivProdArrow B J C))

theorem sum_four_assignments (F : (((A ⊕ J) ⊕ (B ⊕ J)) → C) → ℂ) :
    (∑ f, F f) = ∑ a : A → C, ∑ x : J → C, ∑ b : B → C, ∑ y : J → C,
      F (Sum.elim (Sum.elim a x) (Sum.elim b y)) := by
  calc
    _ = ∑ q : ((A → C) × (J → C)) × ((B → C) × (J → C)),
        F (fourAssignmentsEquiv.symm q) := by
      apply Fintype.sum_equiv fourAssignmentsEquiv
      intro f
      rw [Equiv.symm_apply_apply]
    _ = _ := by
      simp only [Fintype.sum_prod_type]
      rfl

theorem partialSwap_blockArray (u : ((A ⊕ J) → C) → ℂ)
    (v : ((B ⊕ J) → C) → ℂ) (a : A → C) (x : J → C) (b : B → C) (y : J → C) :
    blockArray u v ((Sum.elim (Sum.elim a x) (Sum.elim b y)) ∘ partialSwap.symm) =
      u (Sum.elim a y) * v (Sum.elim b x) := by
  unfold blockArray
  congr 1
  · congr 1
    funext z
    rcases z with a|j <;> rfl
  · congr 1
    funext z
    rcases z with b|j <;> rfl

theorem partialSwap_coefficient_nonneg (u : ((A ⊕ J) → C) → ℂ)
    (v : ((B ⊕ J) → C) → ℂ) :
    0 ≤ arrayCoefficient (blockArray u v) partialSwap := by
  unfold arrayCoefficient arrayPair
  rw [sum_four_assignments]
  have h : (∑ a : A → C, ∑ x : J → C, ∑ b : B → C, ∑ y : J → C,
      blockArray u v (Sum.elim (Sum.elim a x) (Sum.elim b y)) *
        star (blockArray u v
          ((Sum.elim (Sum.elim a x) (Sum.elim b y)) ∘ partialSwap.symm))) =
      ∑ a : A → C, ∑ b : B → C,
        ((Complex.normSq (∑ x : J → C, u (Sum.elim a x) * star (v (Sum.elim b x)))) : ℂ) := by
    simp only [partialSwap_blockArray]
    change (∑ a : A → C, ∑ x : J → C, ∑ b : B → C, ∑ y : J → C,
      u (Sum.elim a x) * v (Sum.elim b y) *
        star (u (Sum.elim a y) * v (Sum.elim b x))) = _
    conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
    exact finite_contraction_square (fun a x => u (Sum.elim a x))
      (fun b x => v (Sum.elim b x))
  rw [h]
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => by
    exact_mod_cast Complex.normSq_nonneg _

end
end CofactorSpectral
