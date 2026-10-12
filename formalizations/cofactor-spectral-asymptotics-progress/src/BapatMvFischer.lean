import BapatMultiColor
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Permanent

set_option autoImplicit false
open scoped BigOperators
open MvPolynomial

namespace BapatFiniteRank

variable {ι κ C R : Type*} [Fintype C] [DecidableEq C] [CommSemiring R]

noncomputable section

def multiFactorial (α : C →₀ ℕ) : ℕ := ∏ c, (α c).factorial

/-- The actual factorial-weighted coefficient pairing, not a permanent oracle. -/
def fischerPair (p q : MvPolynomial C R) : R :=
  p.coeff.sum fun α a => (multiFactorial α : R) * a * q.coeff α

theorem fischerPair_monomial_left (α : C →₀ ℕ) (a : R) (q : MvPolynomial C R) :
    fischerPair (monomial α a) q = (multiFactorial α : R) * a * q.coeff α := by
  simp [fischerPair]

theorem fischerPair_add_left (p q t : MvPolynomial C R) :
    fischerPair (p + q) t = fischerPair p t + fischerPair q t := by
  unfold fischerPair
  rw [AddMonoidAlgebra.coeff_add]
  apply Finsupp.sum_add_index
  · intro α
    simp
  · intro α _ a b
    ring

theorem fischerPair_add_right (p q t : MvPolynomial C R) :
    fischerPair p (q + t) = fischerPair p q + fischerPair p t := by
  simp [fischerPair, mul_add, Finsupp.sum_add]

theorem fischerPair_sum_left {J : Type*} (s : Finset J)
    (p : J → MvPolynomial C R) (q : MvPolynomial C R) :
    fischerPair (∑ j ∈ s, p j) q = ∑ j ∈ s, fischerPair (p j) q := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fischerPair]
  | @insert a s ha ih => simp [Finset.sum_insert, ha, fischerPair_add_left, ih]

theorem fischerPair_sum_right {J : Type*} (s : Finset J)
    (p : MvPolynomial C R) (q : J → MvPolynomial C R) :
    fischerPair p (∑ j ∈ s, q j) = ∑ j ∈ s, fischerPair p (q j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [fischerPair]
  | @insert a s ha ih => simp [Finset.sum_insert, ha, fischerPair_add_right, ih]

def linearForm (v : C → R) : MvPolynomial C R :=
  ∑ c, monomial (Finsupp.single c 1) (v c)

def formsProduct [Fintype ι] (v : ι → C → R) : MvPolynomial C R :=
  ∏ i, linearForm (v i)

def assignmentDegree [Fintype ι] (f : ι → C) : C →₀ ℕ :=
  ∑ i, Finsupp.single (f i) 1

def assignmentWeight [Fintype ι] (v : ι → C → R) (f : ι → C) : R :=
  ∏ i, v i (f i)

theorem assignmentDegree_apply [Fintype ι] [DecidableEq ι]
    (f : ι → C) (c : C) : assignmentDegree f c = colorCounts f c := by
  simp [assignmentDegree, colorCounts, Finsupp.single_apply, eq_comm, Fintype.card_subtype]

theorem assignmentDegree_eq_iff [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (f : ι → C) (g : κ → C) :
    assignmentDegree f = assignmentDegree g ↔ colorCounts f = colorCounts g := by
  constructor
  · intro h
    funext c
    simpa only [assignmentDegree_apply] using congrArg (fun d : C →₀ ℕ => d c) h
  · intro h
    ext c
    simpa only [assignmentDegree_apply] using congrFun h c

theorem multiFactorial_assignmentDegree [Fintype ι] [DecidableEq ι] (f : ι → C) :
    multiFactorial (assignmentDegree f) = ∏ c, (colorCounts f c).factorial := by
  simp only [multiFactorial, assignmentDegree_apply]

theorem formsProduct_expand [Fintype ι] [DecidableEq ι] (v : ι → C → R) :
    formsProduct v = ∑ f : ι → C, monomial (assignmentDegree f) (assignmentWeight v f) := by
  unfold formsProduct linearForm
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f hf
  exact (MvPolynomial.monomial_sum_prod Finset.univ
    (fun i => Finsupp.single (f i) 1) (fun i => v i (f i))).symm

theorem fischerPair_formsProduct_expand [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (v : ι → C → R) (w : κ → C → R) :
    fischerPair (formsProduct v) (formsProduct w) =
      ∑ f : ι → C, ∑ g : κ → C,
        if assignmentDegree f = assignmentDegree g then
          (multiFactorial (assignmentDegree f) : R) * assignmentWeight v f * assignmentWeight w g
        else 0 := by
  rw [formsProduct_expand, formsProduct_expand, fischerPair_sum_left]
  apply Finset.sum_congr rfl
  intro f hf
  rw [fischerPair_sum_right]
  apply Finset.sum_congr rfl
  intro g hg
  rw [fischerPair_monomial_left, MvPolynomial.coeff_monomial]
  split_ifs <;> simp_all

section MixedPermanent

variable [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

def mixedPermanent (A : ι → κ → R) : R :=
  ∑ e : ι ≃ κ, ∏ i, A i (e i)

theorem assignmentWeight_reindex (e : ι ≃ κ) (w : κ → C → R) (f : ι → C) :
    (∏ i, w (e i) (f i)) = assignmentWeight w (fun j => f (e.symm j)) := by
  simpa [assignmentWeight] using e.prod_comp (fun j => w j (f (e.symm j)))

theorem reindex_fiber_iff (f : ι → C) (g : κ → C) (e : ι ≃ κ) :
    (fun j => f (e.symm j)) = g ↔ ∀ i, g (e i) = f i := by
  constructor
  · intro h i
    simpa using (congrFun h (e i)).symm
  · intro h
    funext j
    simpa using (h (e.symm j)).symm

theorem card_reindex_fiber (f : ι → C) (g : κ → C) :
    Fintype.card {e : ι ≃ κ // (fun j => f (e.symm j)) = g} =
      if colorCounts f = colorCounts g then ∏ c, (colorCounts f c).factorial else 0 := by
  let E : {e : ι ≃ κ // (fun j => f (e.symm j)) = g} ≃ ColorTransport f g :=
    Equiv.subtypeEquivRight (reindex_fiber_iff f g)
  exact (Fintype.card_congr E).trans (card_colorTransport f g)

theorem sum_reindexed_assignmentWeight (w : κ → C → R) (f : ι → C) :
    (∑ e : ι ≃ κ, assignmentWeight w (fun j => f (e.symm j))) =
      ∑ g : κ → C, if colorCounts f = colorCounts g then
        ((∏ c, (colorCounts f c).factorial : ℕ) : R) * assignmentWeight w g else 0 := by
  calc
    _ = ∑ g : κ → C, ∑ _e : {e : ι ≃ κ // (fun j => f (e.symm j)) = g},
        assignmentWeight w g :=
      (Fintype.sum_fiberwise' (fun e : ι ≃ κ => fun j => f (e.symm j))
        (assignmentWeight w)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro g hg
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_reindex_fiber]
      split_ifs <;> simp

/-- Genuine mixed cross-Gram permanent equals the full multivariate Fischer pairing.
No rank-two specialization, polynomial oracle, or equality-of-cardinalities assumption. -/
theorem mixedPermanent_fischer (v : ι → C → R) (w : κ → C → R) :
    mixedPermanent (fun i j => ∑ c, v i c * w j c) =
      fischerPair (formsProduct v) (formsProduct w) := by
  classical
  unfold mixedPermanent
  simp_rw [Fintype.prod_sum, Finset.prod_mul_distrib]
  rw [Finset.sum_comm, fischerPair_formsProduct_expand]
  apply Finset.sum_congr rfl
  intro f hf
  change (∑ e : ι ≃ κ, assignmentWeight v f * ∏ i, w (e i) (f i)) = _
  simp_rw [assignmentWeight_reindex]
  rw [← Finset.mul_sum, sum_reindexed_assignmentWeight, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g hg
  simp only [assignmentDegree_eq_iff, multiFactorial_assignmentDegree]
  split_ifs <;> simp_all [mul_left_comm, mul_assoc]

theorem fischerPair_C_mul_left (c : R) (p q : MvPolynomial C R) :
    fischerPair (MvPolynomial.C c * p) q = c * fischerPair p q := by
  conv_lhs => rw [MvPolynomial.as_sum p]
  simp only [Finset.mul_sum, MvPolynomial.C_mul_monomial, fischerPair_sum_left,
    fischerPair_monomial_left]
  unfold fischerPair
  rw [MvPolynomial.sum_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  ring

theorem fischerPair_C_mul_right (c : R) (p q : MvPolynomial C R) :
    fischerPair p (MvPolynomial.C c * q) = c * fischerPair p q := by
  unfold fischerPair
  simp only [MvPolynomial.coeff_C_mul, Finsupp.sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  ring

theorem mixedPermanent_eq_permanent (A : ι → ι → R) :
    mixedPermanent A = Matrix.permanent A := by
  rw [← Matrix.permanent_transpose A]
  rfl

theorem permanent_gram_fischer (v : ι → C → R) :
    Matrix.permanent (fun i j => ∑ c, v i c * v j c) =
      fischerPair (formsProduct v) (formsProduct v) := by
  rw [← mixedPermanent_eq_permanent]
  exact mixedPermanent_fischer v v

end MixedPermanent

end
end BapatFiniteRank
