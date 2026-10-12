import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Exact finite combinatorics of labelled child-pole allocations. Block labels
are preserved and only within-block enumerations are factored out. -/
open scoped BigOperators
noncomputable section
namespace HydrologyTree

variable {B : Type*} [Fintype B] [DecidableEq B]

abbrev AllocationNodes (m : B → ℕ) := Σ b, Fin (m b)

/-- Assign each distinct pole index to a labelled block with the prescribed size. -/
abbrev SizedAllocation (m : B → ℕ) (n : ℕ) :=
  {a : Fin n → B // ∀ b, Fintype.card {i : Fin n // a i=b} = m b}

instance sizedAllocationFinite (m : B → ℕ) (n : ℕ) : Finite (SizedAllocation m n) := by
  unfold SizedAllocation
  infer_instance

instance sizedAllocationFintype (m : B → ℕ) (n : ℕ) : Fintype (SizedAllocation m n) := Fintype.ofFinite _

abbrev AllocationFiber {m : B → ℕ} {n : ℕ} (a : SizedAllocation m n) (b : B) :=
  {i : Fin n // a.val i=b}

/-- Canonical increasing enumeration fixes the internal pole order in every block. -/
def allocationEnumeration {m : B → ℕ} {n : ℕ} (a : SizedAllocation m n) (b : B) :
    Fin (m b) ≃o AllocationFiber a b := Fintype.orderIsoFinOfCardEq _ (a.property b)

abbrev AllocationEnumerations {m : B → ℕ} {n : ℕ} (a : SizedAllocation m n) :=
  (b : B) → Fin (m b) ≃ AllocationFiber a b

def assembleAllocationMap {m : B → ℕ} {n : ℕ} (a : SizedAllocation m n)
    (g : AllocationEnumerations a) : AllocationNodes m → Fin n := fun z => (g z.1 z.2).val

lemma assembleAllocationMap_bijective {m : B → ℕ} {n : ℕ} (a : SizedAllocation m n)
    (g : AllocationEnumerations a) : Function.Bijective (assembleAllocationMap a g) := by
  constructor
  · rintro ⟨b,i⟩ ⟨c,j⟩ h
    have hbc : b=c := (g b i).property.symm.trans ((congrArg a.val h).trans (g c j).property)
    subst c
    have hij := (g b).injective (Subtype.ext h)
    change i=j at hij
    subst j
    rfl
  · intro i
    obtain ⟨j,hj⟩ := (g (a.val i)).surjective ⟨i,rfl⟩
    exact ⟨⟨a.val i,j⟩,congrArg Subtype.val hj⟩

def assembleAllocationEquiv {m : B → ℕ} {n : ℕ} (a : SizedAllocation m n)
    (g : AllocationEnumerations a) : AllocationNodes m ≃ Fin n :=
  Equiv.ofBijective (assembleAllocationMap a g) (assembleAllocationMap_bijective a g)

/-- A canonical coordinate bijection realizing precisely the chosen allocation. -/
def allocationEquiv {m : B → ℕ} {n : ℕ} (a : SizedAllocation m n) : AllocationNodes m ≃ Fin n :=
  assembleAllocationEquiv a (fun b => (allocationEnumeration a b).toEquiv)

lemma allocationEquiv_label {m : B → ℕ} {n : ℕ} (a : SizedAllocation m n) (b : B) (i : Fin (m b)) :
    a.val (allocationEquiv a ⟨b,i⟩)=b := (allocationEnumeration a b i).property

/-- The label function induced by any ordering of all pole indices. -/
def allocationLabel {m : B → ℕ} {n : ℕ} (e : AllocationNodes m ≃ Fin n) (i : Fin n) : B :=
  (e.symm i).1

def equivFiberMap {m : B → ℕ} {n : ℕ} (e : AllocationNodes m ≃ Fin n) (b : B) :
    Fin (m b) → {i : Fin n // allocationLabel e i=b} :=
  fun j => ⟨e ⟨b,j⟩,by simp [allocationLabel]⟩

lemma equivFiberMap_bijective {m : B → ℕ} {n : ℕ} (e : AllocationNodes m ≃ Fin n) (b : B) :
    Function.Bijective (equivFiberMap e b) := by
  constructor
  · intro i j hij
    have h := e.injective (congrArg Subtype.val hij)
    exact Fin.ext (congrArg (fun z : AllocationNodes m => z.2.val) h)
  · intro i
    obtain ⟨⟨c,j⟩,hj⟩ := e.surjective i.val
    have hcb : c=b := by
      have h := i.property
      rw [allocationLabel,← hj,Equiv.symm_apply_apply] at h
      exact h
    subst c
    exact ⟨j,Subtype.ext hj⟩

/-- The required block sizes follow from a proved bijection, not a cardinality assumption. -/
def allocationOfEquiv {m : B → ℕ} {n : ℕ} (e : AllocationNodes m ≃ Fin n) : SizedAllocation m n :=
  ⟨allocationLabel e,fun b => by
    have h := Fintype.card_congr (Equiv.ofBijective (equivFiberMap e b) (equivFiberMap_bijective e b))
    simpa only [Fintype.card_fin] using h.symm⟩

lemma allocationOfEquiv_assemble {m : B → ℕ} {n : ℕ} (a : SizedAllocation m n)
    (g : AllocationEnumerations a) : allocationOfEquiv (assembleAllocationEquiv a g)=a := by
  apply Subtype.ext
  funext i
  obtain ⟨⟨b,j⟩,hj⟩ := (assembleAllocationEquiv a g).surjective i
  rw [← hj]
  change (allocationLabel (assembleAllocationEquiv a g) ((assembleAllocationEquiv a g) ⟨b,j⟩)) = _
  rw [allocationLabel,Equiv.symm_apply_apply]
  exact (g b j).property.symm

/-- Bijection: global pole orderings are labelled allocations together with
independent permutations of the poles within every block. -/
def allocationEnumerationEquiv {m : B → ℕ} {n : ℕ} :
    (Σ a : SizedAllocation m n, AllocationEnumerations a) ≃ (AllocationNodes m ≃ Fin n) := by
  apply Equiv.ofBijective (fun z => assembleAllocationEquiv z.1 z.2)
  constructor
  · rintro ⟨a,g⟩ ⟨b,h⟩ he
    change assembleAllocationEquiv a g = assembleAllocationEquiv b h at he
    have hab : a=b := by
      rw [← allocationOfEquiv_assemble a g,← allocationOfEquiv_assemble b h,he]
    subst b
    have hgh : g=h := by
      funext b
      apply Equiv.ext
      intro i
      apply Subtype.ext
      exact congrArg (fun f : AllocationNodes m ≃ Fin n => f ⟨b,i⟩) he
    subst h
    rfl
  · intro e
    let a := allocationOfEquiv e
    let g : AllocationEnumerations a := fun b =>
      Equiv.ofBijective (equivFiberMap e b) (equivFiberMap_bijective e b)
    refine ⟨⟨a,g⟩,?_⟩
    apply Equiv.ext
    rintro ⟨b,i⟩
    rfl

/-- All bijections between two finite types are a torsor for one permutation group. -/
def equivalencesToPerm {I J : Type*} (e : I ≃ J) : (I ≃ J) ≃ Equiv.Perm I where
  toFun f := f.trans e.symm
  invFun p := p.trans e
  left_inv f := by ext i; simp
  right_inv p := by ext i; simp

lemma card_allocationEnumerations {m : B → ℕ} {n : ℕ} (a : SizedAllocation m n) :
    Fintype.card (AllocationEnumerations a) = ∏ b, (m b).factorial := by
  rw [Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro b _
  rw [Fintype.card_congr (equivalencesToPerm (allocationEnumeration a b).toEquiv),
    Fintype.card_perm,Fintype.card_fin]

/-- Exact labelled allocation count, stated multiplicatively to avoid
unproved integrality of a factorial quotient. Every block size is allowed. -/
theorem sizedAllocation_card_factorial {m : B → ℕ} {n : ℕ}
    (e : AllocationNodes m ≃ Fin n) :
    Fintype.card (SizedAllocation m n) * (∏ b, (m b).factorial) = n.factorial := by
  have h := Fintype.card_congr (allocationEnumerationEquiv (m := m) (n := n))
  rw [Fintype.card_sigma] at h
  simp only [card_allocationEnumerations,Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul] at h
  rw [Fintype.card_congr (equivalencesToPerm e),Fintype.card_perm,Fintype.card_congr e,
    Fintype.card_fin] at h
  exact h

end HydrologyTree
