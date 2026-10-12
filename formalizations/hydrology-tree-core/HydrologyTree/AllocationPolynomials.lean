import HydrologyTree.SizedSpectralAllocation
import HydrologyTree.StieltjesReindex

/-! Canonical block polynomials of a labelled pole allocation. The label data
are recovered from actual polynomial roots, not postulated as extra observations. -/
open Polynomial
noncomputable section
namespace HydrologyTree

variable {B : Type*} [Fintype B] [DecidableEq B] {m : B → ℕ} {n : ℕ}

def allocatedRates (b : Fin n → ℝ) (a : SizedAllocation m n) (c : B) : Fin (m c) → ℝ :=
  fun i => b (allocationEquiv a ⟨c,i⟩)

def allocatedDenominator (b : Fin n → ℝ) (a : SizedAllocation m n) (c : B) : ℝ[X] :=
  stieltjesDenominator (allocatedRates b a c)

lemma allocationEquiv_mem_iff (a : SizedAllocation m n) (c : B) (i : Fin n) :
    (∃ j : Fin (m c), allocationEquiv a ⟨c,j⟩=i) ↔ a.val i=c := by
  constructor
  · rintro ⟨j,rfl⟩
    exact allocationEquiv_label a c j
  · intro hi
    obtain ⟨j,hj⟩ := (allocationEnumeration a c).surjective ⟨i,hi⟩
    exact ⟨j,congrArg Subtype.val hj⟩

/-- Membership in a labelled allocation block is equivalent to an actual zero
of its monic polynomial at the corresponding reference pole. -/
theorem allocatedDenominator_eval_zero_iff (b : Fin n → ℝ) (hb : Function.Injective b)
    (a : SizedAllocation m n) (c : B) (i : Fin n) :
    (allocatedDenominator b a c).eval (-b i)=0 ↔ a.val i=c := by
  rw [allocatedDenominator,eval_stieltjesDenominator,Finset.prod_eq_zero_iff,
    ← allocationEquiv_mem_iff a c i]
  constructor
  · rintro ⟨j,_,hj⟩
    refine ⟨j,hb ?_⟩
    change -b i+b (allocationEquiv a ⟨c,j⟩)=0 at hj
    linarith
  · rintro ⟨j,hj⟩
    exact ⟨j,Finset.mem_univ j,by simp [allocatedRates,hj]⟩

/-- Distinct labelled allocations cannot have the same complete child factors. -/
theorem allocatedDenominators_injective (b : Fin n → ℝ) (hb : Function.Injective b) :
    Function.Injective (fun a : SizedAllocation m n => allocatedDenominator b a) := by
  intro a d h
  change allocatedDenominator b a = allocatedDenominator b d at h
  apply Subtype.ext
  funext i
  have hh : (allocatedDenominator b a (a.val i)).eval (-b i)=0 :=
    (allocatedDenominator_eval_zero_iff b hb a (a.val i) i).mpr rfl
  rw [congrFun h (a.val i)] at hh
  exact ((allocatedDenominator_eval_zero_iff b hb d (a.val i) i).mp hh).symm

/-- Internal pole order is immaterial: the canonical block has exactly the
polynomial determined by any bijection inducing the same allocation. -/
theorem allocatedDenominator_of_equiv (b : Fin n → ℝ)
    (e : AllocationNodes m ≃ Fin n) (c : B) :
    allocatedDenominator b (allocationOfEquiv e) c =
      stieltjesDenominator (fun i : Fin (m c) => b (e ⟨c,i⟩)) := by
  let a := allocationOfEquiv e
  let f : Fin (m c) ≃ AllocationFiber a c :=
    Equiv.ofBijective (equivFiberMap e c) (equivFiberMap_bijective e c)
  have h1 := stieltjesDenominator_reindex (allocationEnumeration a c).toEquiv
    (fun z : AllocationFiber a c => b z.val)
  have h2 := stieltjesDenominator_reindex f (fun z : AllocationFiber a c => b z.val)
  exact h1.trans h2.symm

end HydrologyTree
