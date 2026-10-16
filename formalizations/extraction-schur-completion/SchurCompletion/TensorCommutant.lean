import SchurCompletion.HaarPurity
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Basic

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSchur

open SymmetricSupport ExtractionSpectrum

noncomputable section

theorem count_ofFn_eq_sum {E k : ℕ} (w : Fin k → Fin E) (a : Fin E) :
    (List.ofFn w).count a = ∑ i : Fin k, if w i = a then 1 else 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, Fin.sum_univ_succ]
    simp only [List.count_cons, beq_iff_eq, ih]
    split_ifs <;> omega

theorem occupation_fiber_card {E k : ℕ} (w : Word E k) (a : Fin E) :
    Fintype.card {i : Fin k // w i = a} =
      (List.ofFn w).count a := by
  rw [count_ofFn_eq_sum]
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Equal actual occupation labels are exactly simultaneous permutations
of the actual tensor positions. -/
theorem exists_position_permutation_of_occupation_eq {E k : ℕ} (v w : Word E k)
    (h : occupation E k v = occupation E k w) :
    ∃ σ : Equiv.Perm (Fin k), ∀ i, v (σ i) = w i := by
  classical
  have hm : ((List.ofFn v : List (Fin E)) : Multiset (Fin E)) = List.ofFn w := by
    have hm0 := congrArg Subtype.val h
    change (((List.Vector.ofFn v).toList : List (Fin E)) : Multiset (Fin E)) =
      (((List.Vector.ofFn w).toList : List (Fin E)) : Multiset (Fin E)) at hm0
    simpa only [List.Vector.toList_ofFn] using hm0
  have hcard (a : Fin E) : Fintype.card {i : Fin k // w i = a} =
      Fintype.card {i : Fin k // v i = a} := by
    rw [occupation_fiber_card, occupation_fiber_card]
    simpa only [Multiset.coe_count] using (congrArg (Multiset.count a) hm).symm
  let e (a : Fin E) := Fintype.equivOfCardEq (hcard a)
  exact ⟨Equiv.ofFiberEquiv e, Equiv.ofFiberEquiv_map e⟩

def entryEquiv (D : ℕ) : Fin (D*D) ≃ Fin D × Fin D :=
  Fintype.equivOfCardEq (by simp)

def matrixEntryVector (D : ℕ) (M : Matrix (Fin D) (Fin D) ℂ) : Fin (D*D) → ℂ :=
  fun t => M ((entryEquiv D) t).1 ((entryEquiv D) t).2

def flattenTensorMatrix (D k : ℕ) :
    Matrix (Word D k) (Word D k) ℂ ≃ₗ[ℂ] (Word (D*D) k → ℂ) where
  toFun M t := M (fun i => ((entryEquiv D) (t i)).1) (fun i => ((entryEquiv D) (t i)).2)
  invFun f x y := f (fun i => (entryEquiv D).symm (x i, y i))
  left_inv M := by ext x y; simp
  right_inv f := by ext t; simp
  map_add' M N := rfl
  map_smul' c M := rfl

theorem flatten_tensorMatrix (D k : ℕ) (M : Matrix (Fin D) (Fin D) ℂ) :
    flattenTensorMatrix D k (tensorMatrix M k) = purePower (D*D) k (matrixEntryVector D M) := rfl

theorem matrixEntryVector_surjective (D : ℕ) : Function.Surjective (matrixEntryVector D) := by
  intro z
  refine ⟨fun i j => z ((entryEquiv D).symm (i,j)), ?_⟩
  ext t
  simp [matrixEntryVector]

/-- The concrete linear span of genuine one-copy matrix tensor powers. -/
def tensorPowerSpan (D k : ℕ) : Submodule ℂ (Matrix (Word D k) (Word D k) ℂ) :=
  Submodule.span ℂ (Set.range (fun M : Matrix (Fin D) (Fin D) ℂ => tensorMatrix M k))

theorem flatten_tensorPowerSpan (D k : ℕ) :
    (tensorPowerSpan D k).map (flattenTensorMatrix D k).toLinearMap =
      LinearMap.range (symmetricProjector (D*D) k).mulVecLin := by
  rw [tensorPowerSpan, Submodule.map_span, symmetricProjector_range_eq_purePower_span]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨M,rfl⟩,rfl⟩
    exact ⟨matrixEntryVector D M, rfl⟩
  · rintro ⟨z,rfl⟩
    obtain ⟨M,rfl⟩ := matrixEntryVector_surjective D z
    exact ⟨tensorMatrix M k, ⟨M,rfl⟩, rfl⟩

/-- Actual simultaneous permutation invariance characterizes the full span
of tensor powers. This is the centralizer half of Schur--Weyl, before
classification by Young diagrams. -/
theorem mem_tensorPowerSpan_iff_position_invariant (D k : ℕ)
    (M : Matrix (Word D k) (Word D k) ℂ) :
    M ∈ tensorPowerSpan D k ↔ ∀ σ : Equiv.Perm (Fin k), ∀ x y : Word D k,
      M (x ∘ σ) (y ∘ σ) = M x y := by
  constructor
  · intro hM σ x y
    induction hM using Submodule.span_induction with
    | mem N hN =>
      obtain ⟨N,rfl⟩ := hN
      exact Equiv.prod_comp σ (fun i => N (x i) (y i))
    | zero => rfl
    | add N Q hN hQ ihN ihQ => exact congrArg₂ (·+·) ihN ihQ
    | smul c N hN ihN => exact congrArg (c*·) ihN
  · intro hM
    have hf : flattenTensorMatrix D k M ∈
        LinearMap.range (symmetricProjector (D*D) k).mulVecLin := by
      refine ⟨flattenTensorMatrix D k M, ?_⟩
      apply partitionProjector_mulVec_constant _ (occupation_surjective (D*D) k)
      intro v w hvw
      obtain ⟨σ,hσ⟩ := exists_position_permutation_of_occupation_eq v w hvw
      have h := hM σ
        (fun i => ((entryEquiv D) (v i)).1) (fun i => ((entryEquiv D) (v i)).2)
      change M (fun i => ((entryEquiv D) (v (σ i))).1)
        (fun i => ((entryEquiv D) (v (σ i))).2) = _ at h
      simp only [hσ] at h
      exact h.symm
    rw [← flatten_tensorPowerSpan] at hf
    obtain ⟨N,hN,hNM⟩ := hf
    have heq : N = M := (flattenTensorMatrix D k).injective hNM
    exact heq ▸ hN

end
end ExtractionSchur
