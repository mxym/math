import SymmetricSupport.Occupation
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! A standard polynomial-orbit mechanism for universal compression, stated
on the actual tensor coordinates. It is a foundation for the universal protocol,
not an assertion that the manuscript's full Schur decomposition is formalized. -/
open scoped BigOperators
open Matrix SymmetricSupport Module
namespace UniversalOrbit
noncomputable section

def entryEquiv (D : ℕ) : Fin (D * D) ≃ (Fin D × Fin D) :=
  Fintype.equivOfCardEq (by simp)

def pairWord {D k : ℕ} (x y : Word D k) : Word (D * D) k :=
  fun i => (entryEquiv D).symm (x i, y i)

def entryVector {D : ℕ} (M : Matrix (Fin D) (Fin D) ℂ) : Fin (D*D) → ℂ :=
  fun i => M ((entryEquiv D) i).1 ((entryEquiv D) i).2

/-- The actual k-fold matrix action, including arbitrary nonunitary matrices. -/
def tensorAction {D k : ℕ} (M : Matrix (Fin D) (Fin D) ℂ) (v : Word D k → ℂ) :
    Word D k → ℂ := fun x => ∑ y, (∏ i, M (x i) (y i)) * v y

/-- Contract a tensor of matrix-entry coordinates against a fixed input vector. -/
def contraction {D k : ℕ} (v : Word D k → ℂ) :
    (Word (D*D) k → ℂ) →ₗ[ℂ] (Word D k → ℂ) where
  toFun f x := ∑ y, f (pairWord x y) * v y
  map_add' f g := by
    ext x
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' c f := by
    ext x
    simp [smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem contraction_purePower {D k : ℕ} (M : Matrix (Fin D) (Fin D) ℂ)
    (v : Word D k → ℂ) :
    contraction v (purePower (D*D) k (entryVector M)) = tensorAction M v := by
  ext x
  simp [contraction, purePower, pairWord, entryVector, tensorAction]

/-- A fixed polynomial-size space containing the whole matrix tensor orbit. -/
def orbitSpace {D k : ℕ} (v : Word D k → ℂ) : Submodule ℂ (Word D k → ℂ) :=
  (LinearMap.range (symmetricProjector (D*D) k).mulVecLin).map (contraction v)

theorem tensorAction_mem_orbitSpace {D k : ℕ}
    (M : Matrix (Fin D) (Fin D) ℂ) (v : Word D k → ℂ) :
    tensorAction M v ∈ orbitSpace v := by
  have hp : purePower (D*D) k (entryVector M) ∈
      LinearMap.range (symmetricProjector (D*D) k).mulVecLin :=
    ⟨_, symmetricProjector_fixes_purePower (D*D) k (entryVector M)⟩
  simpa only [orbitSpace, contraction_purePower] using
    (Submodule.mem_map_of_mem (f := contraction v) hp)

theorem finrank_orbitSpace_le {D k : ℕ} (v : Word D k → ℂ) :
    Module.finrank ℂ (orbitSpace v) ≤ (D*D+k-1).choose k := by
  calc
    _ ≤ Module.finrank ℂ (LinearMap.range (symmetricProjector (D*D) k).mulVecLin) :=
      Submodule.finrank_map_le _ _
    _ = (symmetricProjector (D*D) k).rank := rfl
    _ = _ := symmetricProjector_rank_choose (D*D) k

/-- A single known space for every matrix orbit of every word in S. -/
def universalSpace {D k : ℕ} (S : Finset (Word D k)) : Submodule ℂ (Word D k → ℂ) :=
  S.sup (fun x => orbitSpace (Pi.single x (1 : ℂ)))

theorem tensorAction_single_mem_universalSpace {D k : ℕ}
    (S : Finset (Word D k)) (x : Word D k) (hx : x ∈ S)
    (M : Matrix (Fin D) (Fin D) ℂ) :
    tensorAction M (Pi.single x 1) ∈ universalSpace S := by
  exact (Finset.le_sup (f := fun x => orbitSpace (Pi.single x (1 : ℂ))) hx)
    (tensorAction_mem_orbitSpace M _)

theorem universalSpace_mono {D k : ℕ} {S T : Finset (Word D k)} (h : S ⊆ T) :
    universalSpace S ≤ universalSpace T := by
  exact Finset.sup_mono h

theorem finrank_universalSpace_le {D k : ℕ} (S : Finset (Word D k)) :
    Module.finrank ℂ (universalSpace S) ≤ S.card * (D*D+k-1).choose k := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    change Module.finrank ℂ ((∅ : Finset (Word D k)).sup
      (fun x => orbitSpace (Pi.single x (1 : ℂ))) : Submodule ℂ (Word D k → ℂ)) ≤ _
    rw [Finset.sup_empty, finrank_bot]
    simp
  | @insert x S hx ih =>
    change Module.finrank ℂ ((insert x S).sup (fun x => orbitSpace (Pi.single x (1 : ℂ))) :
      Submodule ℂ (Word D k → ℂ)) ≤ _
    rw [Finset.sup_insert]
    calc
      _ ≤ Module.finrank ℂ (orbitSpace (Pi.single x 1)) +
          Module.finrank ℂ (universalSpace S) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ (D*D+k-1).choose k + S.card * (D*D+k-1).choose k :=
        Nat.add_le_add (finrank_orbitSpace_le _) ih
      _ = (insert x S).card * (D*D+k-1).choose k := by
        rw [Finset.card_insert_of_notMem hx]
        ring

end
end UniversalOrbit
