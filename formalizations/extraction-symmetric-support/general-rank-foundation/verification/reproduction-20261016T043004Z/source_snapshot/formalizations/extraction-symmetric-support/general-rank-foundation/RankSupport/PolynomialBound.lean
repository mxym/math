import RankSupport.RankBounds
import RankSupport.Invariance
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free

open scoped BigOperators
open Matrix Module

namespace ExtractionRankSupport

open SymmetricSupport

noncomputable section

/-- The actual rectangular tensor map, with s input coordinates per copy. -/
def rectangularTensor (D s k : ℕ) (A : Matrix (Fin D) (Fin s) ℂ) :
    Matrix (Word D k) (Word s k) ℂ := fun w v => ∏ i, A (w i) (v i)

def rectangularEntryEquiv (D s : ℕ) : Fin (D*s) ≃ (Fin D × Fin s) :=
  Fintype.equivOfCardEq (by simp)

def rectangularPairWord {D s k : ℕ} (w : Word D k) (v : Word s k) : Word (D*s) k :=
  fun i => (rectangularEntryEquiv D s).symm (w i, v i)

def rectangularEntryVector {D s : ℕ} (A : Matrix (Fin D) (Fin s) ℂ) : Fin (D*s) → ℂ :=
  fun i => A ((rectangularEntryEquiv D s) i).1 ((rectangularEntryEquiv D s) i).2

def rectangularContraction {D s k : ℕ} (v : Word s k) :
    (Word (D*s) k → ℂ) →ₗ[ℂ] (Word D k → ℂ) where
  toFun f w := f (rectangularPairWord w v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rectangularContraction_purePower {D s k : ℕ}
    (A : Matrix (Fin D) (Fin s) ℂ) (v : Word s k) :
    rectangularContraction v (purePower (D*s) k (rectangularEntryVector A)) =
      (rectangularTensor D s k A).col v := by
  ext w
  simp [rectangularContraction, purePower, rectangularPairWord, rectangularEntryVector,
    rectangularTensor, Matrix.col]

def rectangularColumnSpace {D s k : ℕ} (v : Word s k) : Submodule ℂ (Word D k → ℂ) :=
  (LinearMap.range (symmetricProjector (D*s) k).mulVecLin).map (rectangularContraction v)

theorem rectangularTensor_col_mem_columnSpace {D s k : ℕ}
    (A : Matrix (Fin D) (Fin s) ℂ) (v : Word s k) :
    (rectangularTensor D s k A).col v ∈ rectangularColumnSpace v := by
  have hp : purePower (D*s) k (rectangularEntryVector A) ∈
      LinearMap.range (symmetricProjector (D*s) k).mulVecLin :=
    ⟨_, symmetricProjector_fixes_purePower (D*s) k _⟩
  simpa only [rectangularColumnSpace, rectangularContraction_purePower] using
    (Submodule.mem_map_of_mem (f := rectangularContraction v) hp)

theorem finrank_rectangularColumnSpace_le {D s k : ℕ} (v : Word s k) :
    Module.finrank ℂ (rectangularColumnSpace (D := D) v) ≤ (D*s+k-1).choose k := by
  calc
    _ ≤ Module.finrank ℂ (LinearMap.range (symmetricProjector (D*s) k).mulVecLin) :=
      Submodule.finrank_map_le _ _
    _ = (symmetricProjector (D*s) k).rank := rfl
    _ = _ := symmetricProjector_rank_choose (D*s) k

def rectangularUniversalSpace (D k s : ℕ) : Submodule ℂ (Word D k → ℂ) :=
  (Finset.univ : Finset (Word s k)).sup (fun v => rectangularColumnSpace v)

theorem rectangularTensor_col_mem_universalSpace {D s k : ℕ}
    (A : Matrix (Fin D) (Fin s) ℂ) (v : Word s k) :
    (rectangularTensor D s k A).col v ∈ rectangularUniversalSpace D k s := by
  exact (Finset.le_sup (f := fun v => rectangularColumnSpace v) (Finset.mem_univ v))
    (rectangularTensor_col_mem_columnSpace A v)

theorem finrank_finite_sup_rectangularColumnSpace_le {D s k : ℕ}
    (T : Finset (Word s k)) :
    Module.finrank ℂ (T.sup (fun v => rectangularColumnSpace (D := D) v) :
      Submodule ℂ (Word D k → ℂ)) ≤
      T.card * (D*s+k-1).choose k := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert v T hv ih =>
    rw [Finset.sup_insert]
    calc
      _ ≤ Module.finrank ℂ (rectangularColumnSpace (D := D) v) +
          Module.finrank ℂ (T.sup (fun v => rectangularColumnSpace (D := D) v) :
            Submodule ℂ (Word D k → ℂ)) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ (D*s+k-1).choose k + T.card * (D*s+k-1).choose k :=
        Nat.add_le_add (finrank_rectangularColumnSpace_le v) ih
      _ = (insert v T).card * (D*s+k-1).choose k := by
        rw [Finset.card_insert_of_notMem hv]
        ring

theorem finrank_rectangularUniversalSpace_le (D k s : ℕ) :
    Module.finrank ℂ (rectangularUniversalSpace D k s) ≤
      s ^ k * (D*s+k-1).choose k := by
  calc
    _ ≤ (Finset.univ : Finset (Word s k)).card * (D*s+k-1).choose k :=
      finrank_finite_sup_rectangularColumnSpace_le (D := D) (s := s) (k := k) _
    _ = _ := by simp only [Finset.card_univ, Word, Fintype.card_fun, Fintype.card_fin]

theorem rectangularTensor_mulVec_productVector (D s k : ℕ)
    (A : Matrix (Fin D) (Fin s) ℂ) (z : Fin k → Fin s → ℂ) :
    rectangularTensor D s k A *ᵥ productVector s k z =
      productVector D k (fun i => A *ᵥ z i) := by
  ext w
  simp only [Matrix.mulVec, dotProduct, rectangularTensor, productVector]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro v _
  exact (Finset.prod_mul_distrib :
    (∏ i, A (w i) (v i) * z i (v i)) =
      (∏ i, A (w i) (v i)) * ∏ i, z i (v i)).symm

/-- A low-dimensional actual factor family admits an actual rectangular
matrix factorization, obtained internally from an injection and linear left
inverse. No basis certificate is requested from the caller. -/
theorem exists_rectangular_factorization (D k s : ℕ) (z : Fin k → Fin D → ℂ)
    (hz : Module.finrank ℂ (Submodule.span ℂ (Set.range z)) ≤ s) :
    ∃ (A : Matrix (Fin D) (Fin s) ℂ) (c : Fin k → Fin s → ℂ),
      ∀ i, A *ᵥ c i = z i := by
  classical
  let S := Submodule.span ℂ (Set.range z)
  have hd : Module.finrank ℂ S ≤ Module.finrank ℂ (Fin s → ℂ) := by simpa using hz
  obtain ⟨f, hf⟩ := (finrank_le_iff_exists_linearMap (R := ℂ) (M := S)
    (M' := Fin s → ℂ)).mp hd
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  let L : (Fin s → ℂ) →ₗ[ℂ] (Fin D → ℂ) := S.subtype.comp g
  let A := LinearMap.toMatrix' L
  have hA : A.mulVecLin = L := Matrix.toLin'_toMatrix' L
  have hzi (i : Fin k) : z i ∈ S := Submodule.subset_span ⟨i, rfl⟩
  refine ⟨A, fun i => f ⟨z i, hzi i⟩, ?_⟩
  intro i
  change A.mulVecLin (f ⟨z i, hzi i⟩) = z i
  rw [hA]
  have h := congrArg (fun l : S →ₗ[ℂ] S => l ⟨z i, hzi i⟩) hg
  exact congrArg Subtype.val h

theorem rankBudgetSpace_le_rectangularUniversalSpace (D k s : ℕ) :
    rankBudgetSpace D k s ≤ rectangularUniversalSpace D k s := by
  apply Submodule.span_le.mpr
  rintro v ⟨z, hz, rfl⟩
  obtain ⟨A, c, hc⟩ := exists_rectangular_factorization D k s z hz
  have hz' : (fun i => A *ᵥ c i) = z := funext hc
  rw [← hz', ← rectangularTensor_mulVec_productVector]
  have hRange : LinearMap.range (rectangularTensor D s k A).mulVecLin ≤
      rectangularUniversalSpace D k s := by
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro v ⟨w, rfl⟩
    exact rectangularTensor_col_mem_universalSpace A w
  exact hRange ⟨productVector s k c, rfl⟩

/-- An explicit polynomial overhead above s^k, proved without any numerical
Schur dimension formula. It is not the manuscript's sharp polynomial factor. -/
theorem rankBudgetProjector_rank_le_polynomial (D k s : ℕ) :
    (rankBudgetProjector D k s).rank ≤ s ^ k * (D*s+k-1).choose k := by
  rw [rankBudgetProjector_rank]
  exact (Submodule.finrank_mono (rankBudgetSpace_le_rectangularUniversalSpace D k s)).trans
    (finrank_rectangularUniversalSpace_le D k s)

end
end ExtractionRankSupport
