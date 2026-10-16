import SymmetricSupport.FinitePartition
import Mathlib.Data.Sym.Card
import Mathlib.Algebra.BigOperators.Group.List.Basic

open scoped BigOperators
open Matrix

namespace SymmetricSupport

/-- Computational basis of an actual k-fold D-level tensor power. -/
abbrev Word (D k : ℕ) := Fin k → Fin D

/-- Occupations identify computational words up to permutation. -/
def occupation (D k : ℕ) (w : Word D k) : Sym (Fin D) k :=
  Sym.ofVector (List.Vector.ofFn w)

theorem occupation_surjective (D k : ℕ) : Function.Surjective (occupation D k) := by
  intro s
  obtain ⟨l, hl⟩ := Quotient.exists_rep s.val
  have hlen : l.length = k := by
    calc
      l.length = Multiset.card (l : Multiset (Fin D)) := rfl
      _ = Multiset.card s.val := congrArg Multiset.card hl
      _ = k := s.property
  let v : List.Vector (Fin D) k := ⟨l, hlen⟩
  refine ⟨v.get, ?_⟩
  simp only [occupation, List.Vector.ofFn_get]
  exact Subtype.ext hl

/-- The actual tensor-product amplitudes of an arbitrary single-system vector. -/
def purePower (D k : ℕ) (z : Fin D → ℂ) : Word D k → ℂ :=
  fun w => ∏ i, z (w i)

theorem purePower_equal_occupation (D k : ℕ) (z : Fin D → ℂ)
    (v w : Word D k) (h : occupation D k v = occupation D k w) :
    purePower D k z v = purePower D k z w := by
  have hm : ((List.ofFn v : List (Fin D)) : Multiset (Fin D)) = List.ofFn w := by
    have hm0 := congrArg Subtype.val h
    change (((List.Vector.ofFn v).toList : List (Fin D)) : Multiset (Fin D)) =
      (((List.Vector.ofFn w).toList : List (Fin D)) : Multiset (Fin D)) at hm0
    simpa only [List.Vector.toList_ofFn] using hm0
  have hp := congrArg (fun m : Multiset (Fin D) => (m.map z).prod) hm
  simpa [purePower, List.prod_ofFn] using hp

/-- A fixed projector on the original D^k coordinate space, independent of z. -/
noncomputable def symmetricProjector (D k : ℕ) : Matrix (Word D k) (Word D k) ℂ :=
  partitionProjector (occupation D k)

theorem symmetricProjector_hermitian (D k : ℕ) :
    (symmetricProjector D k).IsHermitian :=
  partitionProjector_hermitian _

theorem symmetricProjector_idempotent (D k : ℕ) :
    symmetricProjector D k * symmetricProjector D k = symmetricProjector D k :=
  partitionProjector_idempotent _ (occupation_surjective D k)

theorem symmetricProjector_fixes_purePower (D k : ℕ) (z : Fin D → ℂ) :
    (symmetricProjector D k).mulVec (purePower D k z) = purePower D k z :=
  partitionProjector_mulVec_constant _ (occupation_surjective D k) _
    (purePower_equal_occupation D k z)

theorem symmetricProjector_rank_choose (D k : ℕ) :
    (symmetricProjector D k).rank = (D + k - 1).choose k := by
  rw [symmetricProjector, partitionProjector_rank _ (occupation_surjective D k)]
  simpa using Sym.card_sym_eq_choose (α := Fin D) k

theorem symmetricProjector_rank_choose_complement (D k : ℕ) (hD : 0 < D) :
    (symmetricProjector D k).rank = (k + D - 1).choose (D - 1) := by
  rw [symmetricProjector_rank_choose]
  have h : k ≤ D + k - 1 := by omega
  rw [← Nat.choose_symm h]
  congr 1 <;> omega

end SymmetricSupport
