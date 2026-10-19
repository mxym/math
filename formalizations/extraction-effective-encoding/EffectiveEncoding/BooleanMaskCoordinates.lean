import EffectiveEncoding.BinaryMaskPlanProgram

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- Real synchronized wire/Boolean-list visits. The constructor records the
executed keep/skip branch; no finite-set membership or numeric comparison is
used to select that branch. -/
inductive MaskCoordinateTrace where
  | done
  | keep : MaskCoordinateTrace → MaskCoordinateTrace
  | skip : MaskCoordinateTrace → MaskCoordinateTrace


def MaskCoordinateTrace.actions : MaskCoordinateTrace → ℕ
  | .done => 1
  | .keep tail => tail.actions+4
  | .skip tail => tail.actions+3

structure MaskCoordinateResult (α : Type*) where
  items : List α
  trace : MaskCoordinateTrace

/-- One parallel list pass, reading every available stored mask bit once.
The selected wire list inherits input order; sorting/minimum/erase are absent. -/
def maskCoordinateSelectProgram {α : Type*} : List α → List Bool → MaskCoordinateResult α
  | [],_ => ⟨[],.done⟩
  | _::_,[] => ⟨[],.done⟩
  | w::ws,b::bs =>
    let tail:=maskCoordinateSelectProgram ws bs
    if b then ⟨w::tail.items,.keep tail.trace⟩ else ⟨tail.items,.skip tail.trace⟩


theorem maskCoordinateSelectProgram_map {α : Type*} (wires : List α) (f : α → Bool) :
    (maskCoordinateSelectProgram wires (wires.map f)).items=wires.filter f := by
  induction wires with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons,maskCoordinateSelectProgram,List.filter_cons,ih]
    cases f w <;> rfl


theorem maskCoordinateSelectProgram_actions {α : Type*} (wires : List α) (bits : List Bool) :
    (maskCoordinateSelectProgram wires bits).trace.actions≤4*wires.length+1 := by
  induction wires generalizing bits with
  | nil => exact le_refl 1
  | cons w ws ih =>
    cases bits with
    | nil => simp [maskCoordinateSelectProgram,MaskCoordinateTrace.actions]
    | cons b bs =>
      have h:=ih bs
      cases b <;> simp only [maskCoordinateSelectProgram,Bool.false_eq_true,ite_false,ite_true,
        MaskCoordinateTrace.actions,List.length_cons] <;> omega

/-- Semantic list/function bridge; the actual selector consumes the stored
bit list and never evaluates a function by indexed list lookup. -/
theorem packedMask_finRange_map {n : ℕ} (mask : PackedBits n) :
    (List.finRange n).map (unpackBits mask)=mask.toList := by
  rw [←List.ofFn_eq_map,←List.Vector.toList_ofFn]
  simp only [unpackBits,List.Vector.ofFn_get]


def booleanMaskCoordinates {n : ℕ} (mask : PackedBits n) : MaskCoordinateResult (Fin n) :=
  maskCoordinateSelectProgram (List.finRange n) mask.toList


theorem booleanMaskCoordinates_items {n : ℕ} (mask : PackedBits n) :
    (booleanMaskCoordinates mask).items=(List.finRange n).filter (unpackBits mask) := by
  unfold booleanMaskCoordinates
  rw [←packedMask_finRange_map,maskCoordinateSelectProgram_map]

/-- Exact sorted-coordinate list. Sorting and the finite set occur only on
the proof/specification side of this equality, not in the value program. -/
theorem booleanMaskCoordinates_sortedMask {n : ℕ} (mask : PackedBits n) :
    (booleanMaskCoordinates mask).items=(maskOfBits (unpackBits mask)).sort (·≤·) := by
  rw [booleanMaskCoordinates_items]
  apply List.Pairwise.eq_of_mem_iff
    (List.Pairwise.filter _ (List.sortedLT_finRange n).pairwise)
    (Finset.sortedLT_sort _).pairwise
  intro a
  simp [maskOfBits]


theorem booleanMaskCoordinates_nodup {n : ℕ} (mask : PackedBits n) :
    (booleanMaskCoordinates mask).items.Nodup := by
  rw [booleanMaskCoordinates_items]
  exact (List.nodup_finRange n).filter _


theorem booleanMaskCoordinates_actions {n : ℕ} (mask : PackedBits n) :
    (booleanMaskCoordinates mask).trace.actions≤4*n+1 := by
  simpa only [booleanMaskCoordinates,List.length_finRange] using
    maskCoordinateSelectProgram_actions (List.finRange n) mask.toList

end EffectiveEncoding
