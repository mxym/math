import EffectiveEncoding.NativeBooleanRankProgram
import CircuitNumerical.ListAssemblyPrograms

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- The carried Nat count is used by the unchanged native descriptor interface.
The Boolean encoder is stored alongside it and is never recovered by decoding.
Nat successor/control costs are separate from the traces below. -/
structure SavedCountWord where
  count : ℕ
  encoding : UnaryWordEncodingResult


def savedCountSuccessor (previous : SavedCountWord) : SavedCountWord :=
  let increment:=binaryAddProgram previous.encoding.bits [true] false
  let trimmed:=binaryTrimProgram increment.bits
  ⟨previous.count+1,⟨trimmed.bits,.increment previous.encoding.trace increment.trace trimmed.trace⟩⟩


theorem savedCountSuccessor_exact (n : ℕ) :
    savedCountSuccessor ⟨n,unaryWordEncoding n⟩=⟨n+1,unaryWordEncoding (n+1)⟩ := rfl

structure BinaryCountRangeResult where
  items : List SavedCountWord
  current : SavedCountWord
  copyTrace : ListAssemblyTrace

/-- Inclusive ordered range. Each successor performs exactly one real Boolean
increment/trim; saved earlier count words are reused by reference. Concrete
append calls retain their copy traces. No Nat.bits or semantic decoding occurs. -/
def binaryCountRangeProgram : ℕ → BinaryCountRangeResult
  | 0 =>
    let zero : SavedCountWord:=⟨0,⟨[],.zero⟩⟩
    ⟨[zero],zero,.done⟩
  | n+1 =>
    let previous:=binaryCountRangeProgram n
    let next:=savedCountSuccessor previous.current
    let output:=listAppendProgram previous.items [next]
    ⟨output.value,next,.sequence previous.copyTrace output.trace⟩


theorem binaryCountRangeProgram_current (n : ℕ) :
    (binaryCountRangeProgram n).current=⟨n,unaryWordEncoding n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [binaryCountRangeProgram,ih,savedCountSuccessor_exact]

/-- Exact stored list, including each encoding record and its original trace,
not just a bijection or an equality after interpreting Boolean values. -/
theorem binaryCountRangeProgram_items (n : ℕ) :
    (binaryCountRangeProgram n).items=
      (List.range (n+1)).map (fun j => (⟨j,unaryWordEncoding j⟩ : SavedCountWord)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [binaryCountRangeProgram,listAppendProgram_value,binaryCountRangeProgram_current,
      savedCountSuccessor_exact,ih,List.range_succ,List.map_append,List.map_cons,List.map_nil]


theorem binaryCountRangeProgram_length (n : ℕ) :
    (binaryCountRangeProgram n).items.length=n+1 := by
  rw [binaryCountRangeProgram_items,List.length_map,List.length_range]


theorem binaryCountRangeProgram_counts (n : ℕ) :
    ((binaryCountRangeProgram n).items.map SavedCountWord.count)=List.range (n+1) := by
  simp only [binaryCountRangeProgram_items,List.map_map,Function.comp_def]
  exact List.map_id _


def BinaryCountRangeResult.incrementTrimActions (r : BinaryCountRangeResult) : ℕ :=
  r.current.encoding.trace.incrementTrimActions


theorem binaryCountRangeProgram_incrementCount (n : ℕ) :
    (binaryCountRangeProgram n).current.encoding.trace.incrementCount=n := by
  rw [binaryCountRangeProgram_current]
  exact unaryWordEncoding_incrementCount n


theorem binaryCountRangeProgram_incrementTrimActions (n : ℕ) :
    (binaryCountRangeProgram n).incrementTrimActions≤32*(n+1)^2 := by
  unfold BinaryCountRangeResult.incrementTrimActions
  rw [binaryCountRangeProgram_current]
  exact unaryWordEncoding_incrementTrimActions n


theorem binaryCountRangeProgram_copyActions (n : ℕ) :
    (binaryCountRangeProgram n).copyTrace.actions≤8*(n+1)^2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    simp only [binaryCountRangeProgram,ListAssemblyTrace.actions,listAppendProgram_actions,
      binaryCountRangeProgram_length]
    nlinarith

/-- Two concrete trace models only. The projection's arithmetic and Nat-fuel
control, carried-count successor and general allocation remain separate. -/
def BinaryCountRangeResult.actions (r : BinaryCountRangeResult) : ℕ :=
  r.incrementTrimActions+r.copyTrace.actions


theorem binaryCountRangeProgram_actions (n : ℕ) :
    (binaryCountRangeProgram n).actions≤40*(n+1)^2 := by
  exact (Nat.add_le_add (binaryCountRangeProgram_incrementTrimActions n)
    (binaryCountRangeProgram_copyActions n)).trans_eq (by ring)

end EffectiveEncoding
