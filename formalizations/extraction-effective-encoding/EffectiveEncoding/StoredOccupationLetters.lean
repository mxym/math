import EffectiveEncoding.RetainedOccupationFilter
import EffectiveEncoding.BooleanMaskCoordinates

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

inductive WordPresenceTrace where
  | empty
  | nonempty

structure WordPresenceResult where
  present : Bool
  trace : WordPresenceTrace

/-- A stored canonical word is tested by its list constructor, with no Nat
 value/comparison, length, or indexed lookup on the executable path. -/
def wordPresenceProgram : List Bool → WordPresenceResult
  | [] => ⟨false,.empty⟩
  | _::_ => ⟨true,.nonempty⟩


def WordPresenceTrace.actions : WordPresenceTrace → ℕ
  | .empty => 3
  | .nonempty => 3


theorem wordPresenceProgram_actions (bits : List Bool) :
    (wordPresenceProgram bits).trace.actions=3 := by
  cases bits <;> rfl


theorem wordPresenceProgram_correct (bits : List Bool) (h : BinaryWordCanonical bits) :
    (wordPresenceProgram bits).present=decide (0<binaryWordValue bits) := by
  cases bits with
  | nil => rfl
  | cons b bs =>
    have hn : binaryWordValue (b::bs)≠0 := by
      intro hz
      have he:=(binaryWordCanonical_zero_iff (b::bs) h).mp hz
      contradiction
    simpa only [wordPresenceProgram,decide_eq_true (Nat.pos_of_ne_zero hn)]

structure StoredOccupationLettersResult where
  difference : BinaryWordSubtractionResult
  remaining : BinaryWordTrimResult
  first : WordPresenceResult
  second : WordPresenceResult
  third : WordPresenceResult
  fourth : WordPresenceResult
  selected : MaskCoordinateResult (Fin 4)

/-- The three count words and total word are read from already executed range
 and accepted-filter records. Only the remaining count needs new arithmetic:
 one actual ripple subtraction and one trim, both retained. The four actual
 constructor tests control a single ordered fixed-letter selection pass. -/
def storedOccupationLettersProgram (bound : List Bool) (t : NativeTripleWords)
    (totalBits : List Bool) : StoredOccupationLettersResult :=
  let difference:=binarySubtractProgram bound totalBits false
  let remaining:=binaryTrimProgram difference.bits
  let first:=wordPresenceProgram t.first.bits
  let second:=wordPresenceProgram t.second.bits
  let third:=wordPresenceProgram t.third.bits
  let fourth:=wordPresenceProgram remaining.bits
  let selected:=maskCoordinateSelectProgram ([0,1,2,3] : List (Fin 4))
    [first.present,second.present,third.present,fourth.present]
  ⟨difference,remaining,first,second,third,fourth,selected⟩


def StoredOccupationLettersResult.items (r : StoredOccupationLettersResult) : List (Fin 4) :=
  r.selected.items


theorem storedOccupationLettersProgram_remaining {k : ℕ} (x : NativeOccupation k)
    (bound totalBits : List Bool) (t : NativeTripleWords)
    (hb : binaryWordValue bound=k) (ht : binaryWordValue totalBits=total x.1) :
    binaryWordValue (storedOccupationLettersProgram bound t totalBits).remaining.bits=k-total x.1 := by
  have hv:=binarySubtractProgram_nonnegative_value bound totalBits false
    (by simpa only [binaryBitValue,Nat.add_zero,hb,ht] using x.2)
  simp only [binaryBitValue,Nat.sub_zero] at hv
  change binaryWordValue (binaryTrimProgram (binarySubtractProgram bound totalBits false).bits).bits=_
  rw [binaryTrimProgram_value,hv,hb,ht]


theorem storedOccupationLettersProgram_filter {k : ℕ} (x : NativeOccupation k)
    (bound totalBits : List Bool) (t : NativeTripleWords)
    (hb : binaryWordValue bound=k) (ht : binaryWordValue totalBits=total x.1)
    (hv : t.value=x.1)
    (hc : BinaryWordCanonical t.first.bits ∧ BinaryWordCanonical t.second.bits ∧
      BinaryWordCanonical t.third.bits) :
    (storedOccupationLettersProgram bound t totalBits).items=
      ([0,1,2,3] : List (Fin 4)).filter (fun a => decide (0<nativeMass x a)) := by
  have h1 : binaryWordValue t.first.bits=x.1.1 := congrArg Prod.fst hv
  have h2 : binaryWordValue t.second.bits=x.1.2.1 := congrArg (fun z : Triple => z.2.1) hv
  have h3 : binaryWordValue t.third.bits=x.1.2.2 := congrArg (fun z : Triple => z.2.2) hv
  have h4:=storedOccupationLettersProgram_remaining x bound totalBits t hb ht
  have p1:=wordPresenceProgram_correct t.first.bits hc.1
  have p2:=wordPresenceProgram_correct t.second.bits hc.2.1
  have p3:=wordPresenceProgram_correct t.third.bits hc.2.2
  have p4:=wordPresenceProgram_correct
    (binaryTrimProgram (binarySubtractProgram bound totalBits false).bits).bits
    (binaryTrimProgram_canonical _)
  change (maskCoordinateSelectProgram ([0,1,2,3] : List (Fin 4))
    [(wordPresenceProgram t.first.bits).present,(wordPresenceProgram t.second.bits).present,
      (wordPresenceProgram t.third.bits).present,
      (wordPresenceProgram (binaryTrimProgram (binarySubtractProgram bound totalBits false).bits).bits).present]).items=_
  rw [p1,p2,p3,p4,h1,h2,h3]
  change binaryWordValue (binaryTrimProgram (binarySubtractProgram bound totalBits false).bits).bits=_ at h4
  rw [h4]
  have hm : [decide (0<x.1.1),decide (0<x.1.2.1),decide (0<x.1.2.2),decide (0<k-total x.1)]=
      ([0,1,2,3] : List (Fin 4)).map (fun a => decide (0<nativeMass x a)) := by
    simp [nativeMass]
  rw [hm,maskCoordinateSelectProgram_map]

/-- Exact old ordered finite-set specification; the old Finset/filter/sort is
 only on this proof's specification side, absent from the executable program. -/
theorem storedOccupationLettersProgram_sorted {k : ℕ} (x : NativeOccupation k)
    (bound totalBits : List Bool) (t : NativeTripleWords)
    (hb : binaryWordValue bound=k) (ht : binaryWordValue totalBits=total x.1)
    (hv : t.value=x.1)
    (hc : BinaryWordCanonical t.first.bits ∧ BinaryWordCanonical t.second.bits ∧
      BinaryWordCanonical t.third.bits) :
    (storedOccupationLettersProgram bound t totalBits).items=(nativeSelected x).sort (·≤·) := by
  rw [storedOccupationLettersProgram_filter x bound totalBits t hb ht hv hc]
  apply List.Pairwise.eq_of_mem_iff
    (List.Pairwise.filter _ (by decide : ([0,1,2,3] : List (Fin 4)).Pairwise (·<·)))
    (Finset.sortedLT_sort _).pairwise
  intro a
  have hm : a∈([0,1,2,3] : List (Fin 4)) := by fin_cases a <;> decide
  simp [nativeSelected,hm]

/-- Only the retained subtraction, trim, presence branches and selection trace
 are charged. Stored-input preparation, host control and counter work remain
 separate, and the two upstream additions are not charged a second time. -/
def StoredOccupationLettersResult.actions (r : StoredOccupationLettersResult) : ℕ :=
  r.difference.trace.actions+r.remaining.trace.actions+r.first.trace.actions+
    r.second.trace.actions+r.third.trace.actions+r.fourth.trace.actions+r.selected.trace.actions


theorem storedOccupationLettersProgram_actions (bound totalBits : List Bool)
    (t : NativeTripleWords) (B : ℕ) (hb : bound.length≤B) (ht : totalBits.length≤B) :
    (storedOccupationLettersProgram bound t totalBits).actions≤26*(B+1)+29 := by
  have hs:=binarySubtractProgram_actions bound totalBits false
  have hl:=binarySubtractProgram_length bound totalBits false
  have hr:=binaryTrimProgram_actions (binarySubtractProgram bound totalBits false).bits
  have hp:=wordPresenceProgram_actions t.first.bits
  have hq:=wordPresenceProgram_actions t.second.bits
  have hu:=wordPresenceProgram_actions t.third.bits
  have hv:=wordPresenceProgram_actions (binaryTrimProgram (binarySubtractProgram bound totalBits false).bits).bits
  have hx:=maskCoordinateSelectProgram_actions ([0,1,2,3] : List (Fin 4))
    [(wordPresenceProgram t.first.bits).present,(wordPresenceProgram t.second.bits).present,
      (wordPresenceProgram t.third.bits).present,
      (wordPresenceProgram (binaryTrimProgram (binarySubtractProgram bound totalBits false).bits).bits).present]
  have hm:=max_le hb ht
  change (binarySubtractProgram bound totalBits false).trace.actions+
    (binaryTrimProgram (binarySubtractProgram bound totalBits false).bits).trace.actions+
    (wordPresenceProgram t.first.bits).trace.actions+(wordPresenceProgram t.second.bits).trace.actions+
    (wordPresenceProgram t.third.bits).trace.actions+
    (wordPresenceProgram (binaryTrimProgram (binarySubtractProgram bound totalBits false).bits).bits).trace.actions+
    (maskCoordinateSelectProgram ([0,1,2,3] : List (Fin 4)) _).trace.actions≤_
  simp only [List.length_cons,List.length_nil] at hx
  omega

end EffectiveEncoding
