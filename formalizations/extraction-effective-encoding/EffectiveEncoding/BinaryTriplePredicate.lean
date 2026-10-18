import EffectiveEncoding.BinaryCountRange

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding


def nativeOrderIsAtMost : Ordering → Bool
  | .gt => false
  | _ => true


theorem nativeOrderIsAtMost_correct (as bs : List Bool) :
    nativeOrderIsAtMost (binaryWordCompareProgram as bs).order=
      decide (binaryWordValue as≤binaryWordValue bs) := by
  have hc:=binaryWordCompareProgram_correct as bs
  cases ho : (binaryWordCompareProgram as bs).order with
  | lt =>
    have h : binaryWordValue as<binaryWordValue bs := by simpa only [ho,binaryComparisonCorrect] using hc
    simp only [nativeOrderIsAtMost,decide_eq_true h.le]
  | eq =>
    have h : binaryWordValue as=binaryWordValue bs := by simpa only [ho,binaryComparisonCorrect] using hc
    simp [nativeOrderIsAtMost,h]
  | gt =>
    have h : binaryWordValue bs<binaryWordValue as := by simpa only [ho,binaryComparisonCorrect] using hc
    simp only [nativeOrderIsAtMost,decide_eq_false (by omega : ¬binaryWordValue as≤binaryWordValue bs)]

structure BinaryTriplePredicateResult where
  accepted : Bool
  firstSum : BinaryWordAdditionResult
  totalSum : BinaryWordAdditionResult
  comparison : BinaryWordComparisonResult

/-- The predicate actually selects its Boolean result by two stored word
additions and the returned comparison tag. No Nat total, decoding or Nat
comparison is evaluated on this runtime path. -/
def binaryTripleBoundProgram (bound : List Bool) (t : NativeTripleWords) : BinaryTriplePredicateResult :=
  let first:=binaryAddProgram t.first.bits t.second.bits false
  let total:=binaryAddProgram first.bits t.third.bits false
  let compared:=binaryWordCompareProgram total.bits bound
  ⟨nativeOrderIsAtMost compared.order,first,total,compared⟩


theorem binaryTripleBoundProgram_accepted (bound : List Bool) (t : NativeTripleWords) :
    (binaryTripleBoundProgram bound t).accepted=decide (total t.value≤binaryWordValue bound) := by
  simp only [binaryTripleBoundProgram,nativeOrderIsAtMost_correct,binaryAddProgram_value,
    binaryBitValue,Nat.add_zero,NativeTripleWords.value,total]
  rfl

/-- Two finite tag/branch actions in addition to the actual arithmetic traces.
This projection does not charge Nat-fuel, counter or generic allocation work. -/
def BinaryTriplePredicateResult.actions (r : BinaryTriplePredicateResult) : ℕ :=
  r.firstSum.trace.actions+r.totalSum.trace.actions+r.comparison.trace.actions+2


theorem binaryTripleBoundProgram_actions (bound : List Bool) (t : NativeTripleWords) (B : ℕ)
    (ht : t.Width B) (hb : bound.length≤B) :
    (binaryTripleBoundProgram bound t).actions≤64*(B+3) := by
  rcases ht with ⟨ht1,ht2,ht3⟩
  have h1:=binaryAddProgram_actions t.first.bits t.second.bits false
  have hl1:=binaryAddProgram_length t.first.bits t.second.bits false
  have hm1 : max t.first.bits.length t.second.bits.length≤B := max_le ht1 ht2
  have h2:=binaryAddProgram_actions (binaryAddProgram t.first.bits t.second.bits false).bits t.third.bits false
  have hl2:=binaryAddProgram_length (binaryAddProgram t.first.bits t.second.bits false).bits t.third.bits false
  have hm2 : max (binaryAddProgram t.first.bits t.second.bits false).bits.length t.third.bits.length≤B+1 :=
    max_le (by omega) (by omega)
  have h3:=binaryWordCompareProgram_actions
    (binaryAddProgram (binaryAddProgram t.first.bits t.second.bits false).bits t.third.bits false).bits bound
  have hm3 : max (binaryAddProgram (binaryAddProgram t.first.bits t.second.bits false).bits t.third.bits false).bits.length
      bound.length≤B+2 := max_le (by omega) (by omega)
  change (binaryAddProgram t.first.bits t.second.bits false).trace.actions+
    (binaryAddProgram (binaryAddProgram t.first.bits t.second.bits false).bits t.third.bits false).trace.actions+
    (binaryWordCompareProgram
      (binaryAddProgram (binaryAddProgram t.first.bits t.second.bits false).bits t.third.bits false).bits bound).trace.actions+2≤_
  omega

structure BinaryCandidateFilterResult (α : Type*) where
  items : List α
  tests : List BinaryTriplePredicateResult

/-- Real eager filter: the already executed Boolean predicate controls the
cons branch, and every candidate's actual arithmetic record is retained. -/
def binaryCandidateFilterProgram {α : Type*} (bound : List Bool) (words : α → NativeTripleWords) :
    List α → BinaryCandidateFilterResult α
  | [] => ⟨[],[]⟩
  | x::xs =>
    let test:=binaryTripleBoundProgram bound (words x)
    let tail:=binaryCandidateFilterProgram bound words xs
    ⟨if test.accepted then x::tail.items else tail.items,test::tail.tests⟩


theorem binaryCandidateFilterProgram_items {α : Type*} (bound : List Bool) (words : α → NativeTripleWords)
    (xs : List α) :
    (binaryCandidateFilterProgram bound words xs).items=
      xs.filter (fun x => decide (total (words x).value≤binaryWordValue bound)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [binaryCandidateFilterProgram,List.filter_cons,binaryTripleBoundProgram_accepted,ih]

/-- Exact list of actually executed records, including rejected candidates. -/
theorem binaryCandidateFilterProgram_tests {α : Type*} (bound : List Bool) (words : α → NativeTripleWords)
    (xs : List α) :
    (binaryCandidateFilterProgram bound words xs).tests=xs.map (fun x => binaryTripleBoundProgram bound (words x)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [binaryCandidateFilterProgram,ih,List.map_cons]


def BinaryCandidateFilterResult.predicateActions {α : Type*} (r : BinaryCandidateFilterResult α) : ℕ :=
  (r.tests.map BinaryTriplePredicateResult.actions).sum


theorem binaryCandidateFilterProgram_predicateActions {α : Type*} (bound : List Bool)
    (words : α → NativeTripleWords) (xs : List α) (B : ℕ)
    (hb : bound.length≤B) (hx : ∀ x∈xs,(words x).Width B) :
    (binaryCandidateFilterProgram bound words xs).predicateActions≤xs.length*(64*(B+3)) := by
  induction xs with
  | nil => simp [binaryCandidateFilterProgram,BinaryCandidateFilterResult.predicateActions]
  | cons x xs ih =>
    have ht:=binaryTripleBoundProgram_actions bound (words x) B (hx x (by simp)) hb
    have hs:=ih (fun y hy => hx y (by simp [hy]))
    change (binaryTripleBoundProgram bound (words x)).actions+
      (binaryCandidateFilterProgram bound words xs).predicateActions≤_
    exact (Nat.add_le_add ht hs).trans_eq (by simp only [List.length_cons];ring)

end EffectiveEncoding
