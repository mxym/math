import EffectiveEncoding.BinaryTriplesEnumeration

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure RetainedCandidateFilterResult (α : Type*) where
  common : BinaryCandidateFilterResult α
  accepted : List (α×BinaryTriplePredicateResult)

/-- The executed predicate is stored both in the complete test stream and next
 to its accepted input. Neither its Boolean additions nor its comparison are
 replayed to recover a total for downstream occupation selection. -/
def retainedCandidateFilterProgram {α : Type*} (bound : List Bool)
    (words : α → NativeTripleWords) : List α → RetainedCandidateFilterResult α
  | [] => ⟨⟨[],[]⟩,[]⟩
  | x::xs =>
    let test:=binaryTripleBoundProgram bound (words x)
    let tail:=retainedCandidateFilterProgram bound words xs
    if test.accepted then
      ⟨⟨x::tail.common.items,test::tail.common.tests⟩,(x,test)::tail.accepted⟩
    else ⟨⟨tail.common.items,test::tail.common.tests⟩,tail.accepted⟩

/-- Whole old filter record, including every rejected input's executed test. -/
theorem retainedCandidateFilterProgram_common {α : Type*} (bound : List Bool)
    (words : α → NativeTripleWords) (xs : List α) :
    (retainedCandidateFilterProgram bound words xs).common=
      binaryCandidateFilterProgram bound words xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [retainedCandidateFilterProgram,binaryCandidateFilterProgram]
    split <;> simp_all


theorem retainedCandidateFilterProgram_inputs {α : Type*} (bound : List Bool)
    (words : α → NativeTripleWords) (xs : List α) :
    ((retainedCandidateFilterProgram bound words xs).accepted.map Prod.fst)=
      (retainedCandidateFilterProgram bound words xs).common.items := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [retainedCandidateFilterProgram]
    split <;> simp_all


theorem retainedCandidateFilterProgram_mem {α : Type*} (bound : List Bool)
    (words : α → NativeTripleWords) (xs : List α) (a : α×BinaryTriplePredicateResult)
    (ha : a∈(retainedCandidateFilterProgram bound words xs).accepted) :
    a.1∈xs ∧ a.2=binaryTripleBoundProgram bound (words a.1) ∧ a.2.accepted=true := by
  induction xs with
  | nil => simp [retainedCandidateFilterProgram] at ha
  | cons x xs ih =>
    simp only [retainedCandidateFilterProgram] at ha
    split at ha
    · rename_i h
      rcases List.mem_cons.mp ha with rfl|ha
      · exact ⟨List.mem_cons_self,rfl,h⟩
      · obtain ⟨hi,he,hb⟩:=ih ha
        exact ⟨List.mem_cons_of_mem x hi,he,hb⟩
    · obtain ⟨hi,he,hb⟩:=ih ha
      exact ⟨List.mem_cons_of_mem x hi,he,hb⟩

structure RetainedTriplesResult where
  common : BinaryTriplesResult
  accepted : List (SavedTripleWords×BinaryTriplePredicateResult)

/-- Stored count words and accepted total-addition records survive the actual
 range/product/filter execution. The common enumeration is not run a second
 time to produce this result. -/
def retainedTriplesProgram (k : ℕ) : RetainedTriplesResult :=
  let range:=binaryCountRangeProgram k
  let inner:=candidateProductProgram range.items range.items
  let candidates:=candidateProductProgram range.items inner.items
  let filtered:=retainedCandidateFilterProgram range.current.encoding.bits savedTriplePrepared candidates.items
  ⟨⟨range,inner,candidates,filtered.common⟩,filtered.accepted⟩


theorem retainedTriplesProgram_common (k : ℕ) :
    (retainedTriplesProgram k).common=binaryTriplesProgram k := by
  simp only [retainedTriplesProgram,retainedCandidateFilterProgram_common,binaryTriplesProgram]


theorem retainedTriplesProgram_inputs (k : ℕ) :
    ((retainedTriplesProgram k).accepted.map Prod.fst)=(binaryTriplesProgram k).filtered.items := by
  change ((retainedCandidateFilterProgram _ _ _).accepted.map Prod.fst)=_
  rw [retainedCandidateFilterProgram_inputs,retainedCandidateFilterProgram_common]
  rfl


theorem retainedTriplesProgram_mem (k : ℕ) (a : SavedTripleWords×BinaryTriplePredicateResult)
    (ha : a∈(retainedTriplesProgram k).accepted) :
    a.1∈(binaryTriplesProgram k).candidates.items ∧
    a.2=binaryTripleBoundProgram (binaryTriplesProgram k).range.current.encoding.bits
      (savedTriplePrepared a.1) ∧ a.2.accepted=true :=
  retainedCandidateFilterProgram_mem _ _ _ a ha

end EffectiveEncoding
