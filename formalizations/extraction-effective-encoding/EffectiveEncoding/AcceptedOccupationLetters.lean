import EffectiveEncoding.StoredOccupationLetters
import EffectiveEncoding.CandidateNativeTable

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding


theorem retainedTriplesProgram_valid (k : ℕ) (a : SavedTripleWords×BinaryTriplePredicateResult)
    (ha : a∈(retainedTriplesProgram k).accepted) : total (savedTripleCounts a.1)≤k := by
  have hi : a.1∈(binaryTriplesProgram k).filtered.items := by
    rw [←retainedTriplesProgram_inputs]
    exact List.mem_map.mpr ⟨a,ha,rfl⟩
  apply mem_triples.mp
  rw [←binaryTriplesProgram_counts]
  exact List.mem_map.mpr ⟨a.1,hi,rfl⟩


def acceptedNativeOccupation (k : ℕ) (a : SavedTripleWords×BinaryTriplePredicateResult)
    (ha : a∈(retainedTriplesProgram k).accepted) : NativeOccupation k :=
  ⟨savedTripleCounts a.1,retainedTriplesProgram_valid k a ha⟩


theorem savedTriplePrepared_candidate_value (k : ℕ) (s : SavedTripleWords)
    (hs : s∈(binaryTriplesProgram k).candidates.items) :
    (savedTriplePrepared s).value=savedTripleCounts s ∧
    BinaryWordCanonical s.1.encoding.bits ∧ BinaryWordCanonical s.2.1.encoding.bits ∧
      BinaryWordCanonical s.2.2.encoding.bits := by
  rw [binaryTriplesProgram_candidates] at hs
  obtain ⟨t,ht,rfl⟩:=List.mem_map.mp hs
  simp only [specSavedTriple_prepared,nativeTripleWordProgram_value,specSavedTriple_counts]
  exact ⟨trivial,unaryWordEncoding_canonical _,unaryWordEncoding_canonical _,unaryWordEncoding_canonical _⟩

structure AcceptedOccupationLettersResult (k : ℕ) where
  source : SavedTripleWords×BinaryTriplePredicateResult
  native : NativeOccupation k
  letters : StoredOccupationLettersResult

/-- Inputs are only actual saved count words, bound words and accepted total
 records. Attaching a native triple uses stored count projections; its proof
 is erased. No old Nat filter, Nat positivity or independent encoder runs. -/
def acceptedOccupationLettersProgram (k : ℕ) (a : SavedTripleWords×BinaryTriplePredicateResult)
    (ha : a∈(retainedTriplesProgram k).accepted) : AcceptedOccupationLettersResult k :=
  ⟨a,acceptedNativeOccupation k a ha,
    storedOccupationLettersProgram (retainedTriplesProgram k).common.range.current.encoding.bits
      (savedTriplePrepared a.1) a.2.totalSum.bits⟩

/-- For a reusable stage enumeration the bound is supplied directly from its
 stored record; this definition does not call retainedTriplesProgram again. -/
def acceptedOccupationLettersWithBound (bound : List Bool) {k : ℕ}
    (a : SavedTripleWords×BinaryTriplePredicateResult) (h : total (savedTripleCounts a.1)≤k) :
    AcceptedOccupationLettersResult k :=
  ⟨a,⟨savedTripleCounts a.1,h⟩,storedOccupationLettersProgram bound (savedTriplePrepared a.1) a.2.totalSum.bits⟩


theorem acceptedOccupationLettersProgram_sorted (k : ℕ) (a : SavedTripleWords×BinaryTriplePredicateResult)
    (ha : a∈(retainedTriplesProgram k).accepted) :
    (acceptedOccupationLettersProgram k a ha).letters.items=
      (nativeSelected (acceptedOccupationLettersProgram k a ha).native).sort (·≤·) := by
  obtain ⟨hi,he,htrue⟩:=retainedTriplesProgram_mem k a ha
  obtain ⟨hv,h1,h2,h3⟩:=savedTriplePrepared_candidate_value k a.1 hi
  have hb : binaryWordValue (retainedTriplesProgram k).common.range.current.encoding.bits=k := by
    rw [retainedTriplesProgram_common]
    change binaryWordValue (binaryCountRangeProgram k).current.encoding.bits=k
    rw [binaryCountRangeProgram_current,unaryWordEncoding_value]
  have ht : binaryWordValue a.2.totalSum.bits=total (savedTripleCounts a.1) := by
    rw [he]
    simp only [binaryTripleBoundProgram,binaryAddProgram_value,binaryBitValue,Nat.add_zero]
    change total (savedTriplePrepared a.1).value=_
    rw [hv]
  exact storedOccupationLettersProgram_sorted (acceptedNativeOccupation k a ha) _ _ _ hb ht hv ⟨h1,h2,h3⟩

structure AcceptedOccupationTableResult (k : ℕ) where
  enumeration : RetainedTriplesResult
  items : List (AcceptedOccupationLettersResult k)

/-- One enumeration, followed by one actual selector per accepted record. The
 shared bound and each totalSum are read from that same executed enumeration.
 No per-input call to the independent convenience wrapper occurs here. -/
def acceptedOccupationTableProgram (k : ℕ) : AcceptedOccupationTableResult k :=
  let enumeration:=retainedTriplesProgram k
  let bound:=enumeration.common.range.current.encoding.bits
  let items:=enumeration.accepted.attach.map (fun a =>
    acceptedOccupationLettersWithBound bound a.1 (retainedTriplesProgram_valid k a.1 a.2))
  ⟨enumeration,items⟩


theorem acceptedOccupationTableProgram_items (k : ℕ) :
    (acceptedOccupationTableProgram k).items=
      (retainedTriplesProgram k).accepted.attach.map (fun a => acceptedOccupationLettersProgram k a.1 a.2) := rfl


theorem acceptedOccupationTableProgram_native (k : ℕ) :
    ((acceptedOccupationTableProgram k).items.map AcceptedOccupationLettersResult.native)=
      (candidateNativeTableProgram k).items := by
  apply List.map_injective_iff.mpr Subtype.val_injective
  rw [List.map_map,candidateNativeTableProgram_counts]
  simp only [acceptedOccupationTableProgram,List.map_map,Function.comp_def,acceptedOccupationLettersWithBound]
  change (((retainedTriplesProgram k).accepted.attach.map (fun a => savedTripleCounts a.1.1)))=triples k
  rw [List.attach_map_val (f := fun a : SavedTripleWords×BinaryTriplePredicateResult => savedTripleCounts a.1)]
  have hi:=congrArg (List.map savedTripleCounts) (retainedTriplesProgram_inputs k)
  simpa only [List.map_map,Function.comp_def,binaryTriplesProgram_counts] using hi



theorem acceptedOccupationTableProgram_sorted (k : ℕ) (r : AcceptedOccupationLettersResult k)
    (hr : r∈(acceptedOccupationTableProgram k).items) :
    r.letters.items=(nativeSelected r.native).sort (·≤·) := by
  rw [acceptedOccupationTableProgram_items] at hr
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hr
  exact acceptedOccupationLettersProgram_sorted k a.1 a.2


theorem acceptedOccupationLettersProgram_actions (k : ℕ) (a : SavedTripleWords×BinaryTriplePredicateResult)
    (ha : a∈(retainedTriplesProgram k).accepted) :
    (acceptedOccupationLettersProgram k a ha).letters.actions≤26*(k+4)+29 := by
  obtain ⟨hi,he,htrue⟩:=retainedTriplesProgram_mem k a ha
  have hw:=binaryTriplesProgram_candidateWidth k a.1 hi
  have hb : (retainedTriplesProgram k).common.range.current.encoding.bits.length≤k+3 := by
    rw [retainedTriplesProgram_common]
    change (binaryCountRangeProgram k).current.encoding.bits.length≤k+3
    rw [binaryCountRangeProgram_current]
    exact (unaryWordEncoding_length k).trans (by omega)
  have ht : a.2.totalSum.bits.length≤k+3 := by
    rw [he]
    have h1:=binaryAddProgram_length (savedTriplePrepared a.1).first.bits
      (savedTriplePrepared a.1).second.bits false
    have h2:=binaryAddProgram_length
      (binaryAddProgram (savedTriplePrepared a.1).first.bits (savedTriplePrepared a.1).second.bits false).bits
      (savedTriplePrepared a.1).third.bits false
    rcases hw with ⟨hw1,hw2,hw3⟩
    change (binaryAddProgram
      (binaryAddProgram (savedTriplePrepared a.1).first.bits (savedTriplePrepared a.1).second.bits false).bits
      (savedTriplePrepared a.1).third.bits false).bits.length≤_
    omega
  exact storedOccupationLettersProgram_actions _ _ _ (k+3) hb ht


def AcceptedOccupationTableResult.letterActions {k : ℕ} (r : AcceptedOccupationTableResult k) : ℕ :=
  (r.items.map (fun a => a.letters.actions)).sum


theorem acceptedOccupationTableProgram_letterActions (k : ℕ) :
    (acceptedOccupationTableProgram k).letterActions≤(k+1)^3*(26*(k+4)+29) := by
  have hx : ∀ r∈(acceptedOccupationTableProgram k).items,r.letters.actions≤26*(k+4)+29 := by
    intro r hr
    rw [acceptedOccupationTableProgram_items] at hr
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hr
    exact acceptedOccupationLettersProgram_actions k a.1 a.2
  have general : ∀ xs : List (AcceptedOccupationLettersResult k),
      (∀ r∈xs,r.letters.actions≤26*(k+4)+29) →
      (xs.map (fun r => r.letters.actions)).sum≤xs.length*(26*(k+4)+29) := by
    intro xs
    induction xs with
    | nil => intro h;simp
    | cons a xs ih =>
      intro h
      have ha:=h a (by simp)
      have ht:=ih (fun b hb => h b (by simp [hb]))
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      exact (Nat.add_le_add ha ht).trans_eq (by ring)
  have hl : (acceptedOccupationTableProgram k).items.length≤(k+1)^3 := by
    have h:=congrArg List.length (acceptedOccupationTableProgram_native k)
    simp only [List.length_map] at h
    rw [h]
    exact candidateNativeTableProgram_length k
  exact (general _ hx).trans (Nat.mul_le_mul_right _ hl)

/-- The old enumeration trace plus the actual new per-accepted-input letter
 arithmetic/selectors. The accepted-record wrapper/list-allocation overhead
 and host recursion/counter arithmetic remain outside this partial model. -/
def AcceptedOccupationTableResult.actions {k : ℕ} (r : AcceptedOccupationTableResult k) : ℕ :=
  r.enumeration.common.actions+r.letterActions


theorem acceptedOccupationTableProgram_actions (k : ℕ) :
    (acceptedOccupationTableProgram k).actions≤255*(k+4)^4 := by
  have hr : (acceptedOccupationTableProgram k).enumeration.common.actions≤200*(k+4)^4 := by
    change (retainedTriplesProgram k).common.actions≤_
    rw [retainedTriplesProgram_common]
    exact binaryTriplesProgram_actions_polynomial k
  have hf : 26*(k+4)+29≤55*(k+4) := by omega
  have hs : (acceptedOccupationTableProgram k).letterActions≤55*(k+4)^4 :=
    (acceptedOccupationTableProgram_letterActions k).trans
      ((Nat.mul_le_mul (Nat.pow_le_pow_left (by omega : k+1≤k+4) 3) hf).trans_eq (by ring))
  exact (Nat.add_le_add hr hs).trans_eq (by ring)

end EffectiveEncoding
