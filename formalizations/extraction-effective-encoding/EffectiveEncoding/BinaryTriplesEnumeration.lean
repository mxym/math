import EffectiveEncoding.BinaryCandidateProducts

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

abbrev SavedTripleWords := SavedCountWord×SavedCountWord×SavedCountWord

/-- Runtime projections of carried counts and previously stored words. -/
def savedTripleCounts (t : SavedTripleWords) : Triple := (t.1.count,t.2.1.count,t.2.2.count)
def savedTriplePrepared (t : SavedTripleWords) : NativeTripleWords :=
  ⟨t.1.encoding,t.2.1.encoding,t.2.2.encoding⟩

/-- Specification record only; binaryTriplesProgram does not call this
independent encoder or a Boolean-value decoder. -/
def specSavedTriple (t : Triple) : SavedTripleWords :=
  (⟨t.1,unaryWordEncoding t.1⟩,⟨t.2.1,unaryWordEncoding t.2.1⟩,⟨t.2.2,unaryWordEncoding t.2.2⟩)


theorem specSavedTriple_counts (t : Triple) : savedTripleCounts (specSavedTriple t)=t := rfl

theorem specSavedTriple_prepared (t : Triple) :
    savedTriplePrepared (specSavedTriple t)=nativeTripleWordProgram t := rfl

structure BinaryTriplesResult where
  range : BinaryCountRangeResult
  inner : CandidateProductResult (SavedCountWord×SavedCountWord)
  candidates : CandidateProductResult SavedTripleWords
  filtered : BinaryCandidateFilterResult SavedTripleWords

/-- One stored inclusive range, two actual ordered products, and an eager
filter controlled by two Boolean additions and one Boolean comparison per
candidate. Count words are reused from the range; no Nat total/comparison,
Nat.bits or independent per-candidate encoding is executed here. -/
def binaryTriplesProgram (k : ℕ) : BinaryTriplesResult :=
  let range:=binaryCountRangeProgram k
  let inner:=candidateProductProgram range.items range.items
  let candidates:=candidateProductProgram range.items inner.items
  let filtered:=binaryCandidateFilterProgram range.current.encoding.bits savedTriplePrepared candidates.items
  ⟨range,inner,candidates,filtered⟩

/-- Exact pre-filter candidates and stored encoding records in original order. -/
theorem binaryTriplesProgram_candidates (k : ℕ) :
    (binaryTriplesProgram k).candidates.items=
      ((List.range (k+1))×ˢ((List.range (k+1))×ˢ(List.range (k+1)))).map specSavedTriple := by
  simp only [binaryTriplesProgram,candidateProductProgram_items,binaryCountRangeProgram_items,
    candidateProduct_map]
  rfl


theorem binaryTriplesProgram_candidateLength (k : ℕ) :
    (binaryTriplesProgram k).candidates.items.length=(k+1)^3 := by
  rw [binaryTriplesProgram_candidates]
  simp only [List.length_map,List.length_product,List.length_range]
  ring

/-- Exact accepted records, not merely coverage or equality of cardinalities. -/
theorem binaryTriplesProgram_filtered (k : ℕ) :
    (binaryTriplesProgram k).filtered.items=(triples k).map specSavedTriple := by
  change (binaryCandidateFilterProgram (binaryCountRangeProgram k).current.encoding.bits savedTriplePrepared
    (binaryTriplesProgram k).candidates.items).items=_
  rw [binaryCandidateFilterProgram_items,binaryTriplesProgram_candidates,List.filter_map]
  simp only [Function.comp_def,specSavedTriple_prepared,nativeTripleWordProgram_value,
    binaryCountRangeProgram_current,unaryWordEncoding_value,triples]


theorem binaryTriplesProgram_counts (k : ℕ) :
    ((binaryTriplesProgram k).filtered.items.map savedTripleCounts)=triples k := by
  simp only [binaryTriplesProgram_filtered,List.map_map,Function.comp_def,specSavedTriple_counts]
  exact List.map_id _

/-- The prepared rank-scan input list is exactly the previous one, including
all three actual encoder records for each accepted triple. -/
theorem binaryTriplesProgram_prepared (k : ℕ) :
    ((binaryTriplesProgram k).filtered.items.map savedTriplePrepared)=
      (triplesBuild k).items.map nativeTripleWordProgram := by
  simp only [binaryTriplesProgram_filtered,List.map_map,Function.comp_def,specSavedTriple_prepared,triplesBuild_items]


theorem binaryTriplesProgram_tests (k : ℕ) :
    (binaryTriplesProgram k).filtered.tests=(binaryTriplesProgram k).candidates.items.map
      (fun t => binaryTripleBoundProgram (binaryTriplesProgram k).range.current.encoding.bits (savedTriplePrepared t)) :=
  binaryCandidateFilterProgram_tests _ _ _


theorem binaryTriplesProgram_testCount (k : ℕ) :
    (binaryTriplesProgram k).filtered.tests.length=(k+1)^3 := by
  rw [binaryTriplesProgram_tests,List.length_map,binaryTriplesProgram_candidateLength]


theorem binaryTriplesProgram_candidateWidth (k : ℕ) (x : SavedTripleWords)
    (hx : x∈(binaryTriplesProgram k).candidates.items) :
    (savedTriplePrepared x).Width (k+1) := by
  rw [binaryTriplesProgram_candidates] at hx
  rcases List.mem_map.mp hx with ⟨t,ht,rfl⟩
  rcases t with ⟨a,b,c⟩
  rcases List.mem_product.mp ht with ⟨ha,hbc⟩
  rcases List.mem_product.mp hbc with ⟨hb,hc⟩
  simp only [List.mem_range] at ha hb hc
  rw [specSavedTriple_prepared]
  change (unaryWordEncoding a).bits.length≤k+1 ∧
    (unaryWordEncoding b).bits.length≤k+1 ∧ (unaryWordEncoding c).bits.length≤k+1
  refine ⟨?_,?_,?_⟩
  · exact (unaryWordEncoding_length a).trans (by omega)
  · exact (unaryWordEncoding_length b).trans (by omega)
  · exact (unaryWordEncoding_length c).trans (by omega)


theorem binaryTriplesProgram_predicateActions (k : ℕ) :
    (binaryTriplesProgram k).filtered.predicateActions≤(k+1)^3*(64*(k+4)) := by
  have hb : (binaryTriplesProgram k).range.current.encoding.bits.length≤k+1 := by
    change (binaryCountRangeProgram k).current.encoding.bits.length≤k+1
    rw [binaryCountRangeProgram_current]
    exact unaryWordEncoding_length k
  have h:=binaryCandidateFilterProgram_predicateActions
    (binaryTriplesProgram k).range.current.encoding.bits savedTriplePrepared
    (binaryTriplesProgram k).candidates.items (k+1) hb (binaryTriplesProgram_candidateWidth k)
  change (binaryTriplesProgram k).filtered.predicateActions≤_ at h
  simpa only [binaryTriplesProgram_candidateLength,Nat.add_assoc,Nat.reduceAdd] using h

/-- Only actual stored increment/trim, range-copy, tuple/list product and
predicate records are summed. Nat-fuel/count successor, generic wrapper/filter
allocation and projection arithmetic are not silently included in this model. -/
def BinaryTriplesResult.actions (r : BinaryTriplesResult) : ℕ :=
  r.range.actions+r.inner.trace.actions+r.candidates.trace.actions+r.filtered.predicateActions


theorem binaryTriplesProgram_actions (k : ℕ) :
    (binaryTriplesProgram k).actions≤40*(k+1)^2+
      ((k+1)*(10*(k+1)+4)+1)+((k+1)*(10*(k+1)^2+4)+1)+(k+1)^3*(64*(k+4)) := by
  have hr:=binaryCountRangeProgram_actions k
  have hf:=binaryTriplesProgram_predicateActions k
  change (binaryCountRangeProgram k).actions+
    (candidateProductProgram (binaryCountRangeProgram k).items (binaryCountRangeProgram k).items).trace.actions+
    (candidateProductProgram (binaryCountRangeProgram k).items
      (candidateProductProgram (binaryCountRangeProgram k).items (binaryCountRangeProgram k).items).items).trace.actions+_≤_
  rw [candidateProductProgram_actions,candidateProductProgram_actions,candidateProductProgram_items]
  simp only [List.length_product,binaryCountRangeProgram_length]
  apply (Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_right hr _) _) hf).trans_eq
  ring


theorem binaryTriplesProgram_actions_polynomial (k : ℕ) :
    (binaryTriplesProgram k).actions≤200*(k+4)^4 := by
  have h1 : k+1≤k+4 := by omega
  have hb : 1≤k+4 := by omega
  have hp1 : k+1≤(k+4)^4 := h1.trans (by simpa using Nat.pow_le_pow_right hb (by decide : 1≤4))
  have hp2 : (k+1)^2≤(k+4)^4 := (Nat.pow_le_pow_left h1 2).trans (Nat.pow_le_pow_right hb (by decide))
  have hp3 : (k+1)^3≤(k+4)^4 := (Nat.pow_le_pow_left h1 3).trans (Nat.pow_le_pow_right hb (by decide))
  have hp0 : 1≤(k+4)^4 := Nat.one_le_pow _ _ hb
  have hlast : (k+1)^3*(64*(k+4))≤64*(k+4)^4 :=
    (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h1 3)).trans_eq (by ring)
  apply (binaryTriplesProgram_actions k).trans
  nlinarith

end EffectiveEncoding
