import EffectiveEncoding.CandidateRankEndpoints

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure CandidateNativeTableResult (k : ℕ) where
  enumeration : BinaryTriplesResult
  items : List (NativeOccupation k)

/-- Actual native occupation table from the new Boolean filter. Runtime data
is carried triples with erased validity proofs; no semantic Sym or old Nat
filter is evaluated to attach those proofs. -/
def candidateNativeTableProgram (k : ℕ) : CandidateNativeTableResult k :=
  let enumeration:=binaryTriplesProgram k
  let items:=enumeration.filtered.items.attach.map (fun t =>
    (⟨savedTripleCounts t.1,by
      apply mem_triples.mp
      rw [←binaryTriplesProgram_counts k]
      exact List.mem_map.mpr ⟨t.1,t.2,rfl⟩⟩ : NativeOccupation k))
  ⟨enumeration,items⟩


theorem candidateNativeTableProgram_counts (k : ℕ) :
    ((candidateNativeTableProgram k).items.map Subtype.val)=triples k := by
  simp only [candidateNativeTableProgram,List.map_map,Function.comp_def,List.attach_map_val]
  exact binaryTriplesProgram_counts k

/-- Exact ordered native subtype list. The erased proof fields need no choice
or comparison to establish this equality. -/
theorem candidateNativeTableProgram_items (k : ℕ) :
    (candidateNativeTableProgram k).items=nativeOccupationTable k := by
  apply List.map_injective_iff.mpr Subtype.val_injective
  rw [candidateNativeTableProgram_counts]
  simp only [nativeOccupationTable,List.map_map,Function.comp_def,List.attach_map_subtype_val,triplesBuild_items]


theorem candidateNativeTableProgram_length (k : ℕ) :
    (candidateNativeTableProgram k).items.length≤(k+1)^3 := by
  have h:=(congrArg List.length (candidateNativeTableProgram_counts k))
  rw [List.length_map] at h
  rw [h,triples_length,←occupations_length]
  exact enumeration_candidate_bound k

end EffectiveEncoding
