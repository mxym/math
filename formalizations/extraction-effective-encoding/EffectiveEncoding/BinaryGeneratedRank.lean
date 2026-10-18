import EffectiveEncoding.BinaryTriplesEnumeration

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure BinaryGeneratedRankResult (k : ℕ) where
  candidates : BinaryTriplesResult
  prepared : List NativeTripleWords
  input : NativeTripleWords
  scan : NativeTripleScanResult
  index : Fin (occupationRank k)
  encoding : UnaryWordEncodingResult
  output : EndpointBitsResult (codeWires k)

/-- A genuine new rank endpoint. The runtime candidate table/filter is the
stored-word program, not triplesBuild or an old Nat predicate called for an
erasure field. Existing Nat-fuel/successor/index bookkeeping remains explicit
and is not assigned a bit fee by the projections below. -/
def binaryGeneratedRankProgram (k : ℕ) (t : Triple) (h : total t≤k) : BinaryGeneratedRankResult k :=
  let candidates:=binaryTriplesProgram k
  let prepared:=candidates.filtered.items.map savedTriplePrepared
  let input:=nativeTripleWordProgram t
  let scan:=nativeTripleScanProgram input prepared
  let index : Fin (occupationRank k):=⟨scan.index,by
    change (nativeTripleScanProgram (nativeTripleWordProgram t)
      ((binaryTriplesProgram k).filtered.items.map savedTriplePrepared)).index<occupationRank k
    rw [binaryTriplesProgram_prepared,nativeTripleScanProgram_index,nativeTripleWordProgram_value,
      nativeTripleWordMap_values,indexTriplesWithQueries_value,triplesBuild_items,←triples_length]
    exact List.idxOf_lt_length_iff.mpr (mem_triples.mpr h)⟩
  let encoding:=unaryWordEncoding index.val
  let output:=endpointBitsProgram (codeWires k) encoding.bits
  ⟨candidates,prepared,input,scan,index,encoding,output⟩


theorem binaryGeneratedRankProgram_scan (k : ℕ) (t : Triple) (h : total t≤k) :
    (binaryGeneratedRankProgram k t h).scan=(nativeBooleanRankProgram k t h).scan := by
  simp only [binaryGeneratedRankProgram,binaryTriplesProgram_prepared,nativeBooleanRankProgram]


theorem binaryGeneratedRankProgram_input (k : ℕ) (t : Triple) (h : total t≤k) :
    (binaryGeneratedRankProgram k t h).input=(nativeBooleanRankProgram k t h).preparedInput := rfl

/-- The index is selected by the actual stored Boolean scan. The old rank is
used only in this semantic equality proof, not as a runtime input. -/
theorem binaryGeneratedRankProgram_index (k : ℕ) (t : Triple) (h : total t≤k) :
    (binaryGeneratedRankProgram k t h).index=(carriedTripleRankProgram k t h).index := by
  rw [←nativeBooleanRankProgram_ranked]
  apply Fin.ext
  exact congrArg NativeTripleScanResult.index (binaryGeneratedRankProgram_scan k t h)


theorem binaryGeneratedRankProgram_encoding (k : ℕ) (t : Triple) (h : total t≤k) :
    (binaryGeneratedRankProgram k t h).encoding=(nativeBinaryRankProgram k t h).encoding := by
  change unaryWordEncoding (binaryGeneratedRankProgram k t h).index.val=_
  rw [binaryGeneratedRankProgram_index]
  rfl

/-- Exact entire output/padding record, not just interpreted endpoint bits. -/
theorem binaryGeneratedRankProgram_output (k : ℕ) (t : Triple) (h : total t≤k) :
    (binaryGeneratedRankProgram k t h).output=(nativeBinaryRankProgram k t h).output := by
  change endpointBitsProgram (codeWires k) (binaryGeneratedRankProgram k t h).encoding.bits=_
  rw [binaryGeneratedRankProgram_encoding]
  rfl

/-- Count only the actual stored component models: range/product/predicate,
input encoding, Boolean scan comparisons, rank increment/trim and padding.
Prepared-record maps, Nat/control/annotation work and general allocation remain
outside this partial model. -/
def BinaryGeneratedRankResult.actions {k : ℕ} (r : BinaryGeneratedRankResult k) : ℕ :=
  r.candidates.actions+(r.input.encodingActions+r.scan.comparisonActions)+
    (r.encoding.trace.incrementTrimActions+r.output.trace.listActions)


theorem binaryGeneratedRankProgram_actions (k : ℕ) (t : Triple) (h : total t≤k) :
    (binaryGeneratedRankProgram k t h).actions≤
      200*(k+4)^4+300*(k+2)^5+51*(k+3)^6 := by
  have he:=binaryTriplesProgram_actions_polynomial k
  have hs : (binaryGeneratedRankProgram k t h).input.encodingActions+
      (binaryGeneratedRankProgram k t h).scan.comparisonActions≤300*(k+2)^5 := by
    rw [binaryGeneratedRankProgram_input,binaryGeneratedRankProgram_scan]
    have hle : (nativeBooleanRankProgram k t h).preparedInput.encodingActions+
        (nativeBooleanRankProgram k t h).scan.comparisonActions≤
        (nativeBooleanRankProgram k t h).booleanActions := by
      unfold NativeBooleanRankResult.booleanActions
      omega
    exact hle.trans (nativeBooleanRankProgram_booleanActions_polynomial k t h)
  have hd : (binaryGeneratedRankProgram k t h).encoding.trace.incrementTrimActions+
      (binaryGeneratedRankProgram k t h).output.trace.listActions≤51*(k+3)^6 := by
    rw [binaryGeneratedRankProgram_encoding,binaryGeneratedRankProgram_output]
    exact nativeBinaryRankProgram_encodingActions_polynomial k t h
  exact Nat.add_le_add (Nat.add_le_add he hs) hd


theorem binaryGeneratedRankProgram_actions_polynomial (k : ℕ) (t : Triple) (h : total t≤k) :
    (binaryGeneratedRankProgram k t h).actions≤551*(k+4)^6 := by
  have hb : 1≤k+4 := by omega
  have hp4 : (k+4)^4≤(k+4)^6 := Nat.pow_le_pow_right hb (by decide)
  have hp5 : (k+2)^5≤(k+4)^6 := (Nat.pow_le_pow_left (show k+2≤k+4 by omega) 5).trans
    (Nat.pow_le_pow_right hb (by decide))
  have hp6 : (k+3)^6≤(k+4)^6 := Nat.pow_le_pow_left (by omega) 6
  apply (binaryGeneratedRankProgram_actions k t h).trans
  exact (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 200 hp4)
    (Nat.mul_le_mul_left 300 hp5)) (Nat.mul_le_mul_left 51 hp6)).trans_eq (by ring)

end EffectiveEncoding
