import EffectiveEncoding.FixedWidthEndpointBits

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

structure NativeBinaryRankResult (k : ℕ) where
  ranked : ConstructiveRankRun k
  encoding : UnaryWordEncodingResult
  output : EndpointBitsResult (codeWires k)

/-- Rank once, build its actual Boolean digits once by real increment/trim,
then copy/pad them in one structural pass. The old Nat bit extraction is not
called. No semantic occupation is present in the runtime input. -/
def nativeBinaryRankProgram (k : ℕ) (t : Triple) (h : total t≤k) : NativeBinaryRankResult k :=
  let ranked:=carriedTripleRankProgram k t h
  let encoded:=unaryWordEncoding ranked.index.val
  let output:=endpointBitsProgram (codeWires k) encoded.bits
  ⟨ranked,encoded,output⟩


def NativeBinaryRankResult.erase {k : ℕ} (r : NativeBinaryRankResult k) : EncodedEndpoint (codeWires k) :=
  ⟨r.output.bits,![r.ranked.constructionSteps,r.ranked.predicateQueries,r.ranked.natEqualityQueries]⟩

/-- Exact entire endpoint record, including the original actual rank-work data. -/
theorem nativeBinaryRankProgram_erase (k : ℕ) (t : Triple) (h : total t≤k) :
    (nativeBinaryRankProgram k t h).erase=carriedEncodedEndpoint k t h := by
  unfold nativeBinaryRankProgram NativeBinaryRankResult.erase carriedEncodedEndpoint
  congr 1
  apply List.Vector.ext
  intro j
  simp only [endpointBitsProgram_get,List.Vector.get_ofFn]
  rw [←binaryWordValue_testBit_getD,unaryWordEncoding_value]


def NativeBinaryRankResult.encodingActions {k : ℕ} (r : NativeBinaryRankResult k) : ℕ :=
  r.encoding.trace.incrementTrimActions+r.output.trace.listActions


theorem nativeBinaryRankProgram_encodingActions (k : ℕ) (t : Triple) (h : total t≤k) :
    (nativeBinaryRankProgram k t h).encodingActions≤32*(k+1)^6+3*codeWires k+1 := by
  let ranked:=carriedTripleRankProgram k t h
  have hlen : occupationRank k≤(k+1)^3 := by
    rw [←occupations_length]
    exact enumeration_candidate_bound k
  have hr : ranked.index.val+1≤(k+1)^3 := (Nat.add_one_le_iff.mpr ranked.index.isLt).trans hlen
  have hi:=(unaryWordEncoding_incrementTrimActions ranked.index.val).trans
    (Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left hr 2))
  have ho:=endpointBitsProgram_listActions (codeWires k) (unaryWordEncoding ranked.index.val).bits
  change (unaryWordEncoding ranked.index.val).trace.incrementTrimActions+
    (endpointBitsProgram (codeWires k) (unaryWordEncoding ranked.index.val).bits).trace.listActions≤_
  calc
    _≤32*((k+1)^3)^2+(3*codeWires k+1) := Nat.add_le_add hi ho
    _=_ := by ring


theorem nativeBinaryRankProgram_encodingActions_polynomial (k : ℕ) (t : Triple) (h : total t≤k) :
    (nativeBinaryRankProgram k t h).encodingActions≤51*(k+3)^6 := by
  have hc : Nat.clog 2 (k+3)≤k+3 := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n:=k+3)).le
  have hw:=activeWires_log_bound k
  have hw' : codeWires k≤6*(k+3) := by
    have he : activeWires k=2+codeWires k := by unfold activeWires codeWires;omega
    rw [he] at hw
    omega
  have hp : (k+1)^6≤(k+3)^6 := Nat.pow_le_pow_left (by omega) 6
  have hx5 : 1≤(k+3)^5 := Nat.one_le_pow _ _ (by omega)
  have hx : k+3≤(k+3)^6 := by rw [pow_succ];nlinarith
  have h1 : 1≤(k+3)^6 := Nat.one_le_pow _ _ (by omega)
  apply (nativeBinaryRankProgram_encodingActions k t h).trans
  nlinarith

end EffectiveEncoding
