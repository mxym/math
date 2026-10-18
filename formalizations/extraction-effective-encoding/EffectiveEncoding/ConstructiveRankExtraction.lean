import EffectiveEncoding.ConstructiveTriples
import EffectiveEncoding.PackedEndpointExtraction

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

structure ConstructiveRankRun (k : ℕ) where
  index : Fin (occupationRank k)
  constructionSteps : ℕ
  predicateQueries : ℕ
  natEqualityQueries : ℕ

/-- The actual rank now uses explicit range/product/filter list construction,
materializing one range once. No candidate occupation multiset is constructed. -/
def constructiveRankProgram {k : ℕ} (ν : Sym (Fin 4) k) : ConstructiveRankRun k :=
  let candidates:=triplesBuild k
  let scan:=indexTriplesWithQueries (toTriple ν) candidates.items
  ⟨⟨scan.1,by
    change (indexTriplesWithQueries (toTriple ν) (triplesBuild k).items).1<occupationRank k
    rw [indexTriplesWithQueries_value,triplesBuild_items,← triples_length]
    exact List.idxOf_lt_length_iff.mpr (mem_triples.mpr (toTriple_le ν))⟩,
    candidates.steps,candidates.queries,scan.2⟩


def rankByConstructiveTriples {k : ℕ} (ν : Sym (Fin 4) k) : Fin (occupationRank k) :=
  (constructiveRankProgram ν).index


theorem rankByConstructiveTriples_eq {k : ℕ} (ν : Sym (Fin 4) k) :
    rankByConstructiveTriples ν=rankByTriples ν := by
  apply Fin.ext
  change (indexTriplesWithQueries (toTriple ν) (triplesBuild k).items).1=
    (indexTriplesWithQueries (toTriple ν) (countedTriples k).1).1
  rw [indexTriplesWithQueries_value,indexTriplesWithQueries_value,triplesBuild_items,countedTriples_erase]


theorem constructiveRankProgram_constructionSteps {k : ℕ} (ν : Sym (Fin 4) k) :
    (constructiveRankProgram ν).constructionSteps≤28*(k+1)^3 := triplesBuild_steps k


theorem constructiveRankProgram_predicateQueries {k : ℕ} (ν : Sym (Fin 4) k) :
    (constructiveRankProgram ν).predicateQueries=(k+1)^3 := triplesBuild_queries k


theorem constructiveRankProgram_natEqualityQueries {k : ℕ} (ν : Sym (Fin 4) k) :
    (constructiveRankProgram ν).natEqualityQueries≤3*(k+1)^3 := by
  have h:=indexTriplesWithQueries_count (toTriple ν) (triplesBuild k).items
  have hl : (triples k).length≤(k+1)^3 := by
    simpa only [occupations,List.length_map,List.length_attach] using enumeration_candidate_bound k
  have hh : (constructiveRankProgram ν).natEqualityQueries≤3*(triples k).length := by
    simpa only [constructiveRankProgram,triplesBuild_items] using h
  exact hh.trans (Nat.mul_le_mul_left 3 hl)


def constructedCompactEncoding (k : ℕ) : Sym (Fin 4) k ↪ Bits (codeWires k) where
  toFun ν:=boundedBits (codeWires k)
    ⟨(rankByConstructiveTriples ν).val,(rankByConstructiveTriples ν).isLt.trans_le (rank_fits k)⟩
  inj':=by
    intro a b h
    have he:=boundedBits_injective (codeWires k) h
    apply (rankEquiv k).injective
    apply Fin.ext
    change (rank a).val=(rank b).val
    simpa only [rankByConstructiveTriples_eq,rankByTriples_eq] using
      congrArg (fun x : Fin (2^codeWires k) => x.val) he


theorem constructedCompactEncoding_eq (k : ℕ) : constructedCompactEncoding k=tripleCompactEncoding k := by
  ext ν j
  simp only [constructedCompactEncoding,tripleCompactEncoding,rankByConstructiveTriples_eq]


def constructedNextEncoding (k : ℕ) : Sym (Fin 4) (k+1) ↪ Bits (2+codeWires k) :=
  extendEmbedding (codeWires_step k) (constructedCompactEncoding (k+1))


theorem constructedNextEncoding_eq (k : ℕ) : constructedNextEncoding k=tripleNextEncoding k := by
  simp only [constructedNextEncoding,tripleNextEncoding,constructedCompactEncoding_eq]


/-- The occupation list uses the same explicit materialized triple table. -/
def builtOccupations (k : ℕ) : List (Sym (Fin 4) k) :=
  occupationList k (triplesBuild k).items (by
    intro t ht
    apply mem_triples.mp
    rwa [triplesBuild_items] at ht)


theorem builtOccupations_eq (k : ℕ) : builtOccupations k=occupations k := by
  have hc : ∀ t∈(triplesBuild k).items,total t≤k := by
    intro t ht
    apply mem_triples.mp
    rwa [triplesBuild_items] at ht
  change occupationList k (triplesBuild k).items hc=occupations k
  exact occupationList_congr k (triplesBuild_items k) hc (fun _ ht => mem_triples.mp ht)

/-- Build one occupation list per stage and reuse it for branches/alignment. -/
def builtPackedOccupationStepCode {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) : WordCode (2+q) :=
  let occupationsHere:=builtOccupations (k+1)
  occupationsHere.flatMap (branchCode enc)++
    (packedAlignmentRun (by omega) (pivotEmbedding enc) next occupationsHere []).word


theorem builtPackedOccupationStepCode_eq {k q : ℕ} (enc : Sym (Fin 4) k ↪ Bits q)
    (next : Sym (Fin 4) (k+1) ↪ Bits (2+q)) :
    builtPackedOccupationStepCode enc next=packedOccupationStepCode enc next := by
  simp only [builtPackedOccupationStepCode,builtOccupations_eq,packedOccupationStepCode,allBranchCode]


def constructedStageCode (k : ℕ) : WordCode (originalWireCount (k+1)) :=
  prefixCode (active_available k)
    (builtPackedOccupationStepCode (constructedCompactEncoding k) (constructedNextEncoding k))


theorem constructedStageCode_eq (k : ℕ) : constructedStageCode k=packedStageCode k := by
  simp only [constructedStageCode,packedStageCode,builtPackedOccupationStepCode_eq,constructedCompactEncoding_eq,constructedNextEncoding_eq]


def constructedCompressionCode : (k : ℕ) → WordCode (originalWireCount k)
  | 0 => []
  | k+1 => (show WordCode (originalWireCount (k+1)) from
      shiftCode 2 (constructedCompressionCode k))++constructedStageCode k


theorem constructedCompressionCode_eq (k : ℕ) : constructedCompressionCode k=packedCompressionCode k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [constructedCompressionCode,packedCompressionCode,ih,constructedStageCode_eq]


def constructedExtractionCode (k : ℕ) : WordCode (originalWireCount k) :=
  constructedCompressionCode k++
    castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k)))


theorem constructedExtractionCode_eq (k : ℕ) : constructedExtractionCode k=packedExtractionCode k := by
  simp only [constructedExtractionCode,packedExtractionCode,constructedCompressionCode_eq]

/-- Finite-label terminal with explicit constructed triple ranking, packed
alignment endpoints and the actual charged raw provider/online programs. -/
def constructiveRankExtractionCode {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : List (LabelGate m (originalWireCount k)) :=
  let w:=constructedExtractionCode k
  let q:=dyadicCircuitPrecision w.length (p+1)
  compileLabelWord (fun u => (targetProgramDescriptorRun entry inverseLabel table L q u).result.word) w


theorem constructiveRankExtractionCode_eq {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    constructiveRankExtractionCode entry inverseLabel table L k p=packedEndpointExtractionCode entry inverseLabel table L k p := by
  simp only [constructiveRankExtractionCode,packedEndpointExtractionCode,constructedExtractionCode_eq]


theorem constructiveRankExtractionCode_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (constructiveRankExtractionCode entry inverseLabel table L k p)))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [constructiveRankExtractionCode_eq]
  exact packedEndpointExtractionCode_fidelity G entry he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
