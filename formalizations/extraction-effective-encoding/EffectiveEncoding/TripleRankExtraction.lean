import EffectiveEncoding.RankByTriples
import EffectiveEncoding.ChargedProviderCompiler

open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

/-- The existing pair-aligned binary code, now indexed by the direct Nat
triple scan. Candidate occupation multisets are not built by this rank call. -/
def tripleCompactEncoding (k : ℕ) : Sym (Fin 4) k ↪ Bits (codeWires k) where
  toFun ν:=boundedBits (codeWires k)
    ⟨(rankByTriples ν).val,(rankByTriples ν).isLt.trans_le (rank_fits k)⟩
  inj':=by
    intro a b h
    have he:=boundedBits_injective (codeWires k) h
    apply (rankEquiv k).injective
    apply Fin.ext
    change (rank a).val=(rank b).val
    simpa only [rankByTriples_eq] using congrArg (fun x : Fin (2^codeWires k) => x.val) he


theorem tripleCompactEncoding_eq (k : ℕ) : tripleCompactEncoding k=compactEncoding k := by
  ext ν j
  simp only [tripleCompactEncoding,compactEncoding,rankByTriples_eq]


def tripleNextEncoding (k : ℕ) : Sym (Fin 4) (k+1) ↪ Bits (2+codeWires k) :=
  extendEmbedding (codeWires_step k) (tripleCompactEncoding (k+1))


theorem tripleNextEncoding_eq (k : ℕ) : tripleNextEncoding k=nextEncoding k := by
  simp only [tripleNextEncoding,nextEncoding,tripleCompactEncoding_eq]


def tripleStoredStageCode (k : ℕ) : WordCode (originalWireCount (k+1)) :=
  prefixCode (active_available k)
    (storedOccupationStepCode (tripleCompactEncoding k) (tripleNextEncoding k))


theorem tripleStoredStageCode_eq (k : ℕ) : tripleStoredStageCode k=storedStageCode k := by
  simp only [tripleStoredStageCode,storedStageCode,tripleCompactEncoding_eq,tripleNextEncoding_eq]


def tripleStoredCompressionCode : (k : ℕ) → WordCode (originalWireCount k)
  | 0 => []
  | k+1 => (show WordCode (originalWireCount (k+1)) from
      shiftCode 2 (tripleStoredCompressionCode k))++tripleStoredStageCode k


theorem tripleStoredCompressionCode_eq (k : ℕ) : tripleStoredCompressionCode k=storedCompressionCode k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [tripleStoredCompressionCode,storedCompressionCode,ih,tripleStoredStageCode_eq]


def tripleStoredExtractionCode (k : ℕ) : WordCode (originalWireCount k) :=
  tripleStoredCompressionCode k++
    castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k)))


theorem tripleStoredExtractionCode_eq (k : ℕ) : tripleStoredExtractionCode k=storedExtractionCode k := by
  simp only [tripleStoredExtractionCode,storedExtractionCode,tripleStoredCompressionCode_eq]

/-- Actual finite-label extraction with Nat-triple ranking, stored-swap
alignment and the charged raw integer target/online programs. -/
def tripleRankExtractionCode {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : List (LabelGate m (originalWireCount k)) :=
  let w:=tripleStoredExtractionCode k
  let q:=dyadicCircuitPrecision w.length (p+1)
  compileLabelWord (fun u => (targetProgramDescriptorRun entry inverseLabel table L q u).result.word) w


theorem tripleRankExtractionCode_eq {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    tripleRankExtractionCode entry inverseLabel table L k p=chargedProviderExtractionCode entry inverseLabel table L k p := by
  simp only [tripleRankExtractionCode,chargedProviderExtractionCode,tripleStoredExtractionCode_eq]


theorem tripleRankExtractionCode_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → DyadicQuaternionOracle) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote (labelCircuit G
        (tripleRankExtractionCode entry inverseLabel table L k p)))
          (pureMatrix (bitPurePower k z))).trace.re := by
  rw [tripleRankExtractionCode_eq]
  exact chargedProviderExtractionCode_fidelity G entry he inverseLabel hi table L hL hcover k p z hz

end EffectiveEncoding
