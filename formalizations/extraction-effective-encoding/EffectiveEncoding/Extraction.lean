import EffectiveEncoding.Compression
import CircuitRecursion.LocalDiscard

open scoped BigOperators
open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

def castCode {m n : ℕ} (h : m=n) (xs : WordCode m) : WordCode n := h ▸ xs

@[simp] theorem interpret_cast {m n : ℕ} (h : m=n) (xs : WordCode m) :
    interpret (castCode h xs)=castCircuit h (interpret xs) := by subst n;rfl

@[simp] theorem castCode_length {m n : ℕ} (h : m=n) (xs : WordCode m) :
    (castCode h xs).length=xs.length := by subst n;rfl

def bellPreparationCode : WordCode 2 :=
  [.single 0 .hadamard,.cnot 0 1 (by decide)]

theorem interpret_bellPreparationCode : interpret bellPreparationCode=bellPreparationWord := rfl

def bellPairsCode : (h : ℕ) → WordCode (originalWireCount h)
  | 0 => []
  | h+1 => (show WordCode (originalWireCount (h+1)) from
      prefixCode (Nat.le_add_right 2 (originalWireCount h)) bellPreparationCode)++
      (show WordCode (originalWireCount (h+1)) from shiftCode 2 (bellPairsCode h))

theorem interpret_bellPairsCode (h : ℕ) : interpret (bellPairsCode h)=bellPairsWord h := by
  induction h with
  | zero => rfl
  | succ h ih =>
    rw [bellPairsCode,interpret_append]
    erw [interpret_prefix,interpret_shift,interpret_bellPreparationCode,prefixCircuit_eq_lift,ih]
    rfl

def extractionCode (k : ℕ) : WordCode (originalWireCount k) :=
  compressionCode k++
    castCode (register_split k) (shiftCode (codeWires k) (bellPairsCode (bellPairYield k)))

/-- The actual elementary Gate list is bound gate by gate to a computably
generated finite description on the sole original register. -/
noncomputable def extractionCircuit (k : ℕ) : Circuit (originalWireCount k) :=
  interpret (extractionCode k)

theorem extractionCircuit_eq (k : ℕ) :
    extractionCircuit k=compressionCircuit k++tailBellCircuit (register_split k) := by
  rw [extractionCircuit,extractionCode,interpret_append,interpret_cast,
    interpret_shift,interpret_bellPairsCode]
  rfl

theorem extractionCircuit_gate {k : ℕ} (i : Fin (extractionCode k).length) :
    (extractionCircuit k)[i.val]'(by rw [extractionCircuit,interpret_length];exact i.isLt)=
      ((extractionCode k)[i.val]).value := by
  simp only [extractionCircuit,interpret,List.getElem_map]

noncomputable def extractionVector (k : ℕ) (a : Sym (Fin 4) k → ℂ) :
    Bits (originalWireCount k) → ℂ := fun b =>
  (Extraction.coordinateIsometry (compactEncoding k)*ᵥa)
    (prefixBits (castBits (register_split k).symm b))*
      bellPairsVector (bellPairYield k) (suffixBits (castBits (register_split k).symm b))

theorem extractionCircuit_coherent (k : ℕ) (a : Sym (Fin 4) k → ℂ) :
    run (extractionCircuit k) (bitOccupationMatrix k*ᵥa)=extractionVector k a := by
  rw [extractionCircuit_eq,run_append,compressionCircuit_coherent]
  rw [originalEncoding,extendVector_padding (register_split k)]
  exact tailBellCircuit_action (register_split k) _

theorem extractionCircuit_purePower (k : ℕ) (z : Fin 4 → ℂ) :
    run (extractionCircuit k) (bitPurePower k z)=
      extractionVector k (pureOccupationCoefficients k z) := by
  rw [← bitPurePower_expansion,extractionCircuit_coherent]

theorem extractionCode_length (k : ℕ) :
    (extractionCode k).length≤recursiveGateBudget k := by
  have hl : (bellPairsCode (bellPairYield k)).length=2*bellPairYield k := by
    rw [← interpret_length,interpret_bellPairsCode,bellPairsWord_length]
  rw [extractionCode,List.length_append,castCode_length,shiftCode_length,hl]
  have hc := compressionCode_length k
  have hy : bellPairYield k≤k := Nat.sub_le _ _
  have hk : 2*k≤100*k^2 := by cases k <;> nlinarith
  unfold recursiveGateBudget
  omega

theorem extractionCode_polynomial_bound (k : ℕ) :
    (extractionCode k).length≤
      20480*k*(k+2)^6*(6*Nat.clog 2 (k+3)+2)^2+100*k^2 :=
  (extractionCode_length k).trans (recursiveGateBudget_bound k)

theorem extractionCircuit_polynomial_bound (k : ℕ) :
    (extractionCircuit k).length≤
      20480*k*(k+2)^6*(6*Nat.clog 2 (k+3)+2)^2+100*k^2 := by
  rw [extractionCircuit,interpret_length]
  exact extractionCode_polynomial_bound k

noncomputable def garbageVector (k : ℕ) (a : Sym (Fin 4) k → ℂ) :
    Bits (encodingPairs k)×Bits (encodingPairs k) → ℂ := fun z =>
  (Extraction.coordinateIsometry (compactEncoding k)*ᵥa) ((codePairCoordinates k).symm z)

theorem extractionVector_readout (k : ℕ) (a : Sym (Fin 4) k → ℂ)
    (b : Bits (originalWireCount k)) :
    extractionVector k a b=
      (Extraction.codeEmbedding (Extraction.bellCoeff (Bits (bellPairYield k)))*ᵥ
        garbageVector k a) (readoutCoordinates k b) := by
  rw [codeEmbedding_mulVec,readoutCoordinates_split]
  simp only [garbageVector,Equiv.symm_apply_apply]
  unfold extractionVector
  rw [bellPairsVector_standard,mul_comm]
  simp only [Prod.mk.eta,Equiv.symm_apply_apply]

theorem garbageVector_square (k : ℕ) (a : Sym (Fin 4) k → ℂ) :
    vectorSquare (garbageVector k a)=vectorSquare a := by
  have hs := (codePairCoordinates k).symm.sum_comp
    (fun b => Complex.normSq ((Extraction.coordinateIsometry (compactEncoding k)*ᵥa) b))
  change vectorSquare (garbageVector k a)=vectorSquare
    (Extraction.coordinateIsometry (compactEncoding k)*ᵥa) at hs
  exact hs.trans (vectorSquare_isometry _ (Extraction.coordinateIsometry_isometry _) a)

noncomputable def extractionOutput (k : ℕ)
    (X : Matrix (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ) :
    Matrix (Bits (bellPairYield k)×Bits (bellPairYield k))
      (Bits (bellPairYield k)×Bits (bellPairYield k)) ℂ :=
  Extraction.krausApply (Extraction.productEraseKraus
    (d := Bits (bellPairYield k)) (u := Bits (encodingPairs k)) (v := Bits (encodingPairs k)))
      (Matrix.reindexAlgEquiv ℂ ℂ (readoutCoordinates k)
        ((denote (extractionCircuit k) : Matrix (Bits (originalWireCount k))
          (Bits (originalWireCount k)) ℂ)*X*
            (denote (extractionCircuit k) : Matrix (Bits (originalWireCount k))
              (Bits (originalWireCount k)) ℂ)ᴴ))

theorem extractionOutput_coherent (k : ℕ) (a : Sym (Fin 4) k → ℂ) :
    extractionOutput k (pureMatrix (bitOccupationMatrix k*ᵥa))=
      (vectorSquare a : ℂ) • pureMatrix (Extraction.bellVector
        (Extraction.bellCoeff (Bits (bellPairYield k)))) := by
  unfold extractionOutput
  simp only [pureMatrix]
  rw [Extraction.congruence_pure]
  change Extraction.krausApply _
    (Matrix.reindexAlgEquiv ℂ ℂ (readoutCoordinates k)
      (pureMatrix (run (extractionCircuit k) (bitOccupationMatrix k*ᵥa))))=_
  rw [extractionCircuit_coherent]
  have he : Matrix.reindexAlgEquiv ℂ ℂ (readoutCoordinates k)
      (pureMatrix (extractionVector k a))=
      pureMatrix (Extraction.codeEmbedding (Extraction.bellCoeff (Bits (bellPairYield k)))*ᵥ
        garbageVector k a) := by
    ext p q
    simp only [Matrix.coe_reindexAlgEquiv,Matrix.reindex_apply,Matrix.submatrix_apply,pureMatrix,
      Matrix.vecMulVec_apply,Pi.star_apply,extractionVector_readout,Equiv.apply_symm_apply]
  rw [he]
  change Extraction.krausApply _ (Matrix.vecMulVec _ (star _))=_
  rw [← Extraction.congruence_pure,Extraction.productEraseKraus_encoded]
  change (pureMatrix (garbageVector k a)).trace • _=_
  rw [pureMatrix_trace,garbageVector_square]

theorem extractionOutput_purePower (k : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    extractionOutput k (pureMatrix (bitPurePower k z))=
      pureMatrix (Extraction.bellVector (Extraction.bellCoeff (Bits (bellPairYield k)))) := by
  rw [← bitPurePower_expansion,extractionOutput_coherent,
    pureOccupationCoefficients_square k z hz,Complex.ofReal_one,one_smul]

end EffectiveEncoding

