import CircuitRecursion.PhysicalCoordinates
import CircuitCompletion.OperatorError
import SymmetricSupport.UnitSpan

open scoped BigOperators
open Matrix CircuitCompletion SymmetricSupport
namespace CircuitRecursion

noncomputable def garbageVector (k : ℕ) (a : Sym (Fin 4) k → ℂ) :
    Bits (encodingPairs k)×Bits (encodingPairs k) → ℂ := fun z =>
  (Extraction.coordinateIsometry (compactEncoding k)*ᵥa) ((codePairCoordinates k).symm z)

theorem codeEmbedding_mulVec {d u v : Type*} [Fintype d] [Fintype u] [Fintype v]
    [DecidableEq d] [DecidableEq u] [DecidableEq v] (c : ℂ) (a : u×v → ℂ)
    (p : (d×u)×(d×v)) :
    (Extraction.codeEmbedding c*ᵥa) p=
      Extraction.bellVector c (p.1.1,p.2.1)*a (p.1.2,p.2.2) := by
  rcases p with ⟨⟨x,j⟩,⟨y,l⟩⟩
  simp [Extraction.codeEmbedding,Extraction.bellCode,Matrix.mulVec,dotProduct,
    Fintype.sum_prod_type,ite_mul,mul_comm]

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

theorem bitPurePower_square (k : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    vectorSquare (bitPurePower k z)=1 := by
  have ht := unitVector_trace 4 k z hz
  change (pureMatrix (purePower 4 k z)).trace=1 at ht
  rw [pureMatrix_trace] at ht
  have hp : vectorSquare (purePower 4 k z)=1 := by exact_mod_cast ht
  have hs := (originalBitCoordinates k).symm.sum_comp
    (fun w => Complex.normSq (purePower 4 k z w))
  exact hs.trans hp

theorem pureOccupationCoefficients_square (k : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    vectorSquare (pureOccupationCoefficients k z)=1 := by
  have ht := vectorSquare_unitary (denote (compressionCircuit k)) (bitPurePower k z)
  change vectorSquare (run (compressionCircuit k) (bitPurePower k z))=_ at ht
  rw [compressionCircuit_purePower,
    vectorSquare_isometry _ (Extraction.coordinateIsometry_isometry _)] at ht
  exact ht.trans (bitPurePower_square k z hz)

/-- After the one actual global gate word, the only quantum operation is
the explicit product family of local coordinate-discard Kraus operators. -/
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

/-- Exact uniform Bell extraction from every actual normalized unknown
pure two-qubit iid input, by the constructed original-wire word and local discard. -/
theorem extractionOutput_purePower (k : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    extractionOutput k (pureMatrix (bitPurePower k z))=
      pureMatrix (Extraction.bellVector (Extraction.bellCoeff (Bits (bellPairYield k)))) := by
  rw [← bitPurePower_expansion,extractionOutput_coherent,
    pureOccupationCoefficients_square k z hz,Complex.ofReal_one,one_smul]

end CircuitRecursion
