import CircuitRecursion.BellPairs

open scoped BigOperators
open Matrix CircuitCompletion SymmetricSupport
namespace CircuitRecursion

theorem coordinateIsometry_trans {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] (e : α ↪ β) (f : β ↪ γ) :
    Extraction.coordinateIsometry (e.trans f)=
      Extraction.coordinateIsometry f*Extraction.coordinateIsometry e := by
  ext w x
  simp [Extraction.coordinateIsometry,Matrix.mul_apply]

theorem extendVector_padding {α : Type*} [Fintype α] [DecidableEq α]
    {q r n : ℕ} (he : q+r=n) (h : q≤n) (e : α ↪ Bits q) (a : α → ℂ) :
    Extraction.coordinateIsometry (extendEmbedding h e)*ᵥa=
      fun b => (Extraction.coordinateIsometry e*ᵥa) (prefixBits (castBits he.symm b))*
        (Pi.single (zeroBits r) 1 : Bits r → ℂ) (suffixBits (castBits he.symm b)) := by
  subst n
  have hE : extendEmbedding h e=e.trans (padEmbedding r (Function.Embedding.refl (Bits q))) := by
    apply Function.Embedding.ext
    intro x
    exact extendBits_eq_pad h (e x)
  rw [hE,coordinateIsometry_trans,← Matrix.mulVec_mulVec,paddedVector]
  rfl

noncomputable def tailBellCircuit {q n h : ℕ} (he : q+originalWireCount h=n) : Circuit n :=
  castCircuit he (shiftCircuit q (bellPairsWord h))

theorem tailBellCircuit_action {q n h : ℕ} (he : q+originalWireCount h=n)
    (v : Bits q → ℂ) :
    run (tailBellCircuit he)
      (fun b => v (prefixBits (castBits he.symm b))*
        (Pi.single (zeroBits (originalWireCount h)) 1 : Bits (originalWireCount h) → ℂ)
          (suffixBits (castBits he.symm b)))=
      fun b => v (prefixBits (castBits he.symm b))*
        bellPairsVector h (suffixBits (castBits he.symm b)) := by
  have ht := run_castCircuit he (shiftCircuit q (bellPairsWord h))
    (fun b => v (prefixBits b)*
      (Pi.single (zeroBits (originalWireCount h)) 1 : Bits (originalWireCount h) → ℂ)
        (suffixBits b))
  rw [run_shiftCircuit,bellPairsWord_action] at ht
  exact ht

theorem tailBellCircuit_length {q n h : ℕ} (he : q+originalWireCount h=n) :
    (tailBellCircuit he).length=2*h := by
  rw [tailBellCircuit,castCircuit_length,shiftCircuit_length,bellPairsWord_length]

def bellPairYield (k : ℕ) : ℕ := k-encodingPairs k

theorem register_split (k : ℕ) :
    codeWires k+originalWireCount (bellPairYield k)=originalWireCount k := by
  rw [originalWireCount_eq,originalWireCount_eq]
  have h := encodingPairs_le_copy k
  unfold codeWires bellPairYield
  omega

/-- The final H/CNOT word operates on original zero pairs freed by the
proved compressor; the whole program is still one original-register list. -/
noncomputable def extractionCircuit (k : ℕ) : Circuit (originalWireCount k) :=
  compressionCircuit k++tailBellCircuit (register_split k)

noncomputable def extractionVector (k : ℕ) (a : Sym (Fin 4) k → ℂ) :
    Bits (originalWireCount k) → ℂ := fun b =>
  (Extraction.coordinateIsometry (compactEncoding k)*ᵥa)
    (prefixBits (castBits (register_split k).symm b))*
      bellPairsVector (bellPairYield k) (suffixBits (castBits (register_split k).symm b))

/-- One input-independent elementary circuit maps every coherent symmetric
input to a compact garbage vector times the exact Bell-pair output. -/
theorem extractionCircuit_coherent (k : ℕ) (a : Sym (Fin 4) k → ℂ) :
    run (extractionCircuit k) (bitOccupationMatrix k*ᵥa)=extractionVector k a := by
  rw [extractionCircuit,run_append,compressionCircuit_coherent]
  rw [originalEncoding,extendVector_padding (register_split k)]
  exact tailBellCircuit_action (register_split k) _

theorem extractionCircuit_purePower (k : ℕ) (z : Fin 4 → ℂ) :
    run (extractionCircuit k) (bitPurePower k z)=
      extractionVector k (pureOccupationCoefficients k z) := by
  rw [← bitPurePower_expansion,extractionCircuit_coherent]

theorem extractionCircuit_length (k : ℕ) :
    (extractionCircuit k).length≤recursiveGateBudget k := by
  rw [extractionCircuit,List.length_append,tailBellCircuit_length]
  have hc := compressionCircuit_length k
  have hy : bellPairYield k≤k := Nat.sub_le _ _
  have hk : 2*k≤100*k^2 := by cases k <;> nlinarith
  unfold recursiveGateBudget
  omega

/-- The polynomial/clog envelope now bounds the complete actual compression
plus Bell-preparation gate list, before local discarding. -/
theorem extractionCircuit_polynomial_bound (k : ℕ) :
    (extractionCircuit k).length≤
      20480*k*(k+2)^6*(6*Nat.clog 2 (k+3)+2)^2+100*k^2 :=
  (extractionCircuit_length k).trans (recursiveGateBudget_bound k)

end CircuitRecursion
