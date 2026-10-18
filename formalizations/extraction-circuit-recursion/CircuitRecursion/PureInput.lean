import CircuitRecursion.Compression
import SymmetricSupport.PureSpan

open scoped BigOperators
open Matrix CircuitCompletion SymmetricSupport
namespace CircuitRecursion

noncomputable def bitOccupationMatrix (k : ℕ) :
    Matrix (Bits (originalWireCount k)) (Sym (Fin 4) k) ℂ :=
  fun b ν => bitOccupation ν b

/-- One physical matrix compresses every coherent occupation column. -/
theorem compressionCircuit_matrix (k : ℕ) :
    (denote (compressionCircuit k) : Matrix (Bits (originalWireCount k))
      (Bits (originalWireCount k)) ℂ)*bitOccupationMatrix k=
        Extraction.coordinateIsometry (originalEncoding k) := by
  ext b ν
  have h := congrFun (compressionCircuit_action k ν) b
  simpa only [run,bitOccupationMatrix,Matrix.mul_apply,Matrix.mulVec,dotProduct,
    Extraction.coordinateIsometry,Pi.single_apply,eq_comm] using h

theorem compressionCircuit_coherent (k : ℕ) (a : Sym (Fin 4) k → ℂ) :
    run (compressionCircuit k) (bitOccupationMatrix k*ᵥa)=
      Extraction.coordinateIsometry (originalEncoding k)*ᵥa := by
  change (denote (compressionCircuit k) : Matrix (Bits (originalWireCount k))
    (Bits (originalWireCount k)) ℂ)*ᵥ(bitOccupationMatrix k*ᵥa)=_
  rw [Matrix.mulVec_mulVec,compressionCircuit_matrix]

noncomputable def pureOccupationCoefficients (k : ℕ) (z : Fin 4 → ℂ) :
    Sym (Fin 4) k → ℂ := fun ν =>
  (Real.sqrt (fiberCard (occupation 4 k) ν : ℝ) : ℂ)*monomialCoordinates 4 k z ν

noncomputable def bitPurePower (k : ℕ) (z : Fin 4 → ℂ) : Bits (originalWireCount k) → ℂ :=
  fun b => purePower 4 k z ((originalBitCoordinates k).symm b)

theorem bitPurePower_expansion (k : ℕ) (z : Fin 4 → ℂ) :
    bitOccupationMatrix k*ᵥpureOccupationCoefficients k z=bitPurePower k z := by
  classical
  funext b
  let w := (originalBitCoordinates k).symm b
  have hs : (Real.sqrt (fiberCard (occupation 4 k) (occupation 4 k w) : ℝ) : ℂ)≠0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact (Real.sqrt_pos.mpr (by
      exact_mod_cast fiberCard_pos (occupation 4 k) (occupation_surjective 4 k)
        (occupation 4 k w))).ne'
  have hm := congrFun (purePower_occupationCoordinates 4 k z) w
  simp only [Matrix.mulVec,dotProduct,occupationColumns,ite_mul,one_mul,zero_mul,
    Finset.sum_ite_eq,Finset.mem_univ,ite_true] at hm
  change (∑ ν,(if occupation 4 k w=ν then
    ((Real.sqrt (fiberCard (occupation 4 k) ν : ℝ))⁻¹ : ℂ) else 0)*
      ((Real.sqrt (fiberCard (occupation 4 k) ν : ℝ) : ℂ)*monomialCoordinates 4 k z ν))=_
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true,
    Complex.ofReal_inv]
  rw [← mul_assoc,inv_mul_cancel₀ hs,one_mul]
  exact hm

/-- The actual unknown pure iid amplitudes, in the explicitly fixed paired
original-bit convention, are compressed by the same word for every z. -/
theorem compressionCircuit_purePower (k : ℕ) (z : Fin 4 → ℂ) :
    run (compressionCircuit k) (bitPurePower k z)=
      Extraction.coordinateIsometry (originalEncoding k)*ᵥpureOccupationCoefficients k z := by
  rw [← bitPurePower_expansion,compressionCircuit_coherent]

end CircuitRecursion
