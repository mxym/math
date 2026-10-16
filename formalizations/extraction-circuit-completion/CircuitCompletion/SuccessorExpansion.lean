import CircuitCompletion.NormalizedBranch
import CircuitCompletion.Spectators

open scoped BigOperators Kronecker
open Matrix SymmetricSupport
namespace CircuitCompletion

noncomputable def successorVector {k : ℕ} (ν : Sym (Fin 4) (k+1)) : Fin 4×Word 4 k → ℂ :=
  fun p => occupationVector ν (Fin.cons p.1 p.2)

noncomputable def successorCodeVector {k : ℕ} (enc : Sym (Fin 4) k ↪ Word 4 k)
    (ν : Sym (Fin 4) (k+1)) : Fin 4×Word 4 k → ℂ :=
  fun p => if hi : p.1∈ν then (Real.sqrt (occupationMass ν p.1) : ℂ)*
    (Pi.single (enc (ν.erase p.1 hi)) 1 : Word 4 k → ℂ) p.2 else 0

/-- The coherent induction step is proved on actual original occupation
vectors. The previous-stage compression hypothesis is precisely stated;
it is not a claim that the all-k recursion has already been constructed. -/
theorem successor_stage_expansion {k : ℕ} (enc : Sym (Fin 4) k ↪ Word 4 k)
    (U : Matrix (Word 4 k) (Word 4 k) ℂ)
    (hU : ∀ mu,U*ᵥoccupationVector mu=Pi.single (enc mu) 1)
    (ν : Sym (Fin 4) (k+1)) :
    ((1 : Matrix (Fin 4) (Fin 4) ℂ) ⊗ₖ U)*ᵥsuccessorVector ν=successorCodeVector enc ν := by
  classical
  ext p
  rcases p with ⟨i,w⟩
  simp only [Matrix.mulVec,dotProduct,Fintype.sum_prod_type,Matrix.kronecker_apply,Matrix.one_apply]
  simp only [ite_mul,one_mul,zero_mul]
  simp only [successorVector,occupationVector_branch]
  simp only [Finset.sum_ite_irrel,Finset.sum_const_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  by_cases hi : i∈ν
  · simp only [dif_pos hi]
    have hterm (z : Word 4 k) :
        U w z*((Real.sqrt ((ν.val.count i : ℝ)/(k+1)) : ℂ)*occupationVector (ν.erase i hi) z)=
        (Real.sqrt ((ν.val.count i : ℝ)/(k+1)) : ℂ)*(U w z*occupationVector (ν.erase i hi) z) := by ring
    simp only [hterm,← Finset.mul_sum]
    change (Real.sqrt ((ν.val.count i : ℝ)/(k+1)) : ℂ)*
      (U*ᵥoccupationVector (ν.erase i hi)) w=_
    rw [hU]
    simp [successorCodeVector,hi,occupationMass]
  · simp [hi,successorCodeVector]

end CircuitCompletion
