import SpectralProtocol.GeneralPureGuarantee
import Spectrum.Tensor
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators ComplexOrder
open Matrix
namespace CircuitCompletion

def splitCopies (α β : Type*) (k : ℕ) :
    (Fin k → α×β) ≃ ((Fin k → α)×(Fin k → β)) where
  toFun w := (fun i => (w i).1,fun i => (w i).2)
  invFun p i := (p.1 i,p.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Explicit copywise digit coordinates, rather than a cardinality choice. -/
def copywiseCoordinates (m n k : ℕ) :
    (Fin k → Fin (m*n)) ≃ (Fin (m^k)×Fin (n^k)) where
  toFun w := (finFunctionFinEquiv (fun i => (finProdFinEquiv.symm (w i)).1),
    finFunctionFinEquiv (fun i => (finProdFinEquiv.symm (w i)).2))
  invFun p i := finProdFinEquiv (finFunctionFinEquiv.symm p.1 i,finFunctionFinEquiv.symm p.2 i)
  left_inv w := by
    funext i
    simp only [Equiv.symm_apply_apply]
    exact finProdFinEquiv.apply_symm_apply (w i)
  right_inv p := by rcases p with ⟨a,b⟩;apply Prod.ext <;> simp

noncomputable def copywiseInput (m n k : ℕ) (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) :=
  Matrix.reindexAlgEquiv ℂ ℂ (copywiseCoordinates m n k) (ExtractionSpectrum.tensorMatrix X k)

/-- Its entries are literally the kth iid product in each pair of original
copy coordinates. The local integer coordinates use base-m and base-n digits. -/
theorem copywiseInput_entry (m n k : ℕ) (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ)
    (a a' : Fin (m^k)) (b b' : Fin (n^k)) :
    copywiseInput m n k X (a,b) (a',b')=
      ∏ i : Fin k,X (finProdFinEquiv (finFunctionFinEquiv.symm a i,finFunctionFinEquiv.symm b i))
        (finProdFinEquiv (finFunctionFinEquiv.symm a' i,finFunctionFinEquiv.symm b' i)) := rfl

theorem copywiseInput_density (m n k : ℕ) (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ)
    (hX : X.PosSemidef ∧ X.trace=1) : APPT.Quantum.IsDensity (copywiseInput m n k X) := by
  have h := ExtractionSpectrum.tensorMatrix_density X hX k
  refine ⟨h.1.submatrix (copywiseCoordinates m n k).symm,?_⟩
  rw [copywiseInput,SpectralProtocol.reindex_trace]
  exact h.2

/-- One fixed relabelling connects the earlier coordinate convention
with literal copywise tensor coordinates; it is independent of every input. -/
noncomputable def canonicalRelabel (m n k : ℕ) :
    (Fin (m^k)×Fin (n^k)) ≃ (Fin (m^k)×Fin (n^k)) :=
  (SpectralProtocol.bipartitePowerCoordinates m n k).symm.trans (copywiseCoordinates m n k)

theorem reindex_old_tensorInput_eq_copywise (m n k : ℕ)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) :
    Matrix.reindexAlgEquiv ℂ ℂ (canonicalRelabel m n k)
      (SpectralProtocol.bipartitePowerTransport m n k (ExtractionSpectrum.tensorMatrix X k))=
        copywiseInput m n k X := by
  ext x y
  simp [Matrix.reindexAlgEquiv_apply,Matrix.reindex_apply,canonicalRelabel,
    SpectralProtocol.bipartitePowerTransport,copywiseInput]

end CircuitCompletion
