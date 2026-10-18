import OperationalCompletion.CapacitySets
import LOCCInterface.Protocol

open scoped BigOperators ComplexOrder Topology
open Matrix MinimaxProfile ExtractionSpectrum
namespace OperationalCompletion
noncomputable section

/-- The class is the actual finite adaptive-instrument tree semantics, with
the global preprocessing unitary retained separately. -/
theorem finiteLOCC_capacities (m n : ℕ) (hm : 0<m) (hn : 0<n) (hmn : m≤n)
    (X : Matrix (Fin (m*n)) (Fin (m*n)) ℂ) (hX : X.PosSemidef ∧ X.trace=1) :
    faithfulCapacity m n (fun _ _ V => ExtractionLOCC.IsFiniteLOCCProtocol V) X =
        min (Real.log m) ((Real.log m+Real.log n-entropy hX.1.isHermitian.eigenvalues)/2) ∧
    exactCapacity m n (fun _ _ V => ExtractionLOCC.IsFiniteLOCCProtocol V) X =
        min (Real.log m) ((Real.log m+Real.log n-Real.log X.rank)/2) := by
  have hC : ∀ k K (hK : 0<K),ExtractionLOCC.IsFiniteLOCCProtocol
      (reservedProtocol m n k K hm hn hmn hK) := fun k K hK =>
    ExtractionLOCC.productLocal_isFiniteLOCCProtocol _
      (reservedProtocol_isProductLocal m n k K hm hn hmn hK)
  exact ⟨faithfulCapacity_eq m n hm hn hmn _ hC X hX,
    exactCapacity_eq m n hm hn hmn _ hC X hX⟩

end
end OperationalCompletion
