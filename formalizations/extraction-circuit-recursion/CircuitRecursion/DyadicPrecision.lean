import CircuitRecursion.OccupationArithmetic

open scoped Matrix.Norms.L2Operator
open Matrix CircuitCompletion SymmetricSupport
namespace CircuitRecursion

/-- A finite integer precision schedule. This definition computes only the
precision budget; it is not a synthesis algorithm. -/
def dyadicCircuitPrecision (N p : ℕ) : ℕ := p+Nat.clog 2 (max 1 N)

theorem dyadicCircuitPrecision_error (N p : ℕ) :
    (N:ℝ)*(1/2:ℝ)^dyadicCircuitPrecision N p≤(1/2:ℝ)^p := by
  let q := Nat.clog 2 (max 1 N)
  have ht : max 1 N≤2^q := Nat.le_pow_clog (by decide) _
  have ht' : ((max 1 N:ℕ):ℝ)≤(2:ℝ)^q := by exact_mod_cast ht
  have hN : (N:ℝ)≤(2:ℝ)^q :=
    (Nat.cast_le.mpr (le_max_right 1 N)).trans ht'
  change (N:ℝ)*(1/2:ℝ)^(p+q)≤_
  calc
    _=((N:ℝ)*(1/2:ℝ)^q)*(1/2:ℝ)^p := by rw [pow_add]; ring
    _≤((2:ℝ)^q*(1/2:ℝ)^q)*(1/2:ℝ)^p := by gcongr
    _=(1/2:ℝ)^p := by rw [← mul_pow]; norm_num

/-- A finite-precision request for the already proved extraction existence
theorem, expressed entirely by integers. No effective word search or
classical bit-cost claim is added. -/
theorem finiteLibrary_extraction_precision {m : ℕ} (G : Fin m → SU2)
    (hinv : ∀ i,∃ j,G j=(G i)⁻¹)
    (huniversal : Dense (Subgroup.closure (Set.range G) : Set SU2)) :
    ∃ C : ℕ,∀ k p : ℕ,∃ b : Circuit (originalWireCount k),
      (∀ g∈b,usesFiniteLibrary G g) ∧
      b.length≤C*(extractionCircuit k).length*
        (dyadicCircuitPrecision (extractionCircuit k).length p+1)^5 ∧
      ‖(denote (extractionCircuit k) : Matrix (Bits (originalWireCount k))
        (Bits (originalWireCount k)) ℂ)-circuitPhase (extractionCircuit k) •
          (denote b : Matrix (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ)‖≤(1/2:ℝ)^p ∧
      (∀ z : Fin 4 → ℂ,IsUnitVector z →
        1-2*(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
          approximateExtractionOutput k (denote b) (pureMatrix (bitPurePower k z))).trace.re) := by
  obtain ⟨C,hC,ha⟩ := finiteLibrary_wordApproximation G hinv huniversal
  refine ⟨C,fun k p => ?_⟩
  obtain ⟨b,huses,hlen,herr⟩ := ha (originalWireCount k) (extractionCircuit k)
    (dyadicCircuitPrecision (extractionCircuit k).length p)
  have he := herr.trans (dyadicCircuitPrecision_error (extractionCircuit k).length p)
  refine ⟨b,huses,hlen,he,fun z hz => ?_⟩
  exact extractionOutput_robust_up_to_phase k (denote b) z hz _ (by positivity)
    (circuitPhase (extractionCircuit k)) (circuitPhase_normalized _) he

end CircuitRecursion
