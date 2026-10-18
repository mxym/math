import CircuitRecursion.FiniteLibrary

open scoped Matrix.Norms.L2Operator
open Matrix CircuitCompletion SymmetricSupport
namespace CircuitRecursion

noncomputable def libraryPrecision (N : ℕ) (δ : ℝ) : ℕ :=
  ⌈Real.logb 2 (max 1 ((N : ℝ)/δ))⌉₊

theorem libraryPrecision_error (N : ℕ) (δ : ℝ) (hδ : 0<δ) :
    (N : ℝ)*(1/2 : ℝ)^libraryPrecision N δ≤δ := by
  let x := max 1 ((N : ℝ)/δ)
  have hx : 0<x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hp : Real.logb 2 x≤(libraryPrecision N δ : ℝ) := Nat.le_ceil _
  have ht : x≤(2 : ℝ)^(libraryPrecision N δ) := by
    have he := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ)<2) hx).mp hp
    simpa only [Real.rpow_natCast] using he
  have hratio : (N : ℝ)/δ≤(2 : ℝ)^libraryPrecision N δ := (le_max_right _ _).trans ht
  have hN := (div_le_iff₀ hδ).mp hratio
  rw [div_pow,one_pow,mul_one_div]
  exact (div_le_iff₀ (by positivity : (0 : ℝ)<2^libraryPrecision N δ)).mpr (by
    simpa only [mul_comm] using hN)

theorem libraryPrecision_bound (N : ℕ) (δ : ℝ) :
    (libraryPrecision N δ : ℝ)+1≤Real.logb 2 (max 1 ((N : ℝ)/δ))+2 := by
  have hlog : 0≤Real.logb 2 (max 1 ((N : ℝ)/δ)) :=
    Real.logb_nonneg (by norm_num) (le_max_left _ _)
  have ht := Nat.ceil_lt_add_one hlog
  change (libraryPrecision N δ : ℝ)<_ at ht
  linarith

/-- Complete finite-library approximation of the actual extraction word:
the output uses only the specified finite one-qubit library and CNOT on
the original 2k wires, has actual operator error at most δ up to phase,
and retains the same local-discard fidelity at least 1-2δ. The actual
word-length overhead is bounded by a fifth power of the displayed logarithm. -/
theorem finiteLibrary_extraction {m : ℕ} (G : Fin m → SU2)
    (hinv : ∀ i,∃ j,G j=(G i)⁻¹)
    (huniversal : Dense (Subgroup.closure (Set.range G) : Set SU2)) :
    ∃ C : ℕ,∀ (k : ℕ) (δ : ℝ),0<δ → ∃ b : Circuit (originalWireCount k),
      (∀ g∈b,usesFiniteLibrary G g) ∧
      (b.length : ℝ)≤(C : ℝ)*(extractionCircuit k).length*
        (Real.logb 2 (max 1 (((extractionCircuit k).length : ℝ)/δ))+2)^5 ∧
      ‖(denote (extractionCircuit k) : Matrix (Bits (originalWireCount k))
        (Bits (originalWireCount k)) ℂ)-circuitPhase (extractionCircuit k) •
          (denote b : Matrix (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ)‖≤δ ∧
      (∀ z : Fin 4 → ℂ,IsUnitVector z →
        1-2*δ≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
          approximateExtractionOutput k (denote b) (pureMatrix (bitPurePower k z))).trace.re) := by
  obtain ⟨C,hC,ha⟩ := finiteLibrary_wordApproximation G hinv huniversal
  refine ⟨C,fun k δ hδ => ?_⟩
  let N := (extractionCircuit k).length
  let p := libraryPrecision N δ
  obtain ⟨b,huses,hlen,herr⟩ := ha (originalWireCount k) (extractionCircuit k) p
  have herror : ‖(denote (extractionCircuit k) : Matrix (Bits (originalWireCount k))
      (Bits (originalWireCount k)) ℂ)-circuitPhase (extractionCircuit k) •
        (denote b : Matrix (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ)‖≤δ :=
    herr.trans (libraryPrecision_error N δ hδ)
  refine ⟨b,huses,?_,herror,fun z hz => ?_⟩
  · have hl : (b.length : ℝ)≤(C : ℝ)*(extractionCircuit k).length*(p+1 : ℕ)^5 := by
      exact_mod_cast hlen
    have hp : ((p+1 : ℕ) : ℝ)≤Real.logb 2 (max 1 (((extractionCircuit k).length : ℝ)/δ))+2 := by
      simpa only [Nat.cast_add,Nat.cast_one] using libraryPrecision_bound N δ
    exact hl.trans (by gcongr)
  · exact extractionOutput_robust_up_to_phase k (denote b) z hz δ hδ.le
      (circuitPhase (extractionCircuit k)) (circuitPhase_normalized _) herror

end CircuitRecursion
