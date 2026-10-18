import CircuitRecursion.Growth
import CircuitCompletion.PhysicalError

open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open Matrix CircuitCompletion SymmetricSupport
namespace CircuitRecursion

noncomputable def discardOutput (k : ℕ)
    (X : Matrix (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ) :=
  Extraction.krausApply (Extraction.productEraseKraus
    (d := Bits (bellPairYield k)) (u := Bits (encodingPairs k)) (v := Bits (encodingPairs k)))
      (Matrix.reindexAlgEquiv ℂ ℂ (readoutCoordinates k) X)

noncomputable def approximateExtractionOutput (k : ℕ)
    (V : Matrix.unitaryGroup (Bits (originalWireCount k)) ℂ)
    (X : Matrix (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ) :=
  discardOutput k ((V : Matrix (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ)*X*
    (V : Matrix (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ)ᴴ)

noncomputable def discardEffect (k : ℕ) :
    Matrix (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ :=
  (Matrix.reindexAlgEquiv ℂ ℂ (readoutCoordinates k)).symm
    (Extraction.targetEffect (Extraction.productEraseKraus
      (d := Bits (bellPairYield k)) (u := Bits (encodingPairs k)) (v := Bits (encodingPairs k))))

theorem discardEffect_bounds (k : ℕ) :
    (discardEffect k).PosSemidef ∧ (1-discardEffect k).PosSemidef := by
  have hpt : Extraction.PTConjugatePositive (Extraction.productEraseKraus
      (d := Bits (bellPairYield k)) (u := Bits (encodingPairs k)) (v := Bits (encodingPairs k))) :=
    SpectralProtocol.productKraus_PTConjugatePositive _ _
  have hb := Extraction.targetEffect_rains _ Extraction.productEraseKraus_complete hpt
  constructor
  · exact hb.1.submatrix (readoutCoordinates k)
  · have ht := hb.2.1.submatrix (readoutCoordinates k)
    change ((Matrix.reindexAlgEquiv ℂ ℂ (readoutCoordinates k)).symm (1-Extraction.targetEffect
      (Extraction.productEraseKraus (d := Bits (bellPairYield k))
        (u := Bits (encodingPairs k)) (v := Bits (encodingPairs k))))).PosSemidef at ht
    simpa only [map_sub,map_one,discardEffect] using ht

theorem discardEffect_pairing (k : ℕ)
    (X : Matrix (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ) :
    (discardEffect k*X).trace.re=
      (Extraction.bellProjector (d := Bits (bellPairYield k))*discardOutput k X).trace.re := by
  rw [discardOutput,Extraction.target_overlap_eq]
  have he : (discardEffect k*X).trace=
      (Extraction.targetEffect (Extraction.productEraseKraus
        (d := Bits (bellPairYield k)) (u := Bits (encodingPairs k)) (v := Bits (encodingPairs k)))*
          Matrix.reindexAlgEquiv ℂ ℂ (readoutCoordinates k) X).trace := by
    rw [← SpectralProtocol.reindex_trace (readoutCoordinates k)]
    change (Matrix.reindexAlgEquiv ℂ ℂ (readoutCoordinates k) (discardEffect k*X)).trace=_
    rw [map_mul,discardEffect,AlgEquiv.apply_symm_apply]
  exact congrArg Complex.re he

theorem extractionOutput_fidelity_one (k : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    (Extraction.bellProjector (d := Bits (bellPairYield k))*
      extractionOutput k (pureMatrix (bitPurePower k z))).trace.re=1 := by
  rw [extractionOutput_purePower k z hz]
  change (Extraction.bellProjector (d := Bits (bellPairYield k))*Extraction.bellProjector).trace.re=1
  rw [Extraction.bellProjector_idempotent]
  exact congrArg Complex.re (Extraction.bellProjector_density (d := Bits (bellPairYield k))).2

/-- Uniform error bound for this actual final program and its actual local
discard channel. The approximation hypothesis concerns the literal program
matrix; no synthesis-existence or calibration assertion is assumed. -/
theorem extractionOutput_robust (k : ℕ)
    (V : Matrix.unitaryGroup (Bits (originalWireCount k)) ℂ)
    (z : Fin 4 → ℂ) (hz : IsUnitVector z) (δ : ℝ) (hδ : 0≤δ)
    (hUV : ‖(denote (extractionCircuit k) : Matrix (Bits (originalWireCount k))
      (Bits (originalWireCount k)) ℂ)-V‖≤δ) :
    1-2*δ≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k V (pureMatrix (bitPurePower k z))).trace.re := by
  have hpre (W : Matrix.unitaryGroup (Bits (originalWireCount k)) ℂ) :
      (discardEffect k*pureMatrix ((W : Matrix (Bits (originalWireCount k))
        (Bits (originalWireCount k)) ℂ)*ᵥbitPurePower k z)).trace.re=
      (Extraction.bellProjector (d := Bits (bellPairYield k))*
        approximateExtractionOutput k W (pureMatrix (bitPurePower k z))).trace.re := by
    rw [discardEffect_pairing]
    have hc : pureMatrix ((W : Matrix (Bits (originalWireCount k))
        (Bits (originalWireCount k)) ℂ)*ᵥbitPurePower k z)=
        (W : Matrix (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ)*
          pureMatrix (bitPurePower k z)*(W : Matrix (Bits (originalWireCount k))
            (Bits (originalWireCount k)) ℂ)ᴴ := (Extraction.congruence_pure _ _).symm
    rw [hc]
    rfl
  have hb := discardEffect_bounds k
  have hz' := bitPurePower_square k z hz
  rw [← hpre V]
  apply exact_effect_fidelity_lower_delta (discardEffect k) hb.1 hb.2 _ _
    ((vectorSquare_unitary (denote (extractionCircuit k)) _).trans hz')
    ((vectorSquare_unitary V _).trans hz') ?_ δ hδ
    (operator_error_controls_vector _ _ _ hz' δ hδ hUV)
  rw [hpre]
  exact extractionOutput_fidelity_one k z hz

theorem extractionOutput_robust_up_to_phase (k : ℕ)
    (V : Matrix.unitaryGroup (Bits (originalWireCount k)) ℂ)
    (z : Fin 4 → ℂ) (hz : IsUnitVector z) (δ : ℝ) (hδ : 0≤δ)
    (c : ℂ) (hc : Complex.normSq c=1)
    (hUV : ‖(denote (extractionCircuit k) : Matrix (Bits (originalWireCount k))
      (Bits (originalWireCount k)) ℂ)-c • (V : Matrix (Bits (originalWireCount k))
        (Bits (originalWireCount k)) ℂ)‖≤δ) :
    1-2*δ≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k V (pureMatrix (bitPurePower k z))).trace.re := by
  have ht := extractionOutput_robust k (phaseUnitary c hc V) z hz δ hδ hUV
  simpa only [approximateExtractionOutput,phaseUnitary_congruence] using ht

theorem compiledExtraction_error (k : ℕ)
    (compile : Gate (originalWireCount k) → Circuit (originalWireCount k)) (ε : ℝ)
    (heach : ∀ g∈extractionCircuit k,
      ‖(denote (compile g) : Matrix (Bits (originalWireCount k))
        (Bits (originalWireCount k)) ℂ)-g.denote‖≤ε) :
    ‖(denote ((extractionCircuit k).flatMap compile) : Matrix (Bits (originalWireCount k))
      (Bits (originalWireCount k)) ℂ)-denote (extractionCircuit k)‖≤
        (extractionCircuit k).length*ε := by
  apply (compiled_word_error compile (extractionCircuit k)).trans
  have ht := List.sum_le_length_nsmul
    ((extractionCircuit k).map (fun g => ‖(denote (compile g) : Matrix
      (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ)-g.denote‖)) ε (by
        intro x hx
        obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hx
        exact heach g hg)
  simpa only [List.length_map,nsmul_eq_mul] using ht

/-- Literal per-gate replacement accuracy δ/G gives the claimed uniform
fidelity for the actual final word and the same local discard channel. -/
theorem compiledExtraction_fidelity (k : ℕ)
    (compile : Gate (originalWireCount k) → Circuit (originalWireCount k))
    (z : Fin 4 → ℂ) (hz : IsUnitVector z) (δ : ℝ) (hδ : 0≤δ)
    (heach : ∀ g∈extractionCircuit k,
      ‖(denote (compile g) : Matrix (Bits (originalWireCount k))
        (Bits (originalWireCount k)) ℂ)-g.denote‖≤δ/(extractionCircuit k).length) :
    1-2*δ≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
      approximateExtractionOutput k (denote ((extractionCircuit k).flatMap compile))
        (pureMatrix (bitPurePower k z))).trace.re := by
  apply extractionOutput_robust k _ z hz δ hδ
  rw [norm_sub_rev]
  apply (compiledExtraction_error k compile _ heach).trans
  by_cases hn : (extractionCircuit k).length=0
  · simp [hn,hδ]
  · have hn' : ((extractionCircuit k).length : ℝ)≠0 := by exact_mod_cast hn
    have he : ((extractionCircuit k).length : ℝ)*(δ/(extractionCircuit k).length)=δ := by
      field_simp
    exact he.le

theorem compiledExtraction_length (k L : ℕ)
    (compile : Gate (originalWireCount k) → Circuit (originalWireCount k))
    (hL : ∀ g∈extractionCircuit k,(compile g).length≤L) :
    ((extractionCircuit k).flatMap compile).length≤recursiveGateBudget k*L := by
  rw [compiled_word_length]
  have ht := List.sum_le_length_nsmul ((extractionCircuit k).map (fun g => (compile g).length)) L (by
    intro x hx
    obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hx
    exact hL g hg)
  have hs : ((extractionCircuit k).map (fun g => (compile g).length)).sum≤
      (extractionCircuit k).length*L := by simpa [List.length_map,nsmul_eq_mul] using ht
  exact hs.trans (Nat.mul_le_mul_right L (extractionCircuit_length k))

end CircuitRecursion
