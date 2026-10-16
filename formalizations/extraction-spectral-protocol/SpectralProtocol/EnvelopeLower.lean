import SpectralProtocol.PackingRounding

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The ordered eigenvalue enumeration uses precisely Mathlib's native spectral
ordering, rather than a caller-provided sorted-spectrum certificate. -/
noncomputable def spectralPrefixEmbedding (r : ℕ) (hr : r ≤ Fintype.card ι) : Fin r ↪ ι :=
  (Fin.castLEEmb hr).trans
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).toEmbedding

noncomputable def spectralPrefixIndices (r : ℕ) (hr : r ≤ Fintype.card ι) : Finset ι :=
  Finset.univ.map (spectralPrefixEmbedding r hr)

theorem spectralPrefixIndices_card (r : ℕ) (hr : r ≤ Fintype.card ι) :
    (spectralPrefixIndices r hr : Finset ι).card = r := by
  simp only [spectralPrefixIndices, Finset.card_map, Finset.card_univ, Fintype.card_fin]

noncomputable def spectralPrefixMass (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (r : ℕ) (hr : r ≤ Fintype.card ι) : ℝ :=
  ∑ i : Fin r, hX.eigenvalues₀ (Fin.castLE hr i)

theorem spectralPrefixIndices_sum (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (r : ℕ) (hr : r ≤ Fintype.card ι) :
    (∑ i ∈ spectralPrefixIndices r hr, hX.eigenvalues i) = spectralPrefixMass X hX r hr := by
  simp only [spectralPrefixIndices, Finset.sum_map, spectralPrefixMass]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.IsHermitian.eigenvalues, spectralPrefixEmbedding,
    Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.symm_apply_apply]
  rfl

/-- Prefix fidelity value, with the paper's exact continuous Bell-dimension
budget divided by the actual integer target dimension. -/
noncomputable def prefixFidelityValue (a b K : ℕ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.IsHermitian)
    (i : Fin (Fintype.card (Fin a × Fin b))) : ℝ :=
  prefixWidth a b K (i.val+1) / K *
    spectralPrefixMass X hX (i.val+1) (by omega)

/-- The width ratio is exactly the paper's v_r, with all three caps. -/
theorem prefixWidth_div_target (a b K r : ℕ) (hK : 0 < K) :
    prefixWidth a b K r / K =
      min 1 (min ((a:ℝ)/K) (Real.sqrt (((a:ℝ)*b)/r)/K)) := by
  have hKpos : 0 < (K:ℝ) := by exact_mod_cast hK
  unfold prefixWidth
  rw [← min_div_div_right hKpos.le, ← min_div_div_right hKpos.le,
    div_self hKpos.ne']
  exact min_left_comm _ _ _

/-- Finite maximum over every actual ordered spectral prefix. -/
noncomputable def oneShotSpectralEnvelope (a b K : ℕ)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.IsHermitian)
    (hN : 0 < Fintype.card (Fin a × Fin b)) : ℝ :=
  Finset.univ.sup' ⟨⟨0,hN⟩, Finset.mem_univ _⟩ (prefixFidelityValue a b K X hX)

/-- The T_K/4 lower bound from the paper is attained by one actual original-space
unitary and two complete local channels. The maximizing prefix and its genuine
spectral projection are constructed internally. -/
theorem oneShotSpectralEnvelope_actual_lower (a b K : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hK : 0 < K) (hab : a ≤ b)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.PosSemidef) :
    let hN : 0 < Fintype.card (Fin a × Fin b) := by
      simpa only [Fintype.card_prod, Fintype.card_fin] using Nat.mul_pos ha hb
    ∃ (d : ℕ) (hd : 0 < d) (hdk : d ≤ K)
      (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
      (A : Fin (a/d) ⊕ Fin a → Matrix (Fin K) (Fin a) ℂ)
      (B : Fin (b/d) ⊕ Fin b → Matrix (Fin K) (Fin b) ℂ),
      (∑ j,(A j)ᴴ*A j=1) ∧ (∑ j,(B j)ᴴ*B j=1) ∧
      oneShotSpectralEnvelope a b K X hX.isHermitian hN / 4 ≤
        (Extraction.bellProjector (d := Fin K) *
          Extraction.krausApply (Extraction.productKraus A B)
            ((U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) * X *
              (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ)).trace.re := by
  dsimp only
  let hN : 0 < Fintype.card (Fin a × Fin b) := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using Nat.mul_pos ha hb
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup'
    (show (Finset.univ : Finset (Fin (Fintype.card (Fin a × Fin b)))).Nonempty
      from ⟨⟨0,hN⟩,Finset.mem_univ _⟩) (prefixFidelityValue a b K X hX.isHermitian)
  let s := spectralPrefixIndices (ι := Fin a × Fin b) (i.val+1) (by omega)
  have hs : s.card=i.val+1 := spectralPrefixIndices_card _ _
  have hspos : 0 < s.card := by omega
  obtain ⟨d,hd,hdk,U,A,B,hA,hB,he⟩ := spectral_subset_quarter_lower a b K ha hb hK hab X hX s hspos
  refine ⟨d,hd,hdk,U,A,B,hA,hB,?_⟩
  change Finset.univ.sup' _ (prefixFidelityValue a b K X hX.isHermitian) / 4 ≤ _
  rw [hi]
  simp only [prefixFidelityValue]
  have hsum : (∑ j ∈ s, hX.isHermitian.eigenvalues j) =
      spectralPrefixMass X hX.isHermitian (i.val+1) (by omega) := spectralPrefixIndices_sum _ _ _ _
  rw [hs,hsum] at he
  have heq : prefixWidth a b K (i.val+1)/(4*(K:ℝ))*
      spectralPrefixMass X hX.isHermitian (i.val+1) (by omega) =
      (prefixWidth a b K (i.val+1)/(K:ℝ)*
      spectralPrefixMass X hX.isHermitian (i.val+1) (by omega))/4 := by ring
  rwa [heq] at he

end SpectralProtocol