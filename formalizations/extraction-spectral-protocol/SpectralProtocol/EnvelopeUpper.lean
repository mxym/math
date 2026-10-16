import SpectralProtocol.DiagonalData
import SpectralProtocol.GeneralPureGuarantee

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

/-- A sorted actual effect diagonal obeys every prefix-width cap. -/
theorem sorted_diagonal_le_prefixWidth {N : ℕ} (a b K : ℕ) (hK : 0 < K)
    (z : Fin N → ℝ) (hmono : Antitone z)
    (hz : ∀ i,0 ≤ z i ∧ z i ≤ 1 ∧ z i ≤ (a:ℝ)/K)
    (hb : ∑ i,z i^2 ≤ ((a:ℝ)*b)/(K:ℝ)^2) (i : Fin N) :
    z i ≤ prefixWidth a b K (i.val+1)/K := by
  have hKpos : 0 < (K:ℝ) := by exact_mod_cast hK
  have hrpos : 0 < ((i.val+1:ℕ):ℝ) := by positivity
  have hsq := antitone_entry_sq_budget z (fun j => (hz j).1) hmono _ hb i
  have hprod := (le_div_iff₀ (sq_pos_of_pos hKpos)).mp hsq
  have hsq' : (z i*(K:ℝ))^2 ≤ ((a:ℝ)*b)/((i.val+1:ℕ):ℝ) := by
    apply (le_div_iff₀ hrpos).mpr
    push_cast at hprod ⊢
    nlinarith [hprod]
  have hs : z i ≤ Real.sqrt (((a:ℝ)*b)/((i.val+1:ℕ):ℝ))/K :=
    (le_div_iff₀ hKpos).mpr (Real.le_sqrt_of_sq_le hsq')
  rw [prefixWidth_div_target a b K (i.val+1) hK]
  exact le_min (hz i).2.1 (le_min (hz i).2.2 hs)

/-- The harmonic spectral envelope upper bound is a theorem of actual matrix
order and Hilbert--Schmidt constraints, with no trace rearrangement premise. -/
theorem actual_effect_harmonic_envelope (a b K : ℕ) (hK : 0 < K)
    (X M : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.PosSemidef)
    (hM : M.PosSemidef) (hI : (1-M).PosSemidef)
    (hcap : (((a:ℝ)/K) • (1:Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)-M).PosSemidef)
    (hbudget : (M*M).trace.re ≤ ((a:ℝ)*b)/(K:ℝ)^2)
    (hN : 0 < Fintype.card (Fin a × Fin b)) :
    (M*X).trace.re ≤ harmonicFactor (Fintype.card (Fin a × Fin b))*
      oneShotSpectralEnvelope a b K X hX.isHermitian hN := by
  classical
  obtain ⟨z,hpair,hz,hb⟩ := actual_effect_diagonal_data X M hX hM hI _ _ hcap hbudget
  let σ := Tuple.sort (fun j => -z j)
  let zz := fun i => z (σ i)
  have hzz : Antitone zz := by
    intro i j hij
    have h := Tuple.monotone_sort (fun j => -z j) hij
    change -z (σ i) ≤ -z (σ j) at h
    change z (σ j) ≤ z (σ i)
    linarith
  have hzb : (∑ i,zz i^2) ≤ ((a:ℝ)*b)/(K:ℝ)^2 := by
    calc
      _ = ∑ i,z i^2 := Equiv.sum_comp σ (fun i => z i^2)
      _ ≤ _ := hb
  rw [hpair]
  apply harmonic_prefix_comparison hX.isHermitian.eigenvalues₀ z
    (fun i => prefixWidth a b K (i.val+1)/K)
    (oneShotSpectralEnvelope a b K X hX.isHermitian hN)
    hX.isHermitian.eigenvalues₀_antitone
  · intro i
    let e : Fin (Fintype.card (Fin a × Fin b)) ≃ (Fin a × Fin b) :=
      Fintype.equivOfCardEq (Fintype.card_fin _)
    have h := hX.eigenvalues_nonneg (e i)
    simpa only [Matrix.IsHermitian.eigenvalues,e,Equiv.symm_apply_apply] using h
  · intro i
    unfold prefixWidth
    positivity
  · intro i
    change prefixFidelityValue a b K X hX.isHermitian i ≤
      Finset.univ.sup' _ (prefixFidelityValue a b K X hX.isHermitian)
    exact Finset.le_sup' _ (Finset.mem_univ i)
  · intro i
    exact sorted_diagonal_le_prefixWidth a b K hK zz hzz (fun j => hz (σ j)) hzb i

/-- The physical H_N T_K upper bound, uniformly over every original-space
unitary and every actual trace-preserving finite PPT Kraus channel. Together
with oneShotSpectralEnvelope_actual_lower this closes both physical sides of
the paper's finite one-shot spectral comparison. -/
theorem oneShotSpectralEnvelope_actual_upper (a b K : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hK : 0 < K)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.PosSemidef)
    {κ : Type*} [Fintype κ]
    (A : κ → Matrix (Fin K × Fin K) (Fin a × Fin b) ℂ)
    (hcomplete : ∑ j,(A j)ᴴ*A j=1) (hpt : Extraction.PTConjugatePositive A)
    (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ) :
    let hN : 0 < Fintype.card (Fin a × Fin b) := by
      simpa only [Fintype.card_prod,Fintype.card_fin] using Nat.mul_pos ha hb
    (Extraction.bellProjector (d := Fin K)*Extraction.krausApply A
      ((U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)*X*
        (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ)).trace.re ≤
      harmonicFactor (Fintype.card (Fin a × Fin b))*
        oneShotSpectralEnvelope a b K X hX.isHermitian hN := by
  dsimp only
  letI : Nonempty (Fin K) := ⟨⟨0,hK⟩⟩
  let M := preprocessedEffect A U
  have hU : (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ*U=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have hR : Extraction.RainsEffect K (Extraction.targetEffect A) := by
    simpa only [Fintype.card_fin] using Extraction.targetEffect_rains A hcomplete hpt
  have hM : M.PosSemidef := hR.1.conjTranspose_mul_mul_same _
  have hI : (1-M).PosSemidef := one_sub_preprocessedEffect_posSemidef A hcomplete hpt U
  have hcap : (((a:ℝ)/K) • (1:Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)-M).PosSemidef := by
    have hcap₀ := ExtractionLocalCap.rainsEffect_local_order_cap K (Extraction.targetEffect A) hR
    have h := hcap₀.conjTranspose_mul_mul_same (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)
    simpa only [Fintype.card_fin,M,preprocessedEffect,Matrix.mul_sub,Matrix.sub_mul,
      Matrix.mul_smul,Matrix.smul_mul,Matrix.mul_one,hU] using h
  have hbudget : (M*M).trace.re ≤ ((a:ℝ)*b)/(K:ℝ)^2 := by
    have he : (M*M).trace=(Extraction.targetEffect A*Extraction.targetEffect A).trace :=
      ExtractionSpectrum.trace_square_unitary_congruence _ U
    rw [he]
    simpa only [Fintype.card_fin] using Extraction.rainsEffect_trace_square_le K _ hR
  rw [preprocessedEffect_pairing]
  exact actual_effect_harmonic_envelope a b K hK X M hX hM hI hcap hbudget _

end SpectralProtocol