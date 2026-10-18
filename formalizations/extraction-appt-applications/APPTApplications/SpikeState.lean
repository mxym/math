import APPTApplications.Purity
import APPTReview.SchmidtModel

open scoped BigOperators ComplexOrder Topology
open Matrix
namespace ExtractionAPPT
noncomputable section

/-- Each off-diagonal Schmidt product is at most one half, directly from the
normalization of the actual Schmidt coefficients. -/
theorem schmidt_product_le_half {ι : Type} [Fintype ι] [DecidableEq ι]
    (s : ι → ℝ) (hs : ∑ i, (s i)^2 = 1) (i j : ι) (hij : i ≠ j) :
    s i * s j ≤ 1/2 := by
  have hsum : (s i)^2 + (s j)^2 ≤ 1 := by
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({i,j} : Finset ι)) (fun k _ _ => sq_nonneg (s k))
    simpa [Finset.sum_pair hij, hs] using h
  nlinarith [sq_nonneg (s i-s j)]

theorem schmidtSigned_lower {ι : Type} [Fintype ι] [LinearOrder ι]
    (s : ι → ℝ) (hs : ∀ i, 0 ≤ s i) (hsum : ∑ i, (s i)^2 = 1) (p : ι × ι) :
    0 ≤ 1 + 2 * APPTReview.schmidtSigned s p := by
  unfold APPTReview.schmidtSigned
  split_ifs with h hlt
  · positivity
  · have hp := mul_nonneg (hs p.1) (hs p.2)
    linarith
  · have hprod := schmidt_product_le_half s hsum p.1 p.2 h
    linarith

/-- The dimension-independent actual pure partial-transpose bound. -/
theorem pure_partialTranspose_lower {a b : Type} [Fintype a] [Fintype b]
    [LinearOrder a] [DecidableEq b] (v : a × b → ℂ)
    (hv : (∑ p, star (v p) * v p) = 1) :
    (1 + (2 : ℝ) • APPT.Quantum.partialTranspose (Matrix.vecMulVec v (star v))).PosSemidef := by
  obtain ⟨s,L,hs,hsum,hL,hmodel⟩ := APPTReview.exists_pure_partialTranspose_diagonal v hv
  have hd : (Matrix.diagonal (fun p => ((1 + 2*APPTReview.schmidtSigned s p : ℝ) : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro p
    change (0 : ℂ) ≤ ((1 + 2*APPTReview.schmidtSigned s p : ℝ) : ℂ)
    exact_mod_cast schmidtSigned_lower s hs hsum p
  have he : Matrix.diagonal (fun p => ((1 + 2*APPTReview.schmidtSigned s p : ℝ) : ℂ)) =
      1 + (2 : ℝ) • Matrix.diagonal (fun p => (APPTReview.schmidtSigned s p : ℂ)) := by
    ext p q
    by_cases hpq : p=q <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hpq, Complex.real_smul]
  have heq : 1 + (2 : ℝ) • APPT.Quantum.partialTranspose (Matrix.vecMulVec v (star v)) =
      (1-L*Lᴴ) + L * Matrix.diagonal (fun p => ((1 + 2*APPTReview.schmidtSigned s p : ℝ) : ℂ)) * Lᴴ := by
    rw [hmodel,he]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul]
    module
  rw [heq]
  exact hL.add (hd.mul_mul_conjTranspose_same L)

def spikeState (m n : ℕ) (v : Fin m × Fin n → ℂ) :
    Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ :=
  (1 / ((m:ℝ)*n + 2)) • (1 + (2 : ℝ) • Matrix.vecMulVec v (star v))

theorem pure_trace {ι : Type} [Fintype ι] (v : ι → ℂ)
    (hv : (∑ p, star (v p)*v p)=1) : (Matrix.vecMulVec v (star v)).trace=1 := by
  simpa [Matrix.trace_vecMulVec, dotProduct, mul_comm] using hv

theorem spikeState_density (m n : ℕ) (v : Fin m × Fin n → ℂ)
    (hv : (∑ p, star (v p)*v p)=1) : APPT.Quantum.IsDensity (spikeState m n v) := by
  have hZ : 0 < (m:ℝ)*n+2 := by positivity
  constructor
  · exact (Matrix.PosSemidef.one.add ((Matrix.posSemidef_vecMulVec_self_star v).smul
      (by norm_num : (0:ℝ) ≤ 2))).smul (by positivity : (0:ℝ) ≤ 1/((m:ℝ)*n+2))
  · simp only [spikeState, Matrix.trace_smul, Matrix.trace_add, pure_trace v hv,
      Matrix.trace_one, Fintype.card_prod, Fintype.card_fin, Complex.real_smul]
    push_cast
    field_simp
    <;> ring

theorem spikeState_absolutelyPPT (m n : ℕ) (v : Fin m × Fin n → ℂ)
    (hv : (∑ p, star (v p)*v p)=1) : APPT.Quantum.AbsolutelyPPT (spikeState m n v) := by
  apply APPT.Quantum.absolutelyPPT_smul
  · intro U
    have hU1 : (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)ᴴ * U = 1 := U.property.1
    have hU2 : (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) *
        (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)ᴴ = 1 := U.property.2
    let w := (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) *ᵥ v
    have hwtrace : (Matrix.vecMulVec w (star w)).trace = 1 := by
      dsimp only [w]
      rw [← Extraction.congruence_pure, Matrix.trace_mul_cycle, hU1, Matrix.one_mul]
      exact pure_trace v hv
    have hw : (∑ p, star (w p)*w p)=1 := by
      simpa [Matrix.trace_vecMulVec, dotProduct, mul_comm] using hwtrace
    have he : (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ) * (1 + (2:ℝ) • Matrix.vecMulVec v (star v)) *
        (U : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ)ᴴ = 1 + (2:ℝ) • Matrix.vecMulVec w (star w) := by
      simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul,
        Matrix.smul_mul, hU2, Extraction.congruence_pure, w]
    rw [he, APPT.Quantum.partialTranspose_add, APPT.Quantum.partialTranspose_one,
      APPT.Quantum.partialTranspose_smul]
    exact pure_partialTranspose_lower w hw
  · positivity

/-- Every unit vector gives a genuine physical APPT state, with no supplied
Schmidt coefficients, spectral criterion, or APPT certificate. -/
theorem spikeState_mem_appt (m n : ℕ) (v : Fin m × Fin n → ℂ)
    (hv : (∑ p, star (v p)*v p)=1) : spikeState m n v ∈ APPTReview.physicalAPPTStates m n :=
  ⟨spikeState_density m n v hv,spikeState_absolutelyPPT m n v hv⟩

end
end ExtractionAPPT
