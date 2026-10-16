import SpectralProtocol.ScalarEnvelope
import Spectrum.Finite

open scoped BigOperators ComplexOrder
open Matrix
namespace SpectralProtocol

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The full effect data in the actual ordered density eigenbasis. The diagonal,
its Hilbert--Schmidt budget, both scalar caps, and the trace pairing are proved
from actual matrix inequalities. -/
theorem actual_effect_diagonal_data (X M : Matrix ι ι ℂ) (hX : X.PosSemidef)
    (hM : M.PosSemidef) (hI : (1-M).PosSemidef) (c B : ℝ)
    (hcap : (c • (1:Matrix ι ι ℂ)-M).PosSemidef)
    (hbudget : (M*M).trace.re ≤ B) :
    ∃ z : Fin (Fintype.card ι) → ℝ,
      (M*X).trace.re = ∑ i,hX.isHermitian.eigenvalues₀ i*z i ∧
      (∀ i,0 ≤ z i ∧ z i ≤ 1 ∧ z i ≤ c) ∧ (∑ i,z i^2 ≤ B) := by
  classical
  let V := hX.isHermitian.eigenvectorUnitary
  let Q := (V : Matrix ι ι ℂ)ᴴ*M*V
  let z₀ := fun i : ι => (Q i i).re
  let e : Fin (Fintype.card ι) ≃ ι :=
    Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
  let z := fun i => z₀ (e i)
  have hV : (V : Matrix ι ι ℂ)ᴴ*V=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
  have hQ : Q.PosSemidef := hM.conjTranspose_mul_mul_same _
  have hIQ : (1-Q).PosSemidef := by
    have h := hI.conjTranspose_mul_mul_same (V : Matrix ι ι ℂ)
    simpa only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_one,hV] using h
  have hCQ : (c • (1:Matrix ι ι ℂ)-Q).PosSemidef := by
    have h := hcap.conjTranspose_mul_mul_same (V : Matrix ι ι ℂ)
    simpa only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul,
      Matrix.mul_one,hV] using h
  have hz₀ (i : ι) : 0 ≤ z₀ i ∧ z₀ i ≤ 1 ∧ z₀ i ≤ c := by
    have h0 := (RCLike.nonneg_iff.mp (hQ.diag_nonneg (i := i))).1
    have h1 := (RCLike.nonneg_iff.mp (hIQ.diag_nonneg (i := i))).1
    have hc := (RCLike.nonneg_iff.mp (hCQ.diag_nonneg (i := i))).1
    change 0 ≤ (Q i i).re ∧ (Q i i).re ≤ 1 ∧ (Q i i).re ≤ c
    refine ⟨h0,?_,?_⟩
    · simpa only [Matrix.sub_apply,Matrix.one_apply_eq,Complex.sub_re,Complex.one_re]
        using sub_nonneg.mp h1
    · simpa only [Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq,
        Complex.sub_re,Complex.smul_re,Complex.one_re,smul_eq_mul,mul_one]
        using sub_nonneg.mp hc
  have hb₀ : (∑ i,z₀ i^2) ≤ B := by
    calc
      _ ≤ (Q*Q).trace.re := ExtractionSpectrum.diagonal_square_le_trace_square Q hQ.isHermitian
      _ = (M*M).trace.re := congrArg Complex.re (ExtractionSpectrum.trace_square_unitary_congruence M V)
      _ ≤ B := hbudget
  have hp := hX.isHermitian.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
    RCLike.ofReal_eq_complex_ofReal,Function.comp_def] at hp
  have hpair₀ : (M*X).trace.re=∑ i,hX.isHermitian.eigenvalues i*z₀ i := by
    calc
      _ = (M*((V : Matrix ι ι ℂ)*Matrix.diagonal
          (fun i => (hX.isHermitian.eigenvalues i:ℂ))*(V : Matrix ι ι ℂ)ᴴ)).trace.re :=
        congrArg (fun Y => (M*Y).trace.re) hp
      _ = _ := by
        rw [Extraction.trace_congruence_diagonal]
        simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,
          Complex.ofReal_im,mul_zero,sub_zero]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  refine ⟨z,?_,fun i => hz₀ (e i),?_⟩
  · rw [hpair₀]
    have hs := Equiv.sum_comp e (fun i => hX.isHermitian.eigenvalues i*z₀ i)
    simpa only [Matrix.IsHermitian.eigenvalues,e,z,Equiv.symm_apply_apply] using hs.symm
  · calc
      (∑ i,z i^2) = ∑ i,z₀ i^2 := Equiv.sum_comp e (fun i => z₀ i^2)
      _ ≤ B := hb₀

end SpectralProtocol