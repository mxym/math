import SpectralProtocol.ProjectionState
import Mathlib.Data.Nat.Log

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

/-- Number of extractable integer Bell pairs from a support of rank r in
balanced 2^k by 2^k input dimensions. This is an integer formula, not a rounded
real exponent or an assumed gate-count estimate. -/
def integerBellYield (k r : ℕ) : ℕ := k - Nat.clog 4 r

/-- The integer yield is the exact greatest h obeying the rank budget. -/
theorem integerBellYield_iff (k r h : ℕ) (hr : 0 < r) (hrdim : r ≤ 4^k) :
    h ≤ integerBellYield k r ↔ r * 4^h ≤ 4^k := by
  have ht : Nat.clog 4 r ≤ k := Nat.clog_le_of_le_pow hrdim
  constructor
  · intro hhy
    have hhk : h ≤ k := by simp only [integerBellYield] at hhy; omega
    have hclog : Nat.clog 4 r ≤ k-h := by simp only [integerBellYield] at hhy; omega
    have hr' : r ≤ 4^(k-h) := (Nat.clog_le_iff_le_pow (by decide)).mp hclog
    have hpow : 4^(k-h) * 4^h = 4^k := by rw [← pow_add, Nat.sub_add_cancel hhk]
    exact (Nat.mul_le_mul_right (4^h) hr').trans_eq hpow
  · intro hbudget
    have hpow : 4^h ≤ 4^k := by
      calc
        4^h = 1 * 4^h := by omega
        _ ≤ r * 4^h := Nat.mul_le_mul_right _ hr
        _ ≤ 4^k := hbudget
    have hhk : h ≤ k := (Nat.pow_le_pow_iff_right (by decide)).mp hpow
    have hr' : r ≤ 4^(k-h) := by
      rw [← Nat.pow_div hhk (by decide)]
      exact (Nat.le_div_iff_mul_le (by positivity)).mpr hbudget
    have hclog : Nat.clog 4 r ≤ k-h := Nat.clog_le_of_le_pow hr'
    simp only [integerBellYield]
    omega

/-- Integer divisions used by the actual local Kraus construction. -/
theorem integerBellYield_packing (k r : ℕ) (hrdim : r ≤ 4^k) :
    r ≤ (2^k / 2^(integerBellYield k r)) * (2^k / 2^(integerBellYield k r)) := by
  have ht : Nat.clog 4 r ≤ k := Nat.clog_le_of_le_pow hrdim
  have hh : integerBellYield k r ≤ k := Nat.sub_le _ _
  have he : k - integerBellYield k r = Nat.clog 4 r := by
    simp only [integerBellYield]
    omega
  rw [Nat.pow_div hh (by decide), he, ← mul_pow]
  norm_num only [Nat.reduceMul]
  exact Nat.le_pow_clog (by decide) r

/-- A single original-space unitary and two complete local channels extract
exactly the maximal integer number of Bell pairs on every density supported
by the given actual projection. -/
theorem integerBellYield_actual_extractor (k : ℕ)
    (P : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (hrdim : P.rank ≤ 4^k) :
    let h := integerBellYield k P.rank
    ∃ (U : Matrix.unitaryGroup (Fin (2^k) × Fin (2^k)) ℂ)
      (A : Fin (2^k / 2^h) ⊕ Fin (2^k) → Matrix (Fin (2^h)) (Fin (2^k)) ℂ)
      (B : Fin (2^k / 2^h) ⊕ Fin (2^k) → Matrix (Fin (2^h)) (Fin (2^k)) ℂ),
      (∑ j, (A j)ᴴ * A j = 1) ∧ (∑ j, (B j)ᴴ * B j = 1) ∧
      Extraction.PTConjugatePositive (Extraction.productKraus A B) ∧
      ∀ X : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ,
        APPT.Quantum.IsDensity X → P * X * P = X →
        (Extraction.bellProjector (d := Fin (2^h)) *
          Extraction.krausApply (Extraction.productKraus A B)
            ((U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ) * X *
              (U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)ᴴ)).trace.re = 1 := by
  dsimp only
  let h := integerBellYield k P.rank
  obtain ⟨U,A,B,hA,hB,he⟩ := Extraction.finite_projection_fidelity_extractor
    (2^k) (2^k) (2^h) (2^h) (by positivity) le_rfl P hP hPP
    (integerBellYield_packing k P.rank hrdim)
  refine ⟨U,A,B,hA,hB,productKraus_PTConjugatePositive A B,?_⟩
  intro X hX hPX
  simpa only [Nat.cast_pow, Nat.cast_ofNat,
    div_self (by positivity : (2:ℝ)^h ≠ 0)] using he X hX hPX

/-- No physical common extractor can output more Bell pairs than that yield.
The converse is uniform over every initial unitary and every finite Kraus
channel with the required physical transpose-conjugate positivity. -/
theorem integerBellYield_optimal (k h : ℕ)
    (P : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)
    (hP : P.IsHermitian) (hPP : P * P = P) (hr : 0 < P.rank)
    (hrdim : P.rank ≤ 4^k) {κ : Type*} [Fintype κ]
    (A : κ → Matrix (Fin (2^h) × Fin (2^h)) (Fin (2^k) × Fin (2^k)) ℂ)
    (hcomplete : ∑ j, (A j)ᴴ * A j = 1)
    (hpt : Extraction.PTConjugatePositive A)
    (U : Matrix.unitaryGroup (Fin (2^k) × Fin (2^k)) ℂ)
    (hexact : ∀ X : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ,
      APPT.Quantum.IsDensity X → P * X * P = X →
      (Extraction.bellProjector (d := Fin (2^h)) * Extraction.krausApply A
        ((U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ) * X *
          (U : Matrix (Fin (2^k) × Fin (2^k)) (Fin (2^k) × Fin (2^k)) ℂ)ᴴ)).trace.re = 1) :
    h ≤ integerBellYield k P.rank := by
  letI : Nonempty (Fin (2^h)) := ⟨⟨0,by positivity⟩⟩
  have hb := exact_common_support_dimension_budget P hP hPP hr A hcomplete hpt U hexact
  simp only [Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat] at hb
  have hsq (j : ℕ) : ((2:ℝ)^j)^2 = (4:ℝ)^j := by
    rw [pow_two, ← mul_pow]
    norm_num
  rw [hsq, ← pow_two, hsq] at hb
  have hbn : P.rank * 4^h ≤ 4^k := by exact_mod_cast hb
  exact (integerBellYield_iff k P.rank h hr hrdim).mpr hbn

end SpectralProtocol