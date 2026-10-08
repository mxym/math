import EndpointBridge
import NonDiagonal

open scoped BigOperators ComplexOrder
open Set

namespace BapatBounds

theorem negative_endpoint_survives_diagonalPerturbation {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ i j, ‖A i j‖ ≤ R)
    (h1 : (Bapat.endpointDerivative A).re ≤ -(1 / 2 : ℝ))
    (hΓ : 1 ≤ (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) *
      (R + 1) ^ (n - 1)) :
    let Γ := (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) * (R + 1) ^ (n - 1)
    let ε := 1 / (4 * Γ)
    0 < ε ∧ ε ≤ 1 ∧
      (Bapat.endpointDerivative (diagonalPerturbation A ε)).re ≤ -(1 / 4 : ℝ) := by
  dsimp
  let Γ := (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) * (R + 1) ^ (n - 1)
  have hΓp : 0 < Γ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hΓ
  have hεp : 0 < 1 / (4 * Γ) := by positivity
  have hε1 : 1 / (4 * Γ) ≤ 1 := by
    have hh := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (show (1 : ℝ) ≤ 4 * Γ by linarith)
    simpa using hh
  have heq : Γ * (1 / (4 * Γ)) = (1 / 4 : ℝ) := by field_simp
  have hb := endpointDerivative_perturbation_bound A R (1 / (4 * Γ)) hR hA hεp.le hε1
  have hb' : ‖Bapat.endpointDerivative (diagonalPerturbation A (1 / (4 * Γ))) -
      Bapat.endpointDerivative A‖ ≤ (1 / 4 : ℝ) := by
    calc
      _ ≤ (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) *
          (1 / (4 * Γ)) * (R + 1) ^ (n - 1) := hb
      _ = Γ * (1 / (4 * Γ)) := by dsimp [Γ]; ring
      _ = _ := heq
  have hr := (Complex.re_le_norm
    (Bapat.endpointDerivative (diagonalPerturbation A (1 / (4 * Γ))) -
      Bapat.endpointDerivative A)).trans hb'
  simp only [Complex.sub_re] at hr
  exact ⟨hεp, hε1, by linarith⟩

/-- This closes the actual positive-definite perturbation and explicit-interval
chain. The negative endpoint hypothesis must separately come from the actual
Gram/Bargmann bridge and the integer certificate; this is not that certificate. -/
theorem gram_explicit_monotonicity_failure {n r : ℕ}
    (V : Matrix (Fin n) (Fin r) ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hA : ∀ i j, ‖(V * V.conjTranspose) i j‖ ≤ R)
    (h1 : (Bapat.endpointDerivative (V * V.conjTranspose)).re ≤ -(1 / 2 : ℝ))
    (hΓ : 1 ≤ (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) *
      (R + 1) ^ (n - 1))
    (hK : 1 ≤ (n.choose 2 : ℝ) * ((n.choose 2 - 1 : ℕ) : ℝ) *
      (n.factorial : ℝ) * (R + 1) ^ n) :
    let Γ := (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) * (R + 1) ^ (n - 1)
    let ε := 1 / (4 * Γ)
    let B := diagonalPerturbation (V * V.conjTranspose) ε
    let K := (n.choose 2 : ℝ) * ((n.choose 2 - 1 : ℕ) : ℝ) *
      (n.factorial : ℝ) * (R + 1) ^ n
    let h := 1 / (8 * K)
    let q₀ := 1 - h
    B.PosDef ∧ (∃ i j, i ≠ j ∧ B i j ≠ 0) ∧ 0 < q₀ ∧ q₀ < 1 ∧
      h / 8 ≤ (Bapat.qPermanent B (q₀ : ℂ)).re - (Bapat.qPermanent B 1).re ∧
      (Bapat.qPermanent B 1).re < (Bapat.qPermanent B (q₀ : ℂ)).re := by
  dsimp
  let A := V * V.conjTranspose
  let Γ := (n.choose 2 : ℝ) * (n.factorial : ℝ) * (n : ℝ) * (R + 1) ^ (n - 1)
  let ε := 1 / (4 * Γ)
  obtain ⟨hεp, hε1, hb1⟩ := negative_endpoint_survives_diagonalPerturbation A R hR hA h1 hΓ
  have hB := gram_diagonalPerturbation_posDef V ε hεp
  have hentries := diagonalPerturbation_entries A R ε hA hεp.le hε1
  exact ⟨hB, negative_endpoint_nondiagonal _ (by linarith [hb1]),
    qPermanent_explicit_reverse_interval (diagonalPerturbation A ε) (R + 1)
      (by linarith) hentries hb1 hK⟩

end BapatBounds
