import BapatDefs
import ProofBundle
import BapatN200Matrix
import BapatN200Trace
import BapatExactStateBridge

-- Source: DefinitionBridge.lean

set_option autoImplicit false
open scoped BigOperators ComplexOrder

namespace BapatExplicit

theorem inversionCount_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Bapat.inversionCount σ = BapatRankTwo.inversions σ := by
  unfold Bapat.inversionCount BapatRankTwo.inversions
  simp only [Finset.card_filter, Fintype.sum_prod_type]

theorem qPermanent_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (q : ℂ) :
    Bapat.qPermanent A q = BapatRankTwo.qPermanent A q := by
  unfold Bapat.qPermanent BapatRankTwo.qPermanent Bapat.permutationWeight
  simp_rw [inversionCount_eq]
  apply Finset.sum_congr (by ext σ; simp)
  intro σ _
  rfl

theorem endpointDerivative_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (Bapat.endpointDerivative A).re =
      (BapatRankTwo.realQPolynomial A).derivative.eval 1 := by
  rw [BapatRankTwo.realQPolynomial_derivative_one]
  unfold Bapat.endpointDerivative BapatRankTwo.MarkedInversions.weightedInversionSum
    Bapat.permutationWeight BapatRankTwo.MarkedInversions.permutationWeight
  congr 1
  apply Finset.sum_congr (by ext σ; simp)
  intro σ _
  rw [inversionCount_eq]
  rfl

noncomputable def twoColumnGram {n : ℕ} (a b : Fin n → ℂ) :
    Matrix (Fin n) (Fin 2) ℂ := fun i j => if j = 0 then a i else b i

theorem twoColumnGram_mul {n : ℕ} (a b : Fin n → ℂ) :
    twoColumnGram a b * (twoColumnGram a b).conjTranspose = BapatRankTwo.gram a b := by
  ext i j
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    twoColumnGram, BapatRankTwo.gram]

theorem perturb_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (ε : ℝ) :
    BapatBounds.diagonalPerturbation A ε = BapatRankTwo.perturb A ε := rfl

end BapatExplicit

-- Source: ConstantParameters.lean

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BapatExplicit

def gamma : ℕ := 19900 * Nat.factorial 200 * 200 * 1601 ^ 199
def secondBound : ℕ := 19900 * 19899 * Nat.factorial 200 * 1601 ^ 200
def epsilon : ℚ := 1 / (4 * (gamma : ℚ))
def intervalLength : ℚ := 1 / (8 * (secondBound : ℚ))
def q0 : ℚ := 1 - intervalLength

theorem cast_triple_pow (a b c d e : ℕ) :
    ((a * b * c * d ^ e : ℕ) : ℝ) =
      (a : ℝ) * (b : ℝ) * (c : ℝ) * (d : ℝ) ^ e := by
  simp only [Nat.cast_mul, Nat.cast_pow]

theorem gamma_cast : (gamma : ℝ) =
    (Nat.choose 200 2 : ℝ) * (Nat.factorial 200 : ℝ) * ((200 : ℕ) : ℝ) *
      ((1600 : ℝ) + 1) ^ (200 - 1 : ℕ) := by
  have hn : Nat.choose 200 2 = 19900 := by norm_num [Nat.choose_two_right]
  calc
    _ = (19900 : ℝ) * (Nat.factorial 200 : ℝ) * 200 * (1601 : ℝ) ^ (199 : ℕ) :=
      cast_triple_pow 19900 (Nat.factorial 200) 200 1601 199
    _ = _ := by rw [hn, show (1600 : ℝ) + 1 = 1601 by norm_num]; rfl

theorem secondBound_cast : (secondBound : ℝ) =
    (Nat.choose 200 2 : ℝ) * ((Nat.choose 200 2 - 1 : ℕ) : ℝ) *
      (Nat.factorial 200 : ℝ) * ((1600 : ℝ) + 1) ^ (200 : ℕ) := by
  have hn : Nat.choose 200 2 = 19900 := by norm_num [Nat.choose_two_right]
  calc
    _ = (19900 : ℝ) * 19899 * (Nat.factorial 200 : ℝ) * (1601 : ℝ) ^ (200 : ℕ) :=
      cast_triple_pow 19900 19899 (Nat.factorial 200) 1601 200
    _ = _ := by rw [hn, show (1600 : ℝ) + 1 = 1601 by norm_num]; rfl

theorem epsilon_cast : (epsilon : ℝ) = 1 / (4 * (gamma : ℝ)) := by
  simp only [epsilon, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]

theorem intervalLength_cast : (intervalLength : ℝ) = 1 / (8 * (secondBound : ℝ)) := by
  simp only [intervalLength, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]

theorem q0_cast : (q0 : ℝ) = 1 - 1 / (8 * (secondBound : ℝ)) := by
  simp only [q0, Rat.cast_sub, Rat.cast_one, intervalLength_cast]

theorem q0_complex_cast : ((q0 : ℝ) : ℂ) = (q0 : ℂ) := by norm_cast

theorem epsilon_positive : (0 : ℚ) < epsilon := by
  have hf : 0 < Nat.factorial 200 := Nat.factorial_pos 200
  have hg : 0 < gamma := by unfold gamma; positivity
  unfold epsilon
  positivity

theorem intervalLength_positive : (0 : ℚ) < intervalLength := by
  have hf : 0 < Nat.factorial 200 := Nat.factorial_pos 200
  have hk : 0 < secondBound := by unfold secondBound; positivity
  unfold intervalLength
  positivity

end BapatExplicit

-- Source: N200EntryBounds.lean

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open scoped BigOperators ComplexOrder

namespace BapatExplicit
open BapatRankTwo BapatRankTwo.Exact BapatRankTwo.N200

theorem toComplex_norm_sq (z : GI) :
    ‖toComplex z‖ ^ 2 = ((z.re * z.re + z.im * z.im : ℤ) : ℝ) := by
  simp [Complex.sq_norm, Complex.normSq_apply, toComplex, Zsqrtd.lift_apply_apply]

/-- A finite kernel-checked bound on the actual ordered published data. -/
theorem integer_coordinate_norm_bounds : ∀ i : Fin 200,
    let z := vectorAt vectors i.val
    z.1.re * z.1.re + z.1.im * z.1.im ≤ (800 : ℤ) ∧
    z.2.re * z.2.re + z.2.im * z.2.im ≤ (800 : ℤ) := by
  decide +kernel

theorem vector_norm_sq_bounds (i : Fin 200) : ‖a i‖ ^ 2 ≤ (800 : ℝ) ∧
    ‖b i‖ ^ 2 ≤ (800 : ℝ) := by
  have hi := integer_coordinate_norm_bounds i
  constructor
  · rw [a, toComplex_norm_sq]
    exact_mod_cast hi.1
  · rw [b, toComplex_norm_sq]
    exact_mod_cast hi.2

theorem matrix_entry_norm_bound (i j : Fin 200) : ‖matrix i j‖ ≤ (1600 : ℝ) := by
  have hi := vector_norm_sq_bounds i
  have hj := vector_norm_sq_bounds j
  have ha : ‖a i‖ * ‖a j‖ ≤ (800 : ℝ) := by
    nlinarith [sq_nonneg (‖a i‖ - ‖a j‖)]
  have hb : ‖b i‖ * ‖b j‖ ≤ (800 : ℝ) := by
    nlinarith [sq_nonneg (‖b i‖ - ‖b j‖)]
  calc
    ‖matrix i j‖ ≤ ‖a i * star (a j)‖ + ‖b i * star (b j)‖ := norm_add_le _ _
    _ = ‖a i‖ * ‖a j‖ + ‖b i‖ * ‖b j‖ := by simp
    _ ≤ 1600 := by linarith

end BapatExplicit

-- Source: N200RationalEntries.lean

set_option autoImplicit false
open scoped ComplexOrder

namespace BapatExplicit
open BapatRankTwo BapatRankTwo.Exact BapatRankTwo.N200

noncomputable def explicitMatrix : Matrix (Fin 200) (Fin 200) ℂ :=
  perturb matrix (epsilon : ℝ)

theorem toComplex_re (z : GI) : (toComplex z).re = (z.re : ℝ) := by
  simp [toComplex, Zsqrtd.lift_apply_apply]

theorem toComplex_im (z : GI) : (toComplex z).im = (z.im : ℝ) := by
  simp [toComplex, Zsqrtd.lift_apply_apply]

noncomputable def rationalReal (i j : Fin 200) : ℚ :=
  let x := vectorAt vectors i.val
  let y := vectorAt vectors j.val
  (x.1.re : ℚ) * (y.1.re : ℚ) + (x.1.im : ℚ) * (y.1.im : ℚ) +
    (x.2.re : ℚ) * (y.2.re : ℚ) + (x.2.im : ℚ) * (y.2.im : ℚ)

noncomputable def rationalImag (i j : Fin 200) : ℚ :=
  let x := vectorAt vectors i.val
  let y := vectorAt vectors j.val
  (x.1.im : ℚ) * (y.1.re : ℚ) - (x.1.re : ℚ) * (y.1.im : ℚ) +
    ((x.2.im : ℚ) * (y.2.re : ℚ) - (x.2.re : ℚ) * (y.2.im : ℚ))

theorem matrix_rational_entries (i j : Fin 200) :
    matrix i j = (rationalReal i j : ℂ) + (rationalImag i j : ℂ) * Complex.I := by
  apply Complex.ext <;>
    simp [matrix, gram, a, b, rationalReal, rationalImag, toComplex_re, toComplex_im,
      Complex.mul_re, Complex.mul_im] <;> ring

/-- Every entry of the specified positive-definite matrix has rational real
and imaginary parts, using the very same CSV and rational epsilon. -/
theorem explicitMatrix_rational_entries (i j : Fin 200) :
    explicitMatrix i j =
      ((rationalReal i j + if i = j then epsilon else 0 : ℚ) : ℂ) +
        (rationalImag i j : ℂ) * Complex.I := by
  change matrix i j + (Matrix.diagonal (fun _ => ((epsilon : ℝ) : ℂ))) i j = _
  rw [matrix_rational_entries]
  by_cases hij : i = j
  · subst j
    simp [Matrix.diagonal_apply]
    ring
  · simp [Matrix.diagonal_apply, hij]

end BapatExplicit

-- Source: N200EndpointGap.lean

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open scoped BigOperators ComplexOrder

namespace BapatExplicit
open BapatRankTwo BapatRankTwo.Exact BapatRankTwo.N200

/-- Integrality strengthens the certified strict gap to a unit gap. -/
theorem integer_norm_gap_at_least_one :
    (1 : ℤ) ≤ wedgeNorm - 19900 * permanentNorm := by
  have h := norm_gap_positive
  omega

theorem permanentNorm_eq_fischer : (permanentNorm : ℝ) =
    BapatFischer.fischerNormSq 200 (BapatFischer.twoColorProduct a b) := by
  unfold permanentNorm
  rw [← state_eq_200]
  exact fischerInt_state_f (vectorAt vectors) 200

theorem wedgeNorm_eq_fischer : (wedgeNorm : ℝ) =
    BapatFischer.fischerNormSq 198 (wedgePolynomial a b) := by
  unfold wedgeNorm
  rw [← state_eq_200]
  exact fischerInt_state_s (vectorAt vectors) 200

/-- No negative-input premise: the actual matrix is the certified 200-row Gram. -/
theorem matrix_endpoint_unit_gap : (Bapat.endpointDerivative matrix).re ≤ -(1 / 2 : ℝ) := by
  have hgap : (1 : ℝ) ≤ (wedgeNorm : ℝ) - 19900 * (permanentNorm : ℝ) := by
    exact_mod_cast integer_norm_gap_at_least_one
  have hid := realQPolynomial_derivative_fischer a b
  change 2 * (realQPolynomial matrix).derivative.eval 1 = _ at hid
  have hn : (Nat.choose 200 2 : ℝ) = 19900 := by norm_num [Nat.choose_two_right]
  rw [hn, ← permanentNorm_eq_fischer, ← wedgeNorm_eq_fischer] at hid
  rw [endpointDerivative_eq]
  linarith

end BapatExplicit

-- Source: N200Explicit.lean

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open scoped BigOperators ComplexOrder
open Set

namespace BapatExplicit
open BapatRankTwo BapatRankTwo.N200

/-- The paper's specified rational shift and rational q0, with no negative
endpoint hypothesis or unverified numerical input. -/
theorem explicit_rational_counterexample :
    explicitMatrix.PosDef ∧
      (∃ i j, i ≠ j ∧ explicitMatrix i j ≠ 0) ∧
      (0 : ℝ) < (q0 : ℝ) ∧ (q0 : ℝ) < 1 ∧
      (intervalLength : ℝ) / 8 ≤
        (qPermanent explicitMatrix (q0 : ℂ)).re - (qPermanent explicitMatrix 1).re ∧
      (qPermanent explicitMatrix 1).re < (qPermanent explicitMatrix (q0 : ℂ)).re := by
  let V := twoColumnGram a b
  have hV : V * V.conjTranspose = N200.matrix := twoColumnGram_mul a b
  have hA : ∀ i j, ‖(V * V.conjTranspose) i j‖ ≤ (1600 : ℝ) := by
    rw [hV]
    exact matrix_entry_norm_bound
  have hd := BapatBounds.dimension_at_least_three_bounds 200 (by norm_num)
    (1600 : ℝ) (by norm_num)
  have hneg : (Bapat.endpointDerivative (V * V.conjTranspose)).re ≤ -(1 / 2 : ℝ) := by
    rw [hV]
    exact matrix_endpoint_unit_gap
  have h := BapatBounds.gram_explicit_monotonicity_failure V (1600 : ℝ)
    (by norm_num) hA hneg hd.1 hd.2
  dsimp only at h
  rw [hV, ← gamma_cast, ← secondBound_cast, ← epsilon_cast,
    perturb_eq, ← q0_cast, ← intervalLength_cast] at h
  simpa only [explicitMatrix, qPermanent_eq, Complex.ofReal_one, q0_complex_cast] using h

theorem explicit_not_monotone :
    ¬MonotoneOn (fun q : ℝ => (qPermanent explicitMatrix (q : ℂ)).re) (Icc (-1) 1) := by
  obtain ⟨_, _, h0, h1, _, hreverse⟩ := explicit_rational_counterexample
  intro hm
  have hle := hm (show (q0 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> linarith)
    (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) h1.le
  have hle' : (qPermanent explicitMatrix (q0 : ℂ)).re ≤
      (qPermanent explicitMatrix 1).re := by
    simpa only [q0_complex_cast, Complex.ofReal_one] using hle
  exact (not_le_of_gt hreverse) hle'

/-- The explicit rational witness refutes the original strict conjecture. -/
theorem original_conjecture_false_from_explicit : ¬ OriginalBapatConjecture := by
  intro h
  have hp := explicit_rational_counterexample.1
  have hn : ¬ explicitMatrix.IsDiag := perturb_matrix_not_isDiag (epsilon : ℝ)
  exact explicit_not_monotone (h 200 explicitMatrix hp hn).monotoneOn

theorem explicit_qPermanent_real (q : ℝ) :
    qPermanent explicitMatrix (q : ℂ) =
      (((realQPolynomial explicitMatrix).eval q : ℝ) : ℂ) :=
  qPermanent_eq_ofReal_eval explicit_rational_counterexample.1.isHermitian q

end BapatExplicit
