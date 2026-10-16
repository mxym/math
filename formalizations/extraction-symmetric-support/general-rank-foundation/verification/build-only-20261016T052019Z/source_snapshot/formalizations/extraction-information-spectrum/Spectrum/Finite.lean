import Extraction.OverlapConverse
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators ComplexOrder
open Matrix
namespace ExtractionSpectrum

variable {ι : Type*} [Fintype ι]

/-- The mass of eigenvalues above a numerical cutoff. Zero eigenvalues need no
special convention in this finite form. -/
noncomputable def spectralMass (p : ι → ℝ) (c : ℝ) : ℝ :=
  ∑ i, if c ≤ p i then p i else 0

/-- Distribution function of self-information, on the positive support. -/
noncomputable def informationMass (p : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, if 0 < p i ∧ -Real.log (p i) ≤ x then p i else 0

theorem informationMass_eq_spectralMass (p : ι → ℝ) (x : ℝ) :
    informationMass p x = spectralMass p (Real.exp (-x)) := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  apply propext
  constructor
  · rintro ⟨hp, hx⟩
    exact (Real.exp_le_exp.mpr (by linarith : -x ≤ Real.log (p i))).trans_eq
      (Real.exp_log hp)
  · intro h
    have hp : 0 < p i := (Real.exp_pos _).trans_le h
    refine ⟨hp, ?_⟩
    have h' : -x ≤ Real.log (p i) := (Real.le_log_iff_exp_le hp).mpr h
    linarith

/-- A finite information-spectrum estimate, derived from the actual quadratic
budget rather than a supplied tail estimate. -/
theorem finite_spectrum_bound (p z : ι → ℝ) (r c : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (hz : ∀ i, 0 ≤ z i ∧ z i ≤ 1)
    (hbudget : ∑ i, z i ^ 2 ≤ r) (hc : 0 ≤ c) :
    ∑ i, p i * z i ≤ spectralMass p c + Real.sqrt (c * r) := by
  classical
  let s := Finset.univ.filter fun i => p i < c
  have hr : 0 ≤ r :=
    (Finset.sum_nonneg fun i _ => sq_nonneg (z i)).trans hbudget
  have hp2 : ∑ i ∈ s, p i ^ 2 ≤ c := by
    calc
      ∑ i ∈ s, p i ^ 2 ≤ ∑ i ∈ s, c * p i := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : p i < c := (Finset.mem_filter.mp hi).2
        nlinarith [hp i]
      _ = c * ∑ i ∈ s, p i := by rw [Finset.mul_sum]
      _ ≤ c * 1 := by
        apply mul_le_mul_of_nonneg_left _ hc
        rw [← hs]
        exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => hp i)
      _ = c := mul_one _
  have hz2 : ∑ i ∈ s, z i ^ 2 ≤ r :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => sq_nonneg (z i))).trans hbudget
  have hcs : (∑ i ∈ s, p i * z i) ^ 2 ≤ c * r := by
    exact (Finset.sum_mul_sq_le_sq_mul_sq s p z).trans
      (mul_le_mul hp2 hz2 (Finset.sum_nonneg fun i _ => sq_nonneg (z i)) hc)
  have hsmall : ∑ i ∈ s, p i * z i ≤ Real.sqrt (c * r) :=
    Real.le_sqrt_of_sq_le hcs
  have hpoint (i : ι) : p i * z i ≤
      (if c ≤ p i then p i else 0) + (if p i < c then p i * z i else 0) := by
    by_cases h : c ≤ p i
    · simp only [h, ite_true, not_lt_of_ge h, ite_false, add_zero]
      nlinarith [(hz i).2, hp i]
    · simp only [h, ite_false, lt_of_not_ge h, ite_true, zero_add]
      exact le_rfl
  calc
    ∑ i, p i * z i ≤ ∑ i,
        ((if c ≤ p i then p i else 0) + (if p i < c then p i * z i else 0)) :=
      Finset.sum_le_sum fun i _ => hpoint i
    _ = spectralMass p c + ∑ i ∈ s, p i * z i := by
      simp [spectralMass, s, Finset.sum_add_distrib, Finset.sum_filter]
    _ ≤ _ := add_le_add_right hsmall _

variable [DecidableEq ι]

/-- The diagonal part of the Hilbert--Schmidt norm is bounded by the full
trace square. All off-diagonal terms are retained as nonnegative norms. -/
theorem diagonal_square_le_trace_square (M : Matrix ι ι ℂ)
    (hM : M.IsHermitian) :
    ∑ i, (M i i).re ^ 2 ≤ (M * M).trace.re := by
  classical
  have he : (M * M).trace.re = ∑ i, ∑ j, Complex.normSq (M i j) := by
    calc
      _ = (M * Mᴴ).trace.re := by rw [hM.eq]
      _ = _ := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
          Complex.star_def, Complex.mul_conj, Complex.re_sum, Complex.ofReal_re]
  rw [he]
  apply Finset.sum_le_sum
  intro i _
  calc
    (M i i).re ^ 2 ≤ Complex.normSq (M i i) := by
      rw [Complex.normSq_apply]
      nlinarith [sq_nonneg (M i i).im]
    _ ≤ ∑ j, Complex.normSq (M i j) :=
      Finset.single_le_sum (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

/-- Unitary basis changes preserve the complete Hilbert--Schmidt budget. -/
theorem trace_square_unitary_congruence (M : Matrix ι ι ℂ)
    (V : Matrix.unitaryGroup ι ℂ) :
    ((V : Matrix ι ι ℂ)ᴴ * M * V *
      ((V : Matrix ι ι ℂ)ᴴ * M * V)).trace = (M * M).trace := by
  have hV : (V : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ)ᴴ = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self V
  calc
    _ = ((V : Matrix ι ι ℂ)ᴴ * (M * M) * V).trace := by
      congr 1
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (V : Matrix ι ι ℂ), hV, Matrix.one_mul]
    _ = _ := by rw [Matrix.trace_mul_cycle, hV, Matrix.one_mul]

/-- The actual Hermitian eigenspectrum of a density sums to one. -/
theorem density_eigenvalues_sum (X : Matrix ι ι ℂ)
    (hX : X.PosSemidef ∧ X.trace = 1) :
    ∑ i, hX.1.isHermitian.eigenvalues i = 1 := by
  have ht := hX.1.isHermitian.trace_eq_sum_eigenvalues
  have hr := congrArg Complex.re ht
  simpa only [hX.2, Complex.one_re, Complex.re_sum,
    RCLike.ofReal_eq_complex_ofReal, Complex.ofReal_re] using hr.symm

/-- Finite spectrum upper bound for an actual density and an actual PSD effect.
The eigenspace, diagonal entries, and diagonal norm budget are constructed in
the proof. -/
theorem density_effect_spectrum_bound (X M : Matrix ι ι ℂ)
    (hX : X.PosSemidef ∧ X.trace = 1)
    (hM : M.PosSemidef) (hI : (1 - M).PosSemidef)
    (r c : ℝ) (hbudget : (M * M).trace.re ≤ r) (hc : 0 ≤ c) :
    (M * X).trace.re ≤ spectralMass hX.1.isHermitian.eigenvalues c +
      Real.sqrt (c * r) := by
  classical
  let V := hX.1.isHermitian.eigenvectorUnitary
  let Q := (V : Matrix ι ι ℂ)ᴴ * M * V
  let z : ι → ℝ := fun i => (Q i i).re
  have hQ : Q.PosSemidef := hM.conjTranspose_mul_mul_same _
  have hV : (V : Matrix ι ι ℂ)ᴴ * V = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
  have hIQ : (1 - Q).PosSemidef := by
    have h := hI.conjTranspose_mul_mul_same (V : Matrix ι ι ℂ)
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV] using h
  have hz (i : ι) : 0 ≤ z i ∧ z i ≤ 1 := by
    have h0 := (RCLike.nonneg_iff.mp (hQ.diag_nonneg (i := i))).1
    have h1 := (RCLike.nonneg_iff.mp (hIQ.diag_nonneg (i := i))).1
    change 0 ≤ (Q i i).re ∧ (Q i i).re ≤ 1
    constructor
    · exact h0
    · simpa only [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re,
        Complex.one_re] using (sub_nonneg.mp h1)
  have hzb : ∑ i, z i ^ 2 ≤ r := by
    calc
      ∑ i, z i ^ 2 ≤ (Q * Q).trace.re := diagonal_square_le_trace_square Q hQ.isHermitian
      _ = (M * M).trace.re := congrArg Complex.re (trace_square_unitary_congruence M V)
      _ ≤ r := hbudget
  have hp := hX.1.isHermitian.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    RCLike.ofReal_eq_complex_ofReal, Function.comp_def] at hp
  have hpair : (M * X).trace.re = ∑ i, hX.1.isHermitian.eigenvalues i * z i := by
    calc
      _ = (M * ((V : Matrix ι ι ℂ) *
          Matrix.diagonal (fun i => (hX.1.isHermitian.eigenvalues i : ℂ)) *
          (V : Matrix ι ι ℂ)ᴴ)).trace.re := congrArg (fun B => (M * B).trace.re) hp
      _ = _ := by
        rw [Extraction.trace_congruence_diagonal]
        simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
          Complex.ofReal_im, mul_zero, sub_zero]
        exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hpair]
  exact finite_spectrum_bound _ z r c (fun i => hX.1.eigenvalues_nonneg i)
    (density_eigenvalues_sum X hX) hz hzb hc

/-- Exact evaluation of the square-root tail term. -/
theorem cutoff_sqrt_eq (r t : ℝ) (hr : 0 < r) :
    Real.sqrt (Real.exp (-(Real.log r + t)) * r) = Real.exp (-t / 2) := by
  have he : Real.exp (-(Real.log r + t)) * r = Real.exp (-t) := by
    rw [neg_add, Real.exp_add, Real.exp_neg, Real.exp_log hr]
    field_simp
  have he2 : Real.exp (-t) = Real.exp (-t / 2) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [he, he2, Real.sqrt_sq_eq_abs, abs_of_pos (Real.exp_pos _)]

/-- The same spectrum estimate for an explicitly constructed eigenbasis.
This interface permits canonical tensor powers without assuming any theorem
about the sorted tensor eigenvalues. -/
theorem diagonalized_effect_spectrum_bound (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (V : Matrix.unitaryGroup ι ℂ) (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (hI : (1 - M).PosSemidef)
    (r c : ℝ) (hbudget : (M * M).trace.re ≤ r) (hc : 0 ≤ c) :
    (M * ((V : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (p i : ℂ)) *
      (V : Matrix ι ι ℂ)ᴴ)).trace.re ≤ spectralMass p c + Real.sqrt (c * r) := by
  classical
  let Q := (V : Matrix ι ι ℂ)ᴴ * M * V
  let z : ι → ℝ := fun i => (Q i i).re
  have hQ : Q.PosSemidef := hM.conjTranspose_mul_mul_same _
  have hV : (V : Matrix ι ι ℂ)ᴴ * V = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
  have hIQ : (1 - Q).PosSemidef := by
    have h := hI.conjTranspose_mul_mul_same (V : Matrix ι ι ℂ)
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV] using h
  have hz (i : ι) : 0 ≤ z i ∧ z i ≤ 1 := by
    have h0 := (RCLike.nonneg_iff.mp (hQ.diag_nonneg (i := i))).1
    have h1 := (RCLike.nonneg_iff.mp (hIQ.diag_nonneg (i := i))).1
    change 0 ≤ (Q i i).re ∧ (Q i i).re ≤ 1
    constructor
    · exact h0
    · simpa only [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re,
        Complex.one_re] using (sub_nonneg.mp h1)
  have hzb : ∑ i, z i ^ 2 ≤ r := by
    calc
      ∑ i, z i ^ 2 ≤ (Q * Q).trace.re := diagonal_square_le_trace_square Q hQ.isHermitian
      _ = (M * M).trace.re := congrArg Complex.re (trace_square_unitary_congruence M V)
      _ ≤ r := hbudget
  rw [Extraction.trace_congruence_diagonal]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  have he : (∑ i, (((V : Matrix ι ι ℂ)ᴴ * M * V) i i).re * p i) =
      ∑ i, p i * z i := Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [he]
  exact finite_spectrum_bound p z r c hp hs hz hzb hc

theorem diagonalized_effect_information_bound (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1)
    (V : Matrix.unitaryGroup ι ℂ) (M : Matrix ι ι ℂ)
    (hM : M.PosSemidef) (hI : (1 - M).PosSemidef)
    (r t : ℝ) (hr : 0 < r) (hbudget : (M * M).trace.re ≤ r) :
    (M * ((V : Matrix ι ι ℂ) * Matrix.diagonal (fun i => (p i : ℂ)) *
      (V : Matrix ι ι ℂ)ᴴ)).trace.re ≤
        informationMass p (Real.log r + t) + Real.exp (-t / 2) := by
  rw [informationMass_eq_spectralMass, ← cutoff_sqrt_eq r t hr]
  exact diagonalized_effect_spectrum_bound p hp hs V M hM hI r _ hbudget
    (Real.exp_pos _).le

/-- The finite information-spectrum converse for an actual density and an
effect with a derived Hilbert--Schmidt budget. No positivity of `t` is needed. -/
theorem density_effect_information_bound (X M : Matrix ι ι ℂ)
    (hX : X.PosSemidef ∧ X.trace = 1)
    (hM : M.PosSemidef) (hI : (1 - M).PosSemidef)
    (r t : ℝ) (hr : 0 < r) (hbudget : (M * M).trace.re ≤ r) :
    (M * X).trace.re ≤
      informationMass hX.1.isHermitian.eigenvalues (Real.log r + t) +
        Real.exp (-t / 2) := by
  rw [informationMass_eq_spectralMass, ← cutoff_sqrt_eq r t hr]
  exact density_effect_spectrum_bound X M hX hM hI r _ hbudget (Real.exp_pos _).le

/-- Initial global unitaries are absorbed into the physical effect, leaving
the original input eigenspectrum on the right hand side. -/
theorem density_effect_unitary_information_bound (X M : Matrix ι ι ℂ)
    (hX : X.PosSemidef ∧ X.trace = 1)
    (hM : M.PosSemidef) (hI : (1 - M).PosSemidef)
    (r t : ℝ) (hr : 0 < r) (hbudget : (M * M).trace.re ≤ r)
    (U : Matrix.unitaryGroup ι ℂ) :
    (M * ((U : Matrix ι ι ℂ) * X * (U : Matrix ι ι ℂ)ᴴ)).trace.re ≤
      informationMass hX.1.isHermitian.eigenvalues (Real.log r + t) +
        Real.exp (-t / 2) := by
  let B := (U : Matrix ι ι ℂ)ᴴ * M * U
  have hB : B.PosSemidef := hM.conjTranspose_mul_mul_same _
  have hU : (U : Matrix ι ι ℂ)ᴴ * U = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have hIB : (1 - B).PosSemidef := by
    have h := hI.conjTranspose_mul_mul_same (U : Matrix ι ι ℂ)
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU] using h
  have hb : (B * B).trace.re ≤ r := by
    rw [show (B * B).trace = (M * M).trace from trace_square_unitary_congruence M U]
    exact hbudget
  have h := density_effect_information_bound X B hX hB hIB r t hr hb
  have he : (M * ((U : Matrix ι ι ℂ) * X * (U : Matrix ι ι ℂ)ᴴ)).trace =
      (B * X).trace := by
    calc
      _ = (((U : Matrix ι ι ℂ)ᴴ * M) * ((U : Matrix ι ι ℂ) * X)).trace := by
        simpa only [Matrix.mul_assoc] using
          (Matrix.trace_mul_cycle' M ((U : Matrix ι ι ℂ) * X) (U : Matrix ι ι ℂ)ᴴ)
      _ = _ := by simp only [B, Matrix.mul_assoc]
  rwa [he]

variable {a b d κ : Type*} [Fintype a] [Fintype b] [Fintype d] [Fintype κ]
  [DecidableEq a] [DecidableEq b] [DecidableEq d]
  [Nonempty a] [Nonempty b] [Nonempty d]

/-- The physical finite-block upper bound in the manuscript, starting from an
actual finite Kraus channel, trace preservation, transpose-conjugate positivity,
an actual density, and any original-space global unitary. -/
theorem kraus_target_information_bound
    (A : κ → Matrix (d × d) (a × b) ℂ)
    (hcomplete : ∑ j, (A j)ᴴ * A j = 1)
    (hpt : Extraction.PTConjugatePositive A)
    (X : Matrix (a × b) (a × b) ℂ) (hX : APPT.Quantum.IsDensity X)
    (U : Matrix.unitaryGroup (a × b) ℂ) (t : ℝ) :
    (Extraction.bellProjector (d := d) *
      Extraction.krausApply A ((U : Matrix (a × b) (a × b) ℂ) * X *
        (U : Matrix (a × b) (a × b) ℂ)ᴴ)).trace.re ≤
      informationMass hX.1.isHermitian.eigenvalues
        (Real.log ((Fintype.card a * Fintype.card b : ℝ) /
          (Fintype.card d : ℝ)^2) + t) + Real.exp (-t / 2) := by
  rw [Extraction.target_overlap_eq]
  have hM := Extraction.targetEffect_rains A hcomplete hpt
  exact density_effect_unitary_information_bound X (Extraction.targetEffect A)
    hX hM.1 hM.2.1 _ t (by positivity)
    (Extraction.rainsEffect_trace_square_le _ _ hM) U

end ExtractionSpectrum
