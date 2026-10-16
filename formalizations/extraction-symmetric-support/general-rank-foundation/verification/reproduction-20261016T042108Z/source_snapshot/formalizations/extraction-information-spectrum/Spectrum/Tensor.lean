import Spectrum.Finite
import Mathlib.Algebra.BigOperators.Ring.Finset

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSpectrum

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The canonical iid spectral weights on words, retaining zero probabilities. -/
def iidLaw (p : ι → ℝ) (k : ℕ) (w : Fin k → ι) : ℝ := ∏ j, p (w j)

theorem iidLaw_nonneg (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (k : ℕ) (w : Fin k → ι) :
    0 ≤ iidLaw p k w := Finset.prod_nonneg fun j _ => hp _

theorem iidLaw_sum (p : ι → ℝ) (hs : ∑ i, p i = 1) (k : ℕ) :
    ∑ w, iidLaw p k w = 1 := by
  simp only [iidLaw]
  rw [← Fintype.sum_pow, hs, one_pow]

/-- Exact finite probability of the iid self-information sum. Terms containing
a zero-probability letter have zero mass, independently of the totalized log. -/
noncomputable def iidInformationEvent (p : ι → ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  ∑ w : Fin k → ι, if (∑ j, -Real.log (p (w j))) ≤ x then iidLaw p k w else 0

theorem iidInformationEvent_mono (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (k : ℕ) {x y : ℝ} (hxy : x ≤ y) :
    iidInformationEvent p k x ≤ iidInformationEvent p k y := by
  classical
  apply Finset.sum_le_sum
  intro w _
  by_cases hx : (∑ j, -Real.log (p (w j))) ≤ x
  · simp only [hx, ite_true, hx.trans hxy]
    exact le_rfl
  · simp only [hx, ite_false]
    split_ifs
    · exact iidLaw_nonneg p hp k w
    · exact le_rfl

theorem informationMass_iidLaw (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (k : ℕ) (x : ℝ) :
    informationMass (iidLaw p k) x = iidInformationEvent p k x := by
  classical
  apply Finset.sum_congr rfl
  intro w _
  by_cases hz : iidLaw p k w = 0
  · simp [hz]
  · have hpos := lt_of_le_of_ne (iidLaw_nonneg p hp k w) (Ne.symm hz)
    have hf (j : Fin k) : p (w j) ≠ 0 := by
      intro h
      exact hz (Finset.prod_eq_zero (Finset.mem_univ j) h)
    have he : -Real.log (iidLaw p k w) = ∑ j, -Real.log (p (w j)) := by
      rw [iidLaw, Real.log_prod (fun j _ => hf j), Finset.sum_neg_distrib]
    simp only [hpos, true_and, he]

/-- Canonical tensor powers in the original coordinate basis. -/
def tensorMatrix (M : Matrix ι ι ℂ) (k : ℕ) :
    Matrix (Fin k → ι) (Fin k → ι) ℂ := fun w v => ∏ j, M (w j) (v j)

theorem tensorMatrix_mul (M Q : Matrix ι ι ℂ) (k : ℕ) :
    tensorMatrix (M * Q) k = tensorMatrix M k * tensorMatrix Q k := by
  classical
  ext w v
  simp only [tensorMatrix, Matrix.mul_apply]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro u _
  exact Finset.prod_mul_distrib

theorem tensorMatrix_conjTranspose (M : Matrix ι ι ℂ) (k : ℕ) :
    tensorMatrix Mᴴ k = (tensorMatrix M k)ᴴ := by
  ext w v
  simp only [tensorMatrix, Matrix.conjTranspose_apply, star_prod]

theorem tensorMatrix_one (k : ℕ) :
    tensorMatrix (1 : Matrix ι ι ℂ) k = 1 := by
  classical
  ext w v
  by_cases h : w = v
  · subst v
    simp [tensorMatrix]
  · obtain ⟨j, hj⟩ : ∃ j, w j ≠ v j := Function.ne_iff.mp h
    simp only [tensorMatrix, Matrix.one_apply, if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

theorem tensorMatrix_diagonal (p : ι → ℝ) (k : ℕ) :
    tensorMatrix (Matrix.diagonal fun i => (p i : ℂ)) k =
      Matrix.diagonal fun w => (iidLaw p k w : ℂ) := by
  classical
  ext w v
  by_cases h : w = v
  · subst v
    simp [tensorMatrix, iidLaw]
  · obtain ⟨j, hj⟩ : ∃ j, w j ≠ v j := Function.ne_iff.mp h
    simp only [tensorMatrix, Matrix.diagonal_apply, if_neg h]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (if_neg hj)

/-- Tensoring an existing-space unitary produces an existing-space unitary. -/
def tensorUnitary (V : Matrix.unitaryGroup ι ℂ) (k : ℕ) :
    Matrix.unitaryGroup (Fin k → ι) ℂ := by
  classical
  refine ⟨tensorMatrix (V : Matrix ι ι ℂ) k, ?_⟩
  constructor
  · change (tensorMatrix (V : Matrix ι ι ℂ) k)ᴴ * tensorMatrix (V : Matrix ι ι ℂ) k = 1
    rw [← tensorMatrix_conjTranspose, ← tensorMatrix_mul]
    have h : (V : Matrix ι ι ℂ)ᴴ * V = 1 := by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
    rw [h, tensorMatrix_one]
  · change tensorMatrix (V : Matrix ι ι ℂ) k * (tensorMatrix (V : Matrix ι ι ℂ) k)ᴴ = 1
    rw [← tensorMatrix_conjTranspose, ← tensorMatrix_mul]
    have h : (V : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ)ᴴ = 1 := by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self V
    rw [h, tensorMatrix_one]

/-- The iid product law is obtained by tensoring the actual matrix spectral
decomposition. This is not an assumed tensor-spectrum assertion. -/
theorem tensorMatrix_spectral (X : Matrix ι ι ℂ) (hX : X.IsHermitian) (k : ℕ) :
    tensorMatrix X k =
      (tensorUnitary hX.eigenvectorUnitary k : Matrix (Fin k → ι) (Fin k → ι) ℂ) *
        Matrix.diagonal (fun w => (iidLaw hX.eigenvalues k w : ℂ)) *
      (tensorUnitary hX.eigenvectorUnitary k : Matrix (Fin k → ι) (Fin k → ι) ℂ)ᴴ := by
  have h := hX.spectral_theorem
  simp only [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    RCLike.ofReal_eq_complex_ofReal, Function.comp_def] at h
  calc
    _ = tensorMatrix ((hX.eigenvectorUnitary : Matrix ι ι ℂ) *
        Matrix.diagonal (fun i => (hX.eigenvalues i : ℂ)) *
        (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ) k := congrArg (fun M => tensorMatrix M k) h
    _ = _ := by
      simp only [tensorMatrix_mul, tensorMatrix_diagonal, tensorMatrix_conjTranspose]
      rfl

/-- The canonical tensor entries form an actual density, including singular
one-copy inputs and blocklength zero. -/
theorem tensorMatrix_density (X : Matrix ι ι ℂ)
    (hX : X.PosSemidef ∧ X.trace = 1) (k : ℕ) :
    (tensorMatrix X k).PosSemidef ∧ (tensorMatrix X k).trace = 1 := by
  classical
  let p := hX.1.isHermitian.eigenvalues
  let V := tensorUnitary hX.1.isHermitian.eigenvectorUnitary k
  have he := tensorMatrix_spectral X hX.1.isHermitian k
  have hD : (Matrix.diagonal fun w => (iidLaw p k w : ℂ)).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro w
    exact RCLike.nonneg_iff.mpr ⟨iidLaw_nonneg p (fun i => hX.1.eigenvalues_nonneg i) k w,
      Complex.ofReal_im (iidLaw p k w)⟩
  constructor
  · rw [he]
    exact hD.mul_mul_conjTranspose_same _
  · rw [he, Matrix.trace_mul_cycle]
    have hV : (V : Matrix (Fin k → ι) (Fin k → ι) ℂ)ᴴ * V = 1 := by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
    change (((V : Matrix (Fin k → ι) (Fin k → ι) ℂ)ᴴ * V) *
      Matrix.diagonal (fun w => (iidLaw p k w : ℂ))).trace = 1
    rw [hV, Matrix.one_mul, Matrix.trace_diagonal]
    exact_mod_cast iidLaw_sum p (density_eigenvalues_sum X hX) k

/-- Finite information-spectrum upper bound for canonical tensor powers.
The probability is the finite iid law of the one-copy actual eigenvalues. -/
theorem tensorMatrix_effect_information_bound (X : Matrix ι ι ℂ)
    (hX : X.PosSemidef ∧ X.trace = 1) (k : ℕ)
    (M : Matrix (Fin k → ι) (Fin k → ι) ℂ)
    (hM : M.PosSemidef) (hI : (1 - M).PosSemidef)
    (r t : ℝ) (hr : 0 < r) (hbudget : (M * M).trace.re ≤ r) :
    (M * tensorMatrix X k).trace.re ≤
      iidInformationEvent hX.1.isHermitian.eigenvalues k (Real.log r + t) +
        Real.exp (-t / 2) := by
  have h := diagonalized_effect_information_bound (iidLaw hX.1.isHermitian.eigenvalues k)
    (iidLaw_nonneg _ (fun i => hX.1.eigenvalues_nonneg i) k)
    (iidLaw_sum _ (density_eigenvalues_sum X hX) k)
    (tensorUnitary hX.1.isHermitian.eigenvectorUnitary k) M hM hI r t hr hbudget
  rw [← tensorMatrix_spectral X hX.1.isHermitian k] at h
  rwa [informationMass_iidLaw _ (fun i => hX.1.eigenvalues_nonneg i) k] at h

end ExtractionSpectrum
