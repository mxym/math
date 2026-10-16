import SpectralProtocol.SpectralPacking

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace SpectralProtocol

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conjugation by an actual matrix unitary preserves multiplication. -/
theorem unitary_conjugation_mul (U : Matrix.unitaryGroup ι ℂ)
    (A B : Matrix ι ι ℂ) :
    ((U : Matrix ι ι ℂ)*A*(U : Matrix ι ι ℂ)ᴴ) *
      ((U : Matrix ι ι ℂ)*B*(U : Matrix ι ι ℂ)ᴴ) =
    (U : Matrix ι ι ℂ)*(A*B)*(U : Matrix ι ι ℂ)ᴴ := by
  have hU : (U : Matrix ι ι ℂ)ᴴ * U = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U : Matrix ι ι ℂ)ᴴ, hU, Matrix.one_mul]

/-- An arbitrary finite set of actual eigenvectors selects a genuine support
projection. No projection, rank certificate, or spectral truncation is supplied
by the caller. -/
noncomputable def spectralProjection (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (s : Finset ι) : Matrix ι ι ℂ :=
  (hX.eigenvectorUnitary : Matrix ι ι ℂ) *
    Matrix.diagonal (fun i => if i ∈ s then (1:ℂ) else 0) *
    (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ

noncomputable def spectralSelection (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (s : Finset ι) : Matrix ι ι ℂ :=
  (hX.eigenvectorUnitary : Matrix ι ι ℂ) *
    Matrix.diagonal (fun i => if i ∈ s then (hX.eigenvalues i : ℂ) else 0) *
    (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ

theorem spectralProjection_posSemidef (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (s : Finset ι) : (spectralProjection X hX s).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  dsimp only
  simp only [Pi.zero_apply]
  split_ifs <;> positivity

theorem spectralProjection_idempotent (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (s : Finset ι) : spectralProjection X hX s * spectralProjection X hX s =
      spectralProjection X hX s := by
  unfold spectralProjection
  rw [unitary_conjugation_mul, Matrix.diagonal_mul_diagonal]
  congr 2
  apply congrArg Matrix.diagonal
  funext i
  split_ifs <;> simp

theorem spectralProjection_trace (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (s : Finset ι) : (spectralProjection X hX s).trace = (s.card : ℂ) := by
  have hU : (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * hX.eigenvectorUnitary = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hX.eigenvectorUnitary
  rw [spectralProjection, Extraction.isometry_trace_congruence _ hU, Matrix.trace_diagonal]
  simp

theorem spectralProjection_rank (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (s : Finset ι) : (spectralProjection X hX s).rank = s.card := by
  have hp := projection_trace_eq_rank _ (spectralProjection_posSemidef X hX s).isHermitian
    (spectralProjection_idempotent X hX s)
  rw [spectralProjection_trace] at hp
  exact_mod_cast hp.symm

theorem spectralSelection_posSemidef (X : Matrix ι ι ℂ) (hX : X.PosSemidef)
    (s : Finset ι) : (spectralSelection X hX.isHermitian s).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  dsimp only
  simp only [Pi.zero_apply]
  split_ifs
  · exact_mod_cast hX.eigenvalues_nonneg i
  · exact le_rfl

theorem spectralSelection_supported (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (s : Finset ι) :
    spectralProjection X hX s * spectralSelection X hX s * spectralProjection X hX s =
      spectralSelection X hX s := by
  unfold spectralProjection spectralSelection
  rw [unitary_conjugation_mul, unitary_conjugation_mul,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 2
  apply congrArg Matrix.diagonal
  funext i
  split_ifs <;> simp

theorem spectralSelection_trace_re (X : Matrix ι ι ℂ) (hX : X.IsHermitian)
    (s : Finset ι) : (spectralSelection X hX s).trace.re = ∑ i ∈ s, hX.eigenvalues i := by
  have hU : (hX.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ * hX.eigenvectorUnitary = 1 := by
    simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using
      Unitary.coe_star_mul_self hX.eigenvectorUnitary
  rw [spectralSelection, Extraction.isometry_trace_congruence _ hU, Matrix.trace_diagonal]
  simp

theorem spectralSelection_remainder_posSemidef (X : Matrix ι ι ℂ) (hX : X.PosSemidef)
    (s : Finset ι) : (X - spectralSelection X hX.isHermitian s).PosSemidef := by
  have hs : X = (hX.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => (hX.isHermitian.eigenvalues i : ℂ)) *
      (hX.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
    simpa only [Unitary.conjStarAlgAut_apply, Unitary.coe_star, Matrix.star_eq_conjTranspose,
      RCLike.ofReal_eq_complex_ofReal, Function.comp_def] using hX.isHermitian.spectral_theorem
  have he : X - spectralSelection X hX.isHermitian s =
      (hX.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ) *
        Matrix.diagonal (fun i => if i ∈ s then (0:ℂ) else (hX.isHermitian.eigenvalues i : ℂ)) *
        (hX.isHermitian.eigenvectorUnitary : Matrix ι ι ℂ)ᴴ := by
    conv_lhs => lhs; rw [hs]
    simp only [spectralSelection, ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
    congr 2
    apply congrArg Matrix.diagonal
    funext i
    split_ifs <;> simp
  rw [he]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  dsimp only
  simp only [Pi.zero_apply]
  split_ifs
  · exact le_rfl
  · exact_mod_cast hX.eigenvalues_nonneg i

/-- A finite spectral-prefix (indeed arbitrary spectral subset) protocol on the
original input, with no positive-remainder or common-unitary assumption left
for the caller to prove. -/
theorem spectral_subset_actual_lower (a b d K : ℕ) (hd : 0 < d) (hdk : d ≤ K)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) (hX : X.PosSemidef)
    (s : Finset (Fin a × Fin b)) (hr : s.card ≤ (a/d)*(b/d)) :
    ∃ (U : Matrix.unitaryGroup (Fin a × Fin b) ℂ)
      (A : Fin (a/d) ⊕ Fin a → Matrix (Fin K) (Fin a) ℂ)
      (B : Fin (b/d) ⊕ Fin b → Matrix (Fin K) (Fin b) ℂ),
      (∑ j, (A j)ᴴ * A j = 1) ∧ (∑ j, (B j)ᴴ * B j = 1) ∧
      ((d:ℝ)/K) * (∑ i ∈ s, hX.isHermitian.eigenvalues i) ≤
        (Extraction.bellProjector (d := Fin K) *
          Extraction.krausApply (Extraction.productKraus A B)
            ((U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) * X *
              (U : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ)ᴴ)).trace.re := by
  obtain ⟨U,A,B,hA,hB,he⟩ := finite_projection_positive_submatrix_lower a b d K hd hdk
    (spectralProjection X hX.isHermitian s)
    (spectralProjection_posSemidef X hX.isHermitian s).isHermitian
    (spectralProjection_idempotent X hX.isHermitian s)
    (by simpa only [spectralProjection_rank] using hr)
  refine ⟨U,A,B,hA,hB,?_⟩
  simpa only [spectralSelection_trace_re] using he X (spectralSelection X hX.isHermitian s)
    (spectralSelection_posSemidef X hX s) (spectralSelection_remainder_posSemidef X hX s)
    (spectralSelection_supported X hX.isHermitian s)

end SpectralProtocol