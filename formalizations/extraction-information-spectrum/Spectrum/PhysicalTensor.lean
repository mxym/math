import Spectrum.Tensor

open scoped BigOperators ComplexOrder
open Matrix

namespace ExtractionSpectrum

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Reindexing only changes the names of coordinates of a genuine unitary. -/
def reindexUnitary (e : κ ≃ ι) (V : Matrix.unitaryGroup ι ℂ) :
    Matrix.unitaryGroup κ ℂ := by
  refine ⟨(V : Matrix ι ι ℂ).submatrix e e, ?_⟩
  constructor
  · change ((V : Matrix ι ι ℂ).submatrix e e)ᴴ * (V : Matrix ι ι ℂ).submatrix e e = 1
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    have h : (V : Matrix ι ι ℂ)ᴴ * V = 1 := by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self V
    rw [h, Matrix.submatrix_one_equiv]
  · change (V : Matrix ι ι ℂ).submatrix e e * ((V : Matrix ι ι ℂ).submatrix e e)ᴴ = 1
    rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    have h : (V : Matrix ι ι ℂ) * (V : Matrix ι ι ℂ)ᴴ = 1 := by
      simpa only [Unitary.coe_star, Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self V
    rw [h, Matrix.submatrix_one_equiv]

theorem informationMass_reindex (p : ι → ℝ) (e : κ ≃ ι) (x : ℝ) :
    informationMass (p ∘ e) x = informationMass p x := by
  classical
  exact e.sum_comp fun i => if 0 < p i ∧ -Real.log (p i) ≤ x then p i else 0

variable {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

/-- The canonical regrouping of iid copies into Alice's and Bob's original
tensor factors. -/
def bipartiteWordEquiv (k : ℕ) : ((Fin k → a) × (Fin k → b)) ≃ (Fin k → a × b) :=
  { toFun := fun w j => (w.1 j, w.2 j)
    invFun := fun w => (fun j => (w j).1, fun j => (w j).2)
    left_inv := by intro w; rcases w with ⟨x,y⟩; rfl
    right_inv := by intro w; rfl }

/-- Actual tensor entries after the canonical bipartite regrouping. -/
def bipartiteTensor (X : Matrix (a × b) (a × b) ℂ) (k : ℕ) :
    Matrix ((Fin k → a) × (Fin k → b)) ((Fin k → a) × (Fin k → b)) ℂ :=
  (tensorMatrix X k).submatrix (bipartiteWordEquiv k) (bipartiteWordEquiv k)

theorem bipartiteTensor_apply (X : Matrix (a × b) (a × b) ℂ) (k : ℕ)
    (w v : (Fin k → a) × (Fin k → b)) :
    bipartiteTensor X k w v = ∏ j, X (w.1 j, w.2 j) (v.1 j, v.2 j) := rfl

theorem bipartiteTensor_density (X : Matrix (a × b) (a × b) ℂ)
    (hX : APPT.Quantum.IsDensity X) (k : ℕ) :
    APPT.Quantum.IsDensity (bipartiteTensor X k) := by
  have h := tensorMatrix_density X hX k
  refine ⟨h.1.submatrix (bipartiteWordEquiv k), ?_⟩
  let e := bipartiteWordEquiv (a := a) (b := b) k
  exact (e.sum_comp (fun w => tensorMatrix X k w w)).trans h.2

/-- The spectral decomposition of the actual regrouped tensor is proved by
tensoring, then reindexing, the one-copy actual spectral unitary. -/
theorem bipartiteTensor_spectral (X : Matrix (a × b) (a × b) ℂ)
    (hX : X.IsHermitian) (k : ℕ) :
    bipartiteTensor X k =
      (reindexUnitary (bipartiteWordEquiv k) (tensorUnitary hX.eigenvectorUnitary k) :
        Matrix ((Fin k → a) × (Fin k → b)) ((Fin k → a) × (Fin k → b)) ℂ) *
        Matrix.diagonal (fun w => (iidLaw hX.eigenvalues k (bipartiteWordEquiv k w) : ℂ)) *
      (reindexUnitary (bipartiteWordEquiv k) (tensorUnitary hX.eigenvectorUnitary k) :
        Matrix ((Fin k → a) × (Fin k → b)) ((Fin k → a) × (Fin k → b)) ℂ)ᴴ := by
  classical
  unfold bipartiteTensor
  rw [tensorMatrix_spectral X hX k]
  change _ = ((tensorUnitary hX.eigenvectorUnitary k :
      Matrix (Fin k → a × b) (Fin k → a × b) ℂ).submatrix
      (bipartiteWordEquiv k) (bipartiteWordEquiv k)) *
      Matrix.diagonal (fun w => (iidLaw hX.eigenvalues k (bipartiteWordEquiv k w) : ℂ)) *
      ((tensorUnitary hX.eigenvectorUnitary k :
        Matrix (Fin k → a × b) (Fin k → a × b) ℂ).submatrix
        (bipartiteWordEquiv k) (bipartiteWordEquiv k))ᴴ
  rw [Matrix.conjTranspose_submatrix]
  have hd := Matrix.submatrix_diagonal_equiv (fun w => (iidLaw hX.eigenvalues k w : ℂ))
    (bipartiteWordEquiv (a := a) (b := b) k)
  dsimp only [Function.comp_def] at hd
  rw [← hd]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]

variable {d ν : Type*} [Fintype d] [Fintype ν] [DecidableEq d]
  [Nonempty a] [Nonempty b] [Nonempty d]

/-- The manuscript's iid finite-block converse on the actual physical tensor
input, with arbitrary global preprocessing and a genuine postprocessing channel.
Both the original one-copy spectrum and the iid probability are derived. -/
theorem kraus_tensor_information_bound (X : Matrix (a × b) (a × b) ℂ)
    (hX : APPT.Quantum.IsDensity X) (k : ℕ)
    (A : ν → Matrix (d × d) ((Fin k → a) × (Fin k → b)) ℂ)
    (hcomplete : ∑ j, (A j)ᴴ * A j = 1)
    (hpt : Extraction.PTConjugatePositive A)
    (U : Matrix.unitaryGroup ((Fin k → a) × (Fin k → b)) ℂ) (t : ℝ) :
    (Extraction.bellProjector (d := d) *
      Extraction.krausApply A ((U : Matrix _ _ ℂ) * bipartiteTensor X k *
        (U : Matrix _ _ ℂ)ᴴ)).trace.re ≤
      iidInformationEvent hX.1.isHermitian.eigenvalues k
        (Real.log ((Fintype.card (Fin k → a) * Fintype.card (Fin k → b) : ℝ) /
          (Fintype.card d : ℝ)^2) + t) + Real.exp (-t / 2) := by
  classical
  let e := bipartiteWordEquiv (a := a) (b := b) k
  let p := hX.1.isHermitian.eigenvalues
  let q := iidLaw p k ∘ e
  let V := reindexUnitary e (tensorUnitary hX.1.isHermitian.eigenvectorUnitary k)
  have hqs : ∑ w, q w = 1 := by
    change ∑ w, iidLaw p k (e w) = 1
    rw [e.sum_comp]
    exact iidLaw_sum p (density_eigenvalues_sum X hX) k
  have hqp (w) : 0 ≤ q w := iidLaw_nonneg p (fun i => hX.1.eigenvalues_nonneg i) k _
  have hsp : (U : Matrix _ _ ℂ) * bipartiteTensor X k * (U : Matrix _ _ ℂ)ᴴ =
      ((U * V : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ) *
        Matrix.diagonal (fun w => (q w : ℂ)) *
      ((U * V : Matrix.unitaryGroup _ ℂ) : Matrix _ _ ℂ)ᴴ := by
    rw [bipartiteTensor_spectral X hX.1.isHermitian k]
    simp only [Submonoid.coe_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rfl
  rw [Extraction.target_overlap_eq, hsp]
  have hM := Extraction.targetEffect_rains A hcomplete hpt
  have h := diagonalized_effect_information_bound q hqp hqs (U * V)
    (Extraction.targetEffect A) hM.1 hM.2.1 _ t (by positivity)
    (Extraction.rainsEffect_trace_square_le _ _ hM)
  have hm : informationMass q
      (Real.log ((Fintype.card (Fin k → a) * Fintype.card (Fin k → b) : ℝ) /
        (Fintype.card d : ℝ)^2) + t) =
      iidInformationEvent p k
        (Real.log ((Fintype.card (Fin k → a) * Fintype.card (Fin k → b) : ℝ) /
          (Fintype.card d : ℝ)^2) + t) := by
    rw [informationMass_reindex (iidLaw p k) e,
      informationMass_iidLaw p (fun i => hX.1.eigenvalues_nonneg i) k]
  rwa [hm] at h

end ExtractionSpectrum
