import Entry002.GenericSignedArithmetic
import Entry002.TinySteps
import Entry002.SieveReduction

/-!
# Genuine positive rescaling of the full planar lattice

The new embedding is a real linear equivalence obtained by composing the
supplied coordinate isomorphism with multiplication by a positive real number.
Norms, distances and cell areas are the actual Euclidean quantities. Scaling
is selected from proved arithmetic and lattice constants before any walk or
step-bound quantifier. All proofs in this module are new.
-/
set_option autoImplicit false
namespace Entry002
open Module
open scoped BigOperators
variable {L : Type*} [AddCommGroup L]

noncomputable def scaledEmbeddingEquiv (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (scale : ℝ) (hscale : 0 < scale) : CoeffSpace ≃ₗ[ℝ] Plane :=
  e.trans (LinearEquiv.smulOfNeZero ℝ Plane scale hscale.ne')

@[simp] theorem scaledEmbeddingEquiv_apply (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (scale : ℝ) (hscale : 0 < scale) (x : CoeffSpace) :
    scaledEmbeddingEquiv e scale hscale x = scale • e x := by
  simp [scaledEmbeddingEquiv]

@[simp] theorem planarEmbedding_scaled (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (scale : ℝ) (hscale : 0 < scale) (x : L) :
    planarEmbedding b (scaledEmbeddingEquiv e scale hscale) x = scale • planarEmbedding b e x := by
  simp only [planarEmbedding, scaledEmbeddingEquiv_apply]

@[simp] theorem planarEmbedding_scaled_norm (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (scale : ℝ) (hscale : 0 < scale) (x : L) :
    ‖planarEmbedding b (scaledEmbeddingEquiv e scale hscale) x‖ = scale * ‖planarEmbedding b e x‖ := by
  rw [planarEmbedding_scaled, norm_smul, Real.norm_eq_abs, abs_of_pos hscale]

@[simp] theorem planarEmbedding_scaled_dist (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (scale : ℝ) (hscale : 0 < scale) (x y : L) :
    dist (planarEmbedding b (scaledEmbeddingEquiv e scale hscale) x)
      (planarEmbedding b (scaledEmbeddingEquiv e scale hscale) y) =
    scale * dist (planarEmbedding b e x) (planarEmbedding b e y) := by
  simp only [dist_eq_norm, planarEmbedding_scaled, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos hscale]

@[simp] theorem planarCellDet_scaled (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (scale : ℝ) (hscale : 0 < scale) :
    planarCellDet (scaledEmbeddingEquiv e scale hscale) = scale^2 * planarCellDet e := by
  simp only [planarCellDet, signedPlaneDet, scaledEmbeddingEquiv_apply,
    PiLp.smul_apply, smul_eq_mul]
  ring

@[simp] theorem planarCellArea_scaled (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (scale : ℝ) (hscale : 0 < scale) :
    |planarCellDet (scaledEmbeddingEquiv e scale hscale)| = scale^2 * |planarCellDet e| := by
  rw [planarCellDet_scaled, abs_mul, abs_of_nonneg (sq_nonneg scale)]

/-- Every positive scalar rescaling preserves all five actual hypotheses. -/
theorem ArithmeticInterface.scaled {data : SignedResidueData L}
    {b : Basis (Fin 2) ℤ L} {e : CoeffSpace ≃ₗ[ℝ] Plane}
    (A : ArithmeticInterface data b e) (scale : ℝ) (hscale : 0 < scale) :
    ArithmeticInterface data b (scaledEmbeddingEquiv e scale hscale) := by
  obtain ⟨c, hc, hcollision⟩ := A.collision
  obtain ⟨C, hC, hproduct⟩ := A.eligible_product
  refine ⟨A.crt, A.paired_kernel, ?_, ?_, A.density⟩
  · refine ⟨scale*c, mul_pos hscale hc, ?_⟩
    intro p hp σ x hx hzero
    rw [planarEmbedding_scaled_norm]
    have hh := mul_le_mul_of_nonneg_left (hcollision p hp σ x hx hzero) hscale.le
    simpa only [mul_assoc] using hh
  · refine ⟨max 1 (C/scale^2), le_max_left _ _, ?_⟩
    intro v hv S hS
    rw [planarEmbedding_scaled_norm, mul_pow]
    have hbase := hproduct v hv S hS
    have hcoef : C ≤ max 1 (C/scale^2) * scale^2 :=
      (div_le_iff₀ (sq_pos_of_pos hscale)).mp (le_max_right _ _)
    have hh := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖planarEmbedding b e v‖)
    exact hbase.trans (by simpa only [mul_assoc] using hh)

/-- One actual scaling, fixed before every walk, normalizes separation,
collision, eligible products and the fundamental cell area simultaneously. -/
theorem ArithmeticInterface.exists_normalized_embedding {data : SignedResidueData L}
    {b : Basis (Fin 2) ℤ L} {e : CoeffSpace ≃ₗ[ℝ] Plane}
    (A : ArithmeticInterface data b e) :
    ∃ scale : ℝ, ∃ hscale : 0 < scale,
      ArithmeticInterface data b (scaledEmbeddingEquiv e scale hscale) ∧
      (∀ x : L, x ≠ 0 → 1 ≤ ‖planarEmbedding b (scaledEmbeddingEquiv e scale hscale) x‖) ∧
      (∀ p ∈ data.primes, ∀ σ : Bool, ∀ x : L, x ≠ 0 → data.phi p σ x = 0 →
        Real.sqrt p ≤ ‖planarEmbedding b (scaledEmbeddingEquiv e scale hscale) x‖) ∧
      (∀ v : L, IsPrimitive v → ∀ S : Finset ℕ, (∀ p ∈ S, p ∈ data.primes) →
        (S.filter (fun p => data.phi p true v = 0 ∨ data.phi p false v = 0)).prod
          (fun p => (p : ℝ)) ≤ ‖planarEmbedding b (scaledEmbeddingEquiv e scale hscale) v‖^2) ∧
      1 ≤ |planarCellDet (scaledEmbeddingEquiv e scale hscale)| := by
  obtain ⟨δ, hδ, hsep⟩ := planarEmbedding_positive_separation b e
  obtain ⟨c, hc, hcollision⟩ := A.collision
  obtain ⟨C, hC, hproduct⟩ := A.eligible_product
  have harea : 0 < |planarCellDet e| := abs_pos.mpr (planarCellDet_ne_zero e)
  let scale : ℝ := max 1 (max δ⁻¹ (max c⁻¹ (max C |planarCellDet e|⁻¹)))
  have hscale1 : 1 ≤ scale := le_max_left _ _
  have hscale : 0 < scale := zero_lt_one.trans_le hscale1
  have hδinv : δ⁻¹ ≤ scale := (le_max_left _ _).trans (le_max_right _ _)
  have hcinv : c⁻¹ ≤ scale := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hCle : C ≤ scale := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hareainv : |planarCellDet e|⁻¹ ≤ scale := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hscaleδ : 1 ≤ scale*δ := by
    have hh := mul_le_mul_of_nonneg_right hδinv hδ.le
    simpa only [inv_mul_cancel₀ hδ.ne'] using hh
  have hscalec : 1 ≤ scale*c := by
    have hh := mul_le_mul_of_nonneg_right hcinv hc.le
    simpa only [inv_mul_cancel₀ hc.ne'] using hh
  have hscalearea : 1 ≤ scale*|planarCellDet e| := by
    have hh := mul_le_mul_of_nonneg_right hareainv harea.le
    simpa only [inv_mul_cancel₀ harea.ne'] using hh
  have hCscalesq : C ≤ scale^2 := by nlinarith only [hCle, hscale1]
  refine ⟨scale, hscale, A.scaled scale hscale, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [planarEmbedding_scaled_norm]
    exact hscaleδ.trans (mul_le_mul_of_nonneg_left (hsep x hx) hscale.le)
  · intro p hp σ x hx hzero
    rw [planarEmbedding_scaled_norm]
    have hh := mul_le_mul_of_nonneg_left (hcollision p hp σ x hx hzero) hscale.le
    have hsqrt := Real.sqrt_nonneg (p : ℝ)
    nlinarith only [hh, hscalec, hsqrt]
  · intro v hv S hS
    rw [planarEmbedding_scaled_norm, mul_pow]
    exact (hproduct v hv S hS).trans
      (mul_le_mul_of_nonneg_right hCscalesq (sq_nonneg _))
  · rw [planarCellArea_scaled]
    nlinarith only [hscalearea, hscale1, harea]

/-- Rescaling preserves the actual lattice graph exactly when its step bound
is scaled by the same positive scalar. -/
theorem latticeGraph_scaled (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (scale : ℝ) (hscale : 0 < scale)
    (D : ℝ) (V : Set L) :
    latticeGraph b (scaledEmbeddingEquiv e scale hscale) (scale*D) V = latticeGraph b e D V := by
  ext x y
  change (x ≠ y ∧ ‖planarEmbedding b (scaledEmbeddingEquiv e scale hscale) x.val -
    planarEmbedding b (scaledEmbeddingEquiv e scale hscale) y.val‖ ≤ scale*D) ↔ _
  simp only [← dist_eq_norm, planarEmbedding_scaled_dist]
  constructor
  · rintro ⟨hne, hstep⟩
    exact ⟨hne, (mul_le_mul_iff_right₀ hscale).mp hstep⟩
  · rintro ⟨hne, hstep⟩
    exact ⟨hne, mul_le_mul_of_nonneg_left hstep hscale.le⟩

/-- A finite selection excluding every walk in the rescaled graph excludes
all walks in the original graph, with the same actual prime selection. -/
theorem avoiding_no_walk_of_scaled (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (data : SignedResidueData L) (S : Finset ℕ)
    (scale : ℝ) (hscale : 0 < scale) (D : ℝ)
    (hno : ∀ w : ℕ → avoiding data S, Function.Injective w →
      (∀ n, (latticeGraph b (scaledEmbeddingEquiv e scale hscale) (scale*D) (avoiding data S)).Adj
        (w n) (w (n+1))) → False) :
    ∀ w : ℕ → avoiding data S, Function.Injective w →
      (∀ n, (latticeGraph b e D (avoiding data S)).Adj (w n) (w (n+1))) → False := by
  simpa only [latticeGraph_scaled] using hno


/-- It suffices to prove the analytic no-walk theorem for genuine normalized
embeddings and step bounds at least one. This is an implication with the
normalized analytic theorem displayed as its hypothesis. -/
theorem finiteSieveNoWalkTarget_of_normalized
    (hnormalized : ∀ (M : Type) [AddCommGroup M]
      (basis : Basis (Fin 2) ℤ M) (embedding : CoeffSpace ≃ₗ[ℝ] Plane)
      (data : SignedResidueData M), ArithmeticInterface data basis embedding →
      (∀ x : M, x ≠ 0 → 1 ≤ ‖planarEmbedding basis embedding x‖) →
      (∀ p ∈ data.primes, ∀ σ : Bool, ∀ x : M, x ≠ 0 → data.phi p σ x = 0 →
        Real.sqrt p ≤ ‖planarEmbedding basis embedding x‖) →
      (∀ v : M, IsPrimitive v → ∀ S : Finset ℕ, (∀ p ∈ S, p ∈ data.primes) →
        (S.filter (fun p => data.phi p true v = 0 ∨ data.phi p false v = 0)).prod
          (fun p => (p : ℝ)) ≤ ‖planarEmbedding basis embedding v‖^2) →
      1 ≤ |planarCellDet embedding| →
      ∀ D : ℝ, 1 ≤ D → ∃ S : Finset ℕ,
        (∀ p ∈ S, p ∈ data.primes) ∧
        ∀ w : ℕ → avoiding data S, Function.Injective w →
          (∀ n, (latticeGraph basis embedding D (avoiding data S)).Adj
            (w n) (w (n+1))) → False) : FiniteSieveNoWalkTarget := by
  intro M _ basis embedding data hA D _
  obtain ⟨scale, hscale, hAscale, hsep, hcollision, hproduct, hcell⟩ :=
    hA.exists_normalized_embedding
  obtain ⟨S, hS, hno⟩ := hnormalized M basis (scaledEmbeddingEquiv embedding scale hscale)
    data hAscale hsep hcollision hproduct hcell (max 1 (scale*D)) (le_max_left _ _)
  refine ⟨S, hS, ?_⟩
  apply avoiding_no_walk_of_scaled basis embedding data S scale hscale D
  intro w hinj hstep
  apply hno w hinj
  intro n
  exact ⟨(hstep n).1, (hstep n).2.trans (le_max_right _ _)⟩

end Entry002
