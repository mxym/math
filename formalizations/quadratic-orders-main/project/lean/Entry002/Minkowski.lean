import Entry002.Isolation
import Entry002.Orders
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

/-! Real Minkowski isolation for the actual conductor orders `ℤ + f 𝓞_K`.
All coordinates below are genuine conjugate field embeddings. -/

namespace Entry002

variable (K : Type*) [Field K] [NumberField K] (f : ℕ)

/-- The actual two real conjugate coordinates of a conductor-order element. -/
noncomputable def conductorRealMinkowski (σ : K →ₐ[ℚ] ℝ)
    (e : Fin 2 ≃ (K ≃ₐ[ℚ] K)) (x : conductorOrder K f) :
    EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i => σ (e i (x : K)))

@[simp] theorem conductorRealMinkowski_apply (σ : K →ₐ[ℚ] ℝ)
    (e : Fin 2 ≃ (K ≃ₐ[ℚ] K)) (x : conductorOrder K f) (i : Fin 2) :
    conductorRealMinkowski K f σ e x i = σ (e i (x : K)) := rfl

theorem conductorRealMinkowski_injective (σ : K →ₐ[ℚ] ℝ)
    (e : Fin 2 ≃ (K ≃ₐ[ℚ] K)) :
    Function.Injective (conductorRealMinkowski K f σ e) := by
  intro x y h
  have h₀ := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 0) h
  exact Subtype.ext ((e 0).injective (σ.injective h₀))

/-- Composing one real embedding with the two automorphisms enumerates all
complex embeddings, since both sets have the genuine field degree two. -/
theorem real_conjugates_cover_complex_embeddings (hK : Module.finrank ℚ K = 2)
    (σ : K →ₐ[ℚ] ℝ) (e : Fin 2 ≃ (K ≃ₐ[ℚ] K)) :
    Function.Surjective (fun i : Fin 2 =>
      Complex.ofRealHom.comp (σ.toRingHom.comp (e i).toRingHom)) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr ?_ |>.2
  constructor
  · intro i j hij
    apply e.injective
    apply AlgEquiv.ext
    intro x
    apply σ.injective
    apply Complex.ofReal_injective
    exact congrArg (fun φ : K →+* ℂ => φ x) hij
  · simp [NumberField.Embeddings.card K ℂ, hK]

/-- Finite balls in the real Minkowski embedding of every actual quadratic
conductor order. No lattice properness or coordinate-norm hypothesis is assumed. -/
theorem conductorRealMinkowski_finite_balls (hK : Module.finrank ℚ K = 2)
    (σ : K →ₐ[ℚ] ℝ) (e : Fin 2 ≃ (K ≃ₐ[ℚ] K)) (T : ℝ) :
    {x : conductorOrder K f | ‖conductorRealMinkowski K f σ e x‖ ≤ T}.Finite := by
  have hs := NumberField.Embeddings.finite_of_norm_le K ℂ T
  have hp : {x : conductorOrder K f | IsIntegral ℤ (x : K) ∧
      ∀ φ : K →+* ℂ, ‖φ (x : K)‖ ≤ T}.Finite :=
    hs.preimage (fun x y _ _ h => Subtype.ext h)
  apply hp.subset
  intro x hx
  refine ⟨conductorOrder_isIntegral K f x, ?_⟩
  intro φ
  obtain ⟨i, rfl⟩ := real_conjugates_cover_complex_embeddings K hK σ e φ
  have hi := PiLp.norm_apply_le (conductorRealMinkowski K f σ e x) i
  change ‖(σ (e i (x : K)) : ℂ)‖ ≤ T
  simpa only [Complex.norm_real, conductorRealMinkowski_apply] using hi.trans hx

/-- The explicit radius, with all arithmetic hypotheses discharged for actual
elements of a positive conductor order in a real quadratic field. -/
theorem conductorRealMinkowski_pair_radius (hK : Module.finrank ℚ K = 2)
    (hf : 0 < f) (σ : K →ₐ[ℚ] ℝ) (e : Fin 2 ≃ (K ≃ₐ[ℚ] K))
    {x y : conductorOrder K f} {M R : ℝ} (hM : 0 ≤ M) (hne : x ≠ y)
    (hx : |(Algebra.norm ℤ x : ℝ)| ≤ M) (hy : |(Algebra.norm ℤ y : ℝ)| ≤ M)
    (hR : ‖conductorRealMinkowski K f σ e y - conductorRealMinkowski K f σ e x‖ ≤ R) :
    ‖conductorRealMinkowski K f σ e x‖ ≤ (2 * M + 2) * R ∧
      ‖conductorRealMinkowski K f σ e y‖ ≤ (2 * M + 2) * R := by
  obtain ⟨n, hn, hn0⟩ := conductorOrder_real_difference_integral K f hK hf σ e x y hne
  have hv : 1 ≤ |(σ (e 0 (y : K)) - σ (e 0 (x : K))) *
      (σ (e 1 (y : K)) - σ (e 1 (x : K)))| := by
    apply one_le_abs_of_nonzero_integer ⟨n, hn⟩
    rw [hn]
    exact_mod_cast hn0
  apply real_minkowski_pair_radius hM _ _ hv hR
  · simpa only [conductorRealMinkowski_apply,
      conductorOrder_real_embedding_product K f hK hf σ e] using hx
  · simpa only [conductorRealMinkowski_apply,
      conductorOrder_real_embedding_product K f hK hf σ e] using hy

/-- The paper's close-pair isolation conclusion for literal positive conductor
orders, with their actual integer algebra norm and actual real coordinates. -/
theorem conductorRealMinkowski_finite_close_pairs (hK : Module.finrank ℚ K = 2)
    (hf : 0 < f) (σ : K →ₐ[ℚ] ℝ) (e : Fin 2 ≃ (K ≃ₐ[ℚ] K))
    {M R : ℝ} (hM : 0 ≤ M) :
    {p : conductorOrder K f × conductorOrder K f | p.1 ≠ p.2 ∧
      |(Algebra.norm ℤ p.1 : ℝ)| ≤ M ∧ |(Algebra.norm ℤ p.2 : ℝ)| ≤ M ∧
      ‖conductorRealMinkowski K f σ e p.2 - conductorRealMinkowski K f σ e p.1‖ ≤ R}.Finite := by
  have h := finite_real_minkowski_close_pairs (conductorRealMinkowski K f σ e)
    (conductorRealMinkowski_finite_balls K f hK σ e)
    (by simpa only [conductorRealMinkowski_apply] using
      conductorOrder_real_difference_integral K f hK hf σ e) (R := R) hM
  simpa only [conductorRealMinkowski_apply,
    conductorOrder_real_embedding_product K f hK hf σ e] using h

/-- Close-pair isolation persists under every invertible planar linear change
of the actual real Minkowski coordinates. -/
theorem conductorRealPlanar_finite_close_pairs (hK : Module.finrank ℚ K = 2)
    (hf : 0 < f) (σ : K →ₐ[ℚ] ℝ) (e : Fin 2 ≃ (K ≃ₐ[ℚ] K))
    (A : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    {M R : ℝ} (hM : 0 ≤ M) :
    {p : conductorOrder K f × conductorOrder K f | p.1 ≠ p.2 ∧
      |(Algebra.norm ℤ p.1 : ℝ)| ≤ M ∧ |(Algebra.norm ℤ p.2 : ℝ)| ≤ M ∧
      ‖A (conductorRealMinkowski K f σ e p.2) -
        A (conductorRealMinkowski K f σ e p.1)‖ ≤ R}.Finite := by
  apply (conductorRealMinkowski_finite_close_pairs K f hK hf σ e
    (R := ‖A.symm.toContinuousLinearMap‖ * R) hM).subset
  rintro ⟨x, y⟩ ⟨hne, hx, hy, hR⟩
  refine ⟨hne, hx, hy, ?_⟩
  calc
    ‖conductorRealMinkowski K f σ e y - conductorRealMinkowski K f σ e x‖ =
        ‖A.symm (A (conductorRealMinkowski K f σ e y) -
          A (conductorRealMinkowski K f σ e x))‖ := by simp
    _ ≤ ‖A.symm.toContinuousLinearMap‖ *
        ‖A (conductorRealMinkowski K f σ e y) - A (conductorRealMinkowski K f σ e x)‖ :=
      A.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ ‖A.symm.toContinuousLinearMap‖ * R :=
      mul_le_mul_of_nonneg_left hR (norm_nonneg _)

end Entry002
