import Entry002.Isolation
import Entry002.NormBound
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

/-! Bounded-norm isolation for all actual quadratic conductor orders and every
full planar coefficient embedding, without splitting real and imaginary cases. -/

namespace Entry002

open Module

theorem norm_div_le_of_one_le {𝕂 : Type*} [NormedField 𝕂]
    {u v : 𝕂} {M : ℝ} (hM : 0 ≤ M) (hu : ‖u‖ ≤ M) (hv : 1 ≤ ‖v‖) :
    ‖u / v‖ ≤ M := by
  rw [norm_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖v‖)).mpr
  nlinarith

/-- The conjugate ratio estimate holds over any normed field, in particular
over the complex numbers for both real and imaginary quadratic fields. -/
theorem normed_conjugate_ratio_bound {𝕂 : Type*} [NormedField 𝕂]
    {x₀ x₁ y₀ y₁ : 𝕂} {M : ℝ} (hM : 0 ≤ M)
    (hx : ‖x₀ * x₁‖ ≤ M) (hy : ‖y₀ * y₁‖ ≤ M)
    (hv : 1 ≤ ‖(y₀ - x₀) * (y₁ - x₁)‖) :
    ‖x₀ / (y₀ - x₀)‖ ≤ 2 * M + 2 ∧ ‖x₁ / (y₁ - x₁)‖ ≤ 2 * M + 2 := by
  let v₀ := y₀ - x₀
  let v₁ := y₁ - x₁
  have hvn : v₀ * v₁ ≠ 0 := by
    intro he
    have hz : ‖(y₀ - x₀) * (y₁ - x₁)‖ = 0 := by simpa [v₀, v₁] using congrArg norm he
    linarith
  have hv₀ : v₀ ≠ 0 := (mul_ne_zero_iff.mp hvn).1
  have hv₁ : v₁ ≠ 0 := (mul_ne_zero_iff.mp hvn).2
  let t₀ := x₀ / v₀
  let t₁ := x₁ / v₁
  have hp : t₀ * t₁ = (x₀ * x₁) / (v₀ * v₁) := div_mul_div_comm _ _ _ _
  have hpbound : ‖t₀ * t₁‖ ≤ M := by
    rw [hp]
    exact norm_div_le_of_one_le hM hx hv
  have ht : t₀ + t₁ = (y₀ * y₁ - x₀ * x₁) / (v₀ * v₁) - 1 := by
    dsimp [t₀, t₁, v₀, v₁] at *
    field_simp [hv₀, hv₁]
    ring
  have hd : ‖y₀ * y₁ - x₀ * x₁‖ ≤ 2 * M := by
    exact (norm_sub_le _ _).trans (by linarith)
  have htbound : ‖t₀ + t₁‖ ≤ 2 * M + 1 := by
    rw [ht]
    calc
      _ ≤ ‖(y₀ * y₁ - x₀ * x₁) / (v₀ * v₁)‖ + ‖(1 : 𝕂)‖ := norm_sub_le _ _
      _ ≤ 2 * M + 1 := by
        rw [norm_one]
        have hb := norm_div_le_of_one_le (by linarith : 0 ≤ 2 * M) hd hv
        linarith
  exact ⟨quadratic_root_bound hM htbound hpbound (by ring),
    quadratic_root_bound hM htbound hpbound (by ring)⟩

theorem normed_conjugate_endpoint_bound {𝕂 : Type*} [NormedField 𝕂]
    {x₀ x₁ y₀ y₁ : 𝕂} {M : ℝ} (hM : 0 ≤ M)
    (hx : ‖x₀ * x₁‖ ≤ M) (hy : ‖y₀ * y₁‖ ≤ M)
    (hv : 1 ≤ ‖(y₀ - x₀) * (y₁ - x₁)‖) :
    ‖x₀‖ ≤ (2 * M + 2) * ‖y₀ - x₀‖ ∧
      ‖x₁‖ ≤ (2 * M + 2) * ‖y₁ - x₁‖ := by
  obtain ⟨h₀, h₁⟩ := normed_conjugate_ratio_bound hM hx hy hv
  have hvn : (y₀ - x₀) * (y₁ - x₁) ≠ 0 := by
    intro he
    rw [he, norm_zero] at hv
    linarith
  have hv₀ := (mul_ne_zero_iff.mp hvn).1
  have hv₁ := (mul_ne_zero_iff.mp hvn).2
  constructor
  · calc
      ‖x₀‖ = ‖x₀ / (y₀ - x₀)‖ * ‖y₀ - x₀‖ := by
        rw [← norm_mul, div_mul_cancel₀ _ hv₀]
      _ ≤ _ := mul_le_mul_of_nonneg_right h₀ (norm_nonneg _)
  · calc
      ‖x₁‖ = ‖x₁ / (y₁ - x₁)‖ * ‖y₁ - x₁‖ := by
        rw [← norm_mul, div_mul_cancel₀ _ hv₁]
      _ ≤ _ := mul_le_mul_of_nonneg_right h₁ (norm_nonneg _)

variable (K : Type*) [Field K] [NumberField K] (f : ℕ)

theorem complex_conjugates_cover_embeddings (hK : Module.finrank ℚ K = 2)
    (σ : K →ₐ[ℚ] ℂ) (τ : Fin 2 ≃ (K ≃ₐ[ℚ] K)) :
    Function.Surjective (fun i : Fin 2 => σ.toRingHom.comp (τ i).toRingHom) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr ?_ |>.2
  constructor
  · intro i j hij
    apply τ.injective
    apply AlgEquiv.ext
    intro x
    exact σ.injective (congrArg (fun φ : K →+* ℂ => φ x) hij)
  · simp [NumberField.Embeddings.card K ℂ, hK]

theorem conductor_complex_product_norm (hK : Module.finrank ℚ K = 2)
    (hf : 0 < f) (σ : K →ₐ[ℚ] ℂ) (τ : Fin 2 ≃ (K ≃ₐ[ℚ] K))
    (x : conductorOrder K f) :
    ‖σ (τ 0 (x : K)) * σ (τ 1 (x : K))‖ = |(Algebra.norm ℤ x : ℝ)| := by
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  have hp := field_norm_eq_product_embeddings σ τ (x : K)
  rw [conductorOrder_norm_eq_field_norm K f hf x] at hp
  simpa [Int.norm_eq_abs] using (congrArg norm hp).symm

/-- Isolation for every actual quadratic conductor order in every full planar
coefficient embedding. Norm-bounded elements may be infinite; their distinct
close ordered pairs are finite. All arithmetic and lattice inputs are proved. -/
theorem conductor_planar_finite_close_pairs (hK : Module.finrank ℚ K = 2)
    (hf : 0 < f) (b : Basis (Fin 2) ℤ (conductorOrder K f))
    (e : CoeffSpace ≃ₗ[ℝ] Plane) {M R : ℝ} (hM : 0 ≤ M) :
    {p : conductorOrder K f × conductorOrder K f | p.1 ≠ p.2 ∧
      |(Algebra.norm ℤ p.1 : ℝ)| ≤ M ∧ |(Algebra.norm ℤ p.2 : ℝ)| ≤ M ∧
      ‖planarEmbedding b e p.2 - planarEmbedding b e p.1‖ ≤ R}.Finite := by
  classical
  let σ : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let τ := quadraticConjugates K hK
  let φ : Fin 2 → (conductorOrder K f →+* ℂ) := fun i =>
    σ.toRingHom.comp ((τ i).toRingHom.comp (conductorOrder K f).subtype)
  let L : Fin 2 → (Plane →L[ℝ] ℂ) := fun i => embeddingPlanarFunctional b e (φ i)
  let B := max ‖L 0‖ ‖L 1‖
  let T := (2 * M + 2) * (B * R)
  have hpoint : ∀ x y : conductorOrder K f, x ≠ y →
      |(Algebra.norm ℤ x : ℝ)| ≤ M → |(Algebra.norm ℤ y : ℝ)| ≤ M →
      ‖planarEmbedding b e y - planarEmbedding b e x‖ ≤ R →
      ∀ ψ : K →+* ℂ, ‖ψ (x : K)‖ ≤ T := by
    intro x y hne hx hy hd
    have hR : 0 ≤ R := (norm_nonneg _).trans hd
    have hprod : ∀ z : conductorOrder K f,
        ‖φ 0 z * φ 1 z‖ = |(Algebra.norm ℤ z : ℝ)| :=
      conductor_complex_product_norm K f hK hf σ τ
    have hx' : ‖φ 0 x * φ 1 x‖ ≤ M := by rw [hprod]; exact hx
    have hy' : ‖φ 0 y * φ 1 y‖ ≤ M := by rw [hprod]; exact hy
    have hv : 1 ≤ ‖(φ 0 y - φ 0 x) * (φ 1 y - φ 1 x)‖ := by
      have hp := hprod (y - x)
      simp only [map_sub] at hp
      rw [hp]
      apply one_le_abs_of_nonzero_integer ⟨Algebra.norm ℤ (y - x), rfl⟩
      exact_mod_cast (order_norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne.symm))
    obtain ⟨h₀, h₁⟩ := normed_conjugate_endpoint_bound hM hx' hy' hv
    have hi : ∀ i : Fin 2, ‖φ i y - φ i x‖ ≤ B * R := by
      intro i
      have hLi : ‖L i‖ ≤ B := by
        fin_cases i
        · exact le_max_left _ _
        · exact le_max_right _ _
      calc
        ‖φ i y - φ i x‖ = ‖L i (planarEmbedding b e y - planarEmbedding b e x)‖ := by
          rw [map_sub, embeddingPlanarFunctional_apply, embeddingPlanarFunctional_apply]
        _ ≤ ‖L i‖ * ‖planarEmbedding b e y - planarEmbedding b e x‖ := (L i).le_opNorm _
        _ ≤ ‖L i‖ * R := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
        _ ≤ B * R := mul_le_mul_of_nonneg_right hLi hR
    have hz : ∀ i : Fin 2, ‖φ i x‖ ≤ T := by
      intro i
      have hxi : ‖φ i x‖ ≤ (2 * M + 2) * ‖φ i y - φ i x‖ := by
        fin_cases i
        · exact h₀
        · exact h₁
      exact hxi.trans (mul_le_mul_of_nonneg_left (hi i) (by linarith))
    intro ψ
    obtain ⟨i, rfl⟩ := complex_conjugates_cover_embeddings K hK σ τ ψ
    exact hz i
  have hs := NumberField.Embeddings.finite_of_norm_le K ℂ T
  have hp : {x : conductorOrder K f | IsIntegral ℤ (x : K) ∧
      ∀ ψ : K →+* ℂ, ‖ψ (x : K)‖ ≤ T}.Finite :=
    hs.preimage (fun x y _ _ h => Subtype.ext h)
  apply (hp.prod hp).subset
  rintro ⟨x, y⟩ ⟨hne, hx, hy, hd⟩
  refine ⟨⟨conductorOrder_isIntegral K f x, hpoint x y hne hx hy hd⟩,
    ⟨conductorOrder_isIntegral K f y, hpoint y x hne.symm hy hx ?_⟩⟩
  simpa only [norm_sub_rev] using hd

end Entry002
