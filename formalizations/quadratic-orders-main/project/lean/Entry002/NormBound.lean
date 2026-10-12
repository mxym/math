import Entry002.Orders
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The actual homogeneous quadratic norm bound in arbitrary full planar
coordinates, equation `normbound` in entry 002 version 3. -/

namespace Entry002

open Module
open scoped BigOperators

section LinearExtensions

variable {O : Type*} [CommRing O]

/-- Extend an embedding of the integral order along its actual basis. -/
noncomputable def embeddingCoefficientLinearMap (b : Basis (Fin 2) ℤ O)
    (φ : O →+* ℂ) : CoeffSpace →ₗ[ℝ] ℂ where
  toFun z := ∑ i : Fin 2, z i • φ (b i)
  map_add' z w := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c z := by simp [mul_assoc]

theorem embeddingCoefficientLinearMap_apply (b : Basis (Fin 2) ℤ O)
    (φ : O →+* ℂ) (x : O) :
    embeddingCoefficientLinearMap b φ (fun i => (b.repr x i : ℝ)) = φ x := by
  change (∑ i : Fin 2, (b.repr x i : ℝ) • φ (b i)) = φ x
  calc
    _ = ∑ i : Fin 2, φ ((b.repr x i) • b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Int.cast_smul_eq_zsmul]
    _ = φ (∑ i : Fin 2, (b.repr x i) • b i) := (map_sum φ _ _).symm
    _ = φ x := congrArg φ (b.sum_repr x)

/-- The embedding functional in the user-selected full planar coordinates. -/
noncomputable def embeddingPlanarFunctional (b : Basis (Fin 2) ℤ O)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (φ : O →+* ℂ) : Plane →L[ℝ] ℂ :=
  (embeddingCoefficientLinearMap b φ).toContinuousLinearMap.comp
    e.symm.toContinuousLinearEquiv.toContinuousLinearMap

theorem embeddingPlanarFunctional_apply (b : Basis (Fin 2) ℤ O)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (φ : O →+* ℂ) (x : O) :
    embeddingPlanarFunctional b e φ (planarEmbedding b e x) = φ x := by
  change embeddingCoefficientLinearMap b φ
    (e.symm (e (fun i => (b.repr x i : ℝ)))) = φ x
  rw [e.symm_apply_apply]
  exact embeddingCoefficientLinearMap_apply b φ x

theorem norm_embedding_le_planar (b : Basis (Fin 2) ℤ O)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (φ : O →+* ℂ) (x : O) :
    ‖φ x‖ ≤ ‖embeddingPlanarFunctional b e φ‖ * ‖planarEmbedding b e x‖ := by
  rw [← embeddingPlanarFunctional_apply b e φ x]
  exact (embeddingPlanarFunctional b e φ).le_opNorm _

end LinearExtensions

variable (K : Type*) [Field K] [NumberField K] (f : ℕ)

/-- The field norm of every actual quadratic-order element satisfies the
manuscript's quadratic bound in every full planar coefficient embedding. -/
theorem exists_order_norm_bound (hK : Module.finrank ℚ K = 2) (hf : 0 < f)
    (b : Basis (Fin 2) ℤ (conductorOrder K f))
    (e : CoeffSpace ≃ₗ[ℝ] Plane) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : conductorOrder K f,
      |(Algebra.norm ℤ x : ℝ)| ≤ C * ‖planarEmbedding b e x‖ ^ 2 := by
  classical
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  let σ : K →ₐ[ℚ] ℂ := IsAlgClosed.lift
  let τ := quadraticConjugates K hK
  let φ₀ : conductorOrder K f →+* ℂ :=
    σ.toRingHom.comp ((τ 0).toRingHom.comp (conductorOrder K f).subtype)
  let φ₁ : conductorOrder K f →+* ℂ :=
    σ.toRingHom.comp ((τ 1).toRingHom.comp (conductorOrder K f).subtype)
  let L₀ := embeddingPlanarFunctional b e φ₀
  let L₁ := embeddingPlanarFunctional b e φ₁
  refine ⟨max 1 (‖L₀‖ * ‖L₁‖), le_max_left _ _, ?_⟩
  intro x
  have hn : |(Algebra.norm ℤ x : ℝ)| = ‖φ₀ x‖ * ‖φ₁ x‖ := by
    have hprod := field_norm_eq_product_embeddings σ τ (x : K)
    rw [conductorOrder_norm_eq_field_norm K f hf x] at hprod
    have hnorm := congrArg norm hprod
    simpa [φ₀, φ₁, norm_mul, Int.norm_eq_abs] using hnorm
  rw [hn]
  have h₀ : ‖φ₀ x‖ ≤ ‖L₀‖ * ‖planarEmbedding b e x‖ := by
    rw [← embeddingPlanarFunctional_apply b e φ₀ x]
    exact L₀.le_opNorm _
  have h₁ : ‖φ₁ x‖ ≤ ‖L₁‖ * ‖planarEmbedding b e x‖ := by
    rw [← embeddingPlanarFunctional_apply b e φ₁ x]
    exact L₁.le_opNorm _
  calc
    ‖φ₀ x‖ * ‖φ₁ x‖ ≤ (‖L₀‖ * ‖planarEmbedding b e x‖) *
        (‖L₁‖ * ‖planarEmbedding b e x‖) :=
      mul_le_mul h₀ h₁ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (‖L₀‖ * ‖L₁‖) * ‖planarEmbedding b e x‖ ^ 2 := by ring
    _ ≤ max 1 (‖L₀‖ * ‖L₁‖) * ‖planarEmbedding b e x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)

theorem exists_order_natAbs_norm_bound (hK : Module.finrank ℚ K = 2) (hf : 0 < f)
    (b : Basis (Fin 2) ℤ (conductorOrder K f))
    (e : CoeffSpace ≃ₗ[ℝ] Plane) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : conductorOrder K f,
      ((Algebra.norm ℤ x).natAbs : ℝ) ≤ C * ‖planarEmbedding b e x‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_order_norm_bound K f hK hf b e
  refine ⟨C, hC, ?_⟩
  intro x
  simpa only [Nat.cast_natAbs, Int.cast_abs] using hbound x

/-- The collision constant for actual conductor orders, with the geometric
norm upper bound now proved rather than supplied. -/
theorem exists_order_collision_bound (hK : Module.finrank ℚ K = 2) (hf : 0 < f)
    (b : Basis (Fin 2) ℤ (conductorOrder K f))
    (e : CoeffSpace ≃ₗ[ℝ] Plane) :
    ∃ c : ℝ, 0 < c ∧ ∀ (p : ℕ) (x : conductorOrder K f), x ≠ 0 →
      p ∣ (Algebra.norm ℤ x).natAbs →
      c * Real.sqrt (p : ℝ) ≤ ‖planarEmbedding b e x‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_order_natAbs_norm_bound K f hK hf b e
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  refine ⟨(Real.sqrt C)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hCpos), ?_⟩
  intro p x hx hp
  simpa only [div_eq_mul_inv, mul_comm] using
    norm_collision_lower_bound hx hp hCpos (norm_nonneg _) (hbound x)

/-- The full distinct-eligible-prime norm estimate in arbitrary full planar
coordinates. This requires neither a chosen factorization of the order nor a
primitive-vector surrogate. -/
theorem exists_order_prime_product_bound (hK : Module.finrank ℚ K = 2) (hf : 0 < f)
    (b : Basis (Fin 2) ℤ (conductorOrder K f))
    (e : CoeffSpace ≃ₗ[ℝ] Plane) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (S : Finset ℕ) (x : conductorOrder K f), x ≠ 0 →
      (∀ p ∈ S, Nat.Prime p) → (∀ p ∈ S, p ∣ (Algebra.norm ℤ x).natAbs) →
      S.prod (fun p => (p : ℝ)) ≤ C * ‖planarEmbedding b e x‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_order_natAbs_norm_bound K f hK hf b e
  exact ⟨C, hC, fun S x hx hprime hdiv =>
    norm_prime_product_bound S hx hprime hdiv (hbound x)⟩

end Entry002
