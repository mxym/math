import Entry005.ZonotopeDeterminant
import Entry005.ZonotopeInjectionCombinatorics

noncomputable section
open MeasureTheory Module
open scoped BigOperators RealInnerProductSpace

namespace Entry005

universe u

def zonotopeDeterminantSum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {d m : ℕ} (b : OrthonormalBasis (Fin d) ℝ E) (g : Fin m → E) : ℝ :=
  ∑ σ : Fin d ↪ Fin m, |b.toBasis.det (fun i => g (σ i))|

def zonotopeCoefficient (d : ℕ) : ℝ := 2 ^ d / (d.factorial : ℝ)

theorem zonotope_coefficient_mul_succ (d : ℕ) :
    zonotopeCoefficient (d + 1) * (d + 1 : ℝ) = 2 * zonotopeCoefficient d := by
  have hf : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero d)
  have hd : (d + 1 : ℝ) ≠ 0 := by positivity
  simp only [zonotopeCoefficient, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, pow_succ]
  field_simp

section FormulaBases

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem finite_zonotope_volume_zero_dimensional {m : ℕ}
    (b : OrthonormalBasis (Fin 0) ℝ E) (g : Fin m → E) :
    (volume (finiteZonotope g)).toReal =
      zonotopeCoefficient 0 * zonotopeDeterminantSum b g := by
  rw [finite_zonotope_volume_isometry g b.repr, finite_zonotope_euclidean_zero_volume]
  simp [zonotopeCoefficient, zonotopeDeterminantSum, Basis.det_isEmpty]

theorem finite_zonotope_volume_no_generators {d : ℕ}
    (b : OrthonormalBasis (Fin (d + 1)) ℝ E) (g : Fin 0 → E) :
    (volume (finiteZonotope g)).toReal =
      zonotopeCoefficient (d + 1) * zonotopeDeterminantSum b g := by
  have hd : finrank ℝ E = d + 1 := by
    simpa using finrank_eq_card_basis b.toBasis
  have hcard : Fintype.card (Fin 0) < finrank ℝ E := by simp [hd]
  have : IsEmpty (Fin (d + 1) ↪ Fin 0) := ⟨fun f => Fin.elim0 (f 0)⟩
  rw [finite_zonotope_volume_zero_of_card_lt g hcard]
  simp [zonotopeDeterminantSum]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem zonotope_determinant_sum_height {d m : ℕ}
    (b : OrthonormalBasis (Fin (d + 1)) ℝ E) (v : E)
    (bH : OrthonormalBasis (Fin d) ℝ (ℝ ∙ v)ᗮ) (g : Fin m → E) :
    (∑ τ : Fin d ↪ Fin m, |b.toBasis.det (Fin.cons v (fun i => g (τ i)))|) =
      ‖v‖ * zonotopeDeterminantSum bH
        (fun i => (ℝ ∙ v)ᗮ.orthogonalProjectionOnto (g i)) := by
  have : Fact (finrank ℝ E = d + 1) := ⟨by simpa using finrank_eq_card_basis b.toBasis⟩
  simp_rw [orthonormal_determinant_height b v bH]
  simp only [zonotopeDeterminantSum, Finset.mul_sum]

end FormulaBases

/-- The actual finite Euclidean zonotope volume formula. The injection sum
counts each unordered generator selection `d!` times; no geometric volume
formula appears among the hypotheses. -/
theorem finite_zonotope_volume_determinant_sum
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {d m : ℕ}
    (b : OrthonormalBasis (Fin d) ℝ E) (g : Fin m → E) :
    (volume (finiteZonotope g)).toReal = zonotopeCoefficient d * zonotopeDeterminantSum b g := by
  induction d generalizing E m with
  | zero => exact finite_zonotope_volume_zero_dimensional b g
  | succ d ihd =>
    induction m with
    | zero => exact finite_zonotope_volume_no_generators b g
    | succ m ihm =>
      let v := g 0
      let q : Fin m → E := fun i => g i.succ
      have hg : g = Fin.cons v q := by
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      have : Fact (finrank ℝ E = d + 1) := ⟨by simpa using finrank_eq_card_basis b.toBasis⟩
      have hold := ihm q
      have hsum := alternating_injection_sum_cons d m b.toBasis.det v q
      change zonotopeDeterminantSum b (Fin.cons v q) =
        zonotopeDeterminantSum b q + (d + 1 : ℝ) * _ at hsum
      rw [hg, finite_zonotope_volume_cons_projected, hold]
      by_cases hv : v = 0
      · rw [hsum]
        have hz : (∑ τ : Fin d ↪ Fin m,
            |b.toBasis.det (Fin.cons v (fun i => q (τ i)))|) = 0 := by
          apply Finset.sum_eq_zero
          intro τ _
          rw [hv]
          simp [← b.toBasis.det.map_update_zero (Fin.cons (0 : E) (fun i => q (τ i))) 0]
        rw [hz]
        simp [hv]
      · let bH := OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) d hv
        have hlow := ihd bH (fun i => (ℝ ∙ v)ᗮ.orthogonalProjectionOnto (q i))
        rw [hlow, hsum, zonotope_determinant_sum_height b v bH q]
        rw [mul_add]
        congr 1
        have hcoef := congrArg (fun c : ℝ => c * ‖v‖ *
          zonotopeDeterminantSum bH (fun i => (ℝ ∙ v)ᗮ.orthogonalProjectionOnto (q i)))
          (zonotope_coefficient_mul_succ d)
        nlinarith only [hcoef]

/-- The formula with literal Euclidean coordinate matrix determinants. -/
theorem finite_zonotope_volume_matrix {d m : ℕ} (g : Fin m → EuclideanSpace ℝ (Fin d)) :
    (volume (finiteZonotope g)).toReal =
      (2 ^ d / (d.factorial : ℝ)) *
        ∑ σ : Fin d ↪ Fin m, |Matrix.det (fun i j => g (σ j) i)| := by
  simpa only [zonotopeCoefficient, zonotopeDeterminantSum,
    orthonormal_basis_det_coordinates, EuclideanSpace.basisFun_repr] using
    finite_zonotope_volume_determinant_sum (EuclideanSpace.basisFun (Fin d) ℝ) g

end Entry005
