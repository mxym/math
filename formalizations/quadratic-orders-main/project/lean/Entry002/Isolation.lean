import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# The explicit bounded-norm isolation radius

This file formalizes the scalar root bound and the real Minkowski-coordinate
part of Lemma 9.2 (`lem:radius`) of Entry 002, version 3. The product of the two
coordinates is the genuine field norm in real Minkowski coordinates. The
arithmetic input is stated explicitly as a lower bound on the absolute product
of a nonzero difference; a separate lemma derives this bound from integrality.
-/

namespace Entry002

/-- The quadratic root estimate used in the bounded-norm isolation argument.
It works for real and complex roots, and more generally for any normed field. -/
theorem quadratic_root_bound {𝕂 : Type*} [NormedField 𝕂]
    {a b z : 𝕂} {M : ℝ} (hM : 0 ≤ M)
    (ha : ‖a‖ ≤ 2 * M + 1) (hb : ‖b‖ ≤ M)
    (hz : z ^ 2 - a * z + b = 0) : ‖z‖ ≤ 2 * M + 2 := by
  have heq : z ^ 2 = a * z - b := by linear_combination hz
  have hi : ‖z‖ ^ 2 ≤ (2 * M + 1) * ‖z‖ + M := by
    calc
      ‖z‖ ^ 2 = ‖z ^ 2‖ := (norm_pow z 2).symm
      _ = ‖a * z - b‖ := congrArg norm heq
      _ ≤ ‖a * z‖ + ‖b‖ := norm_sub_le _ _
      _ = ‖a‖ * ‖z‖ + ‖b‖ := by rw [norm_mul]
      _ ≤ (2 * M + 1) * ‖z‖ + M := by gcongr
  by_contra hn
  have hr : 2 * M + 2 < ‖z‖ := lt_of_not_ge hn
  have hs : (2 * M + 2) * ‖z‖ ≤ ‖z‖ ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hr.le) (norm_nonneg z)]
  nlinarith

/-- A nonzero integer field norm has absolute value at least one. -/
theorem one_le_abs_of_nonzero_integer {r : ℝ}
    (hr : ∃ n : ℤ, r = n) (hn : r ≠ 0) : 1 ≤ |r| := by
  obtain ⟨n, rfl⟩ := hr
  have hn' : n ≠ 0 := by exact_mod_cast hn
  exact_mod_cast Int.one_le_abs hn'

/-- Bounding a numerator by `M` and an absolute denominator by one bounds the
absolute quotient by `M`. -/
theorem abs_div_le_of_one_le {u v M : ℝ} (hM : 0 ≤ M)
    (hu : |u| ≤ M) (hv : 1 ≤ |v|) : |u / v| ≤ M := by
  rw [abs_div]
  apply (div_le_iff₀ (by linarith : 0 < |v|)).mpr
  nlinarith

/-- The conjugate coordinates of `x / (y-x)` satisfy the root estimate. -/
theorem real_minkowski_ratio_bound {x₁ x₂ y₁ y₂ M : ℝ}
    (hM : 0 ≤ M) (hx : |x₁ * x₂| ≤ M) (hy : |y₁ * y₂| ≤ M)
    (hv : 1 ≤ |(y₁ - x₁) * (y₂ - x₂)|) :
    |x₁ / (y₁ - x₁)| ≤ 2 * M + 2 ∧
      |x₂ / (y₂ - x₂)| ≤ 2 * M + 2 := by
  let v₁ := y₁ - x₁
  let v₂ := y₂ - x₂
  have hvn : v₁ * v₂ ≠ 0 := by
    intro he
    have : |(y₁ - x₁) * (y₂ - x₂)| = 0 := by simpa [v₁, v₂] using congrArg abs he
    linarith
  have hv₁ : v₁ ≠ 0 := (mul_ne_zero_iff.mp hvn).1
  have hv₂ : v₂ ≠ 0 := (mul_ne_zero_iff.mp hvn).2
  let t₁ := x₁ / v₁
  let t₂ := x₂ / v₂
  have hp : t₁ * t₂ = (x₁ * x₂) / (v₁ * v₂) := by
    dsimp [t₁, t₂]
    exact div_mul_div_comm _ _ _ _
  have hpbound : |t₁ * t₂| ≤ M := by
    rw [hp]
    exact abs_div_le_of_one_le hM hx hv
  have htrace : t₁ + t₂ = (y₁ * y₂ - x₁ * x₂) / (v₁ * v₂) - 1 := by
    dsimp [t₁, t₂, v₁, v₂] at *
    field_simp [hv₁, hv₂]
    ring
  have hd : |y₁ * y₂ - x₁ * x₂| ≤ 2 * M := by
    calc
      _ ≤ |y₁ * y₂| + |x₁ * x₂| := abs_sub _ _
      _ ≤ 2 * M := by linarith
  have htbound : |t₁ + t₂| ≤ 2 * M + 1 := by
    rw [htrace]
    calc
      _ ≤ |(y₁ * y₂ - x₁ * x₂) / (v₁ * v₂)| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ 2 * M + 1 := by
        have := abs_div_le_of_one_le (by linarith : 0 ≤ 2 * M) hd hv
        simpa using add_le_add_right this 1
  constructor
  · simpa only [Real.norm_eq_abs] using
      quadratic_root_bound hM htbound hpbound (by ring : t₁ ^ 2 - (t₁ + t₂) * t₁ + t₁ * t₂ = 0)
  · simpa only [Real.norm_eq_abs] using
      quadratic_root_bound hM htbound hpbound (by ring : t₂ ^ 2 - (t₁ + t₂) * t₂ + t₁ * t₂ = 0)

/-- The Euclidean norm in real Minkowski coordinates obeys the explicit
isolation radius. No definiteness assumption is made on the field norm. -/
theorem real_minkowski_endpoint_bound {x y : EuclideanSpace ℝ (Fin 2)} {M : ℝ}
    (hM : 0 ≤ M) (hx : |x 0 * x 1| ≤ M) (hy : |y 0 * y 1| ≤ M)
    (hv : 1 ≤ |(y 0 - x 0) * (y 1 - x 1)|) :
    ‖x‖ ≤ (2 * M + 2) * ‖y - x‖ := by
  let C := 2 * M + 2
  have hC : 0 ≤ C := by dsimp [C]; linarith
  obtain ⟨h₀, h₁⟩ := real_minkowski_ratio_bound hM hx hy hv
  have hvn : (y 0 - x 0) * (y 1 - x 1) ≠ 0 := by
    intro he
    rw [he, abs_zero] at hv
    linarith
  have hv₀ : y 0 - x 0 ≠ 0 := (mul_ne_zero_iff.mp hvn).1
  have hv₁ : y 1 - x 1 ≠ 0 := (mul_ne_zero_iff.mp hvn).2
  have hc₀ : |x 0| ≤ C * |y 0 - x 0| := by
    calc
      |x 0| = |x 0 / (y 0 - x 0)| * |y 0 - x 0| := by
        rw [← abs_mul, div_mul_cancel₀ _ hv₀]
      _ ≤ C * |y 0 - x 0| := mul_le_mul_of_nonneg_right h₀ (abs_nonneg _)
  have hc₁ : |x 1| ≤ C * |y 1 - x 1| := by
    calc
      |x 1| = |x 1 / (y 1 - x 1)| * |y 1 - x 1| := by
        rw [← abs_mul, div_mul_cancel₀ _ hv₁]
      _ ≤ C * |y 1 - x 1| := mul_le_mul_of_nonneg_right h₁ (abs_nonneg _)
  have hs₀ : (x 0) ^ 2 ≤ C ^ 2 * (y 0 - x 0) ^ 2 := by
    have := (sq_le_sq₀ (abs_nonneg (x 0)) (mul_nonneg hC (abs_nonneg _))).mpr hc₀
    simpa [mul_pow] using this
  have hs₁ : (x 1) ^ 2 ≤ C ^ 2 * (y 1 - x 1) ^ 2 := by
    have := (sq_le_sq₀ (abs_nonneg (x 1)) (mul_nonneg hC (abs_nonneg _))).mpr hc₁
    simpa [mul_pow] using this
  have hn : ‖x‖ ^ 2 ≤ (C * ‖y - x‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    simp only [Fin.sum_univ_two, PiLp.sub_apply]
    nlinarith [hs₀, hs₁]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hC (norm_nonneg _))).mp hn

/-- Both endpoints of a close bounded-norm pair lie in the claimed Euclidean
ball. Integrality of the nonzero difference norm is the sole arithmetic input. -/
theorem real_minkowski_pair_radius {x y : EuclideanSpace ℝ (Fin 2)} {M R : ℝ}
    (hM : 0 ≤ M) (hx : |x 0 * x 1| ≤ M) (hy : |y 0 * y 1| ≤ M)
    (hv : 1 ≤ |(y 0 - x 0) * (y 1 - x 1)|) (hR : ‖y - x‖ ≤ R) :
    ‖x‖ ≤ (2 * M + 2) * R ∧ ‖y‖ ≤ (2 * M + 2) * R := by
  have hC : 0 ≤ 2 * M + 2 := by linarith
  constructor
  · exact (real_minkowski_endpoint_bound hM hx hy hv).trans
      (mul_le_mul_of_nonneg_left hR hC)
  · have hv' : 1 ≤ |(x 0 - y 0) * (x 1 - y 1)| := by
      convert hv using 1
      congr 1
      ring
    have hr' : ‖x - y‖ ≤ R := by simpa only [norm_sub_rev] using hR
    exact (real_minkowski_endpoint_bound hM hy hx hv').trans
      (mul_le_mul_of_nonneg_left hr' hC)

/-- Changing from Minkowski coordinates to any fixed planar embedding costs
the product of the operator norms of the change of coordinates and its inverse,
exactly as in the last assertion of the explicit-radius lemma. -/
theorem real_planar_pair_radius
    (e : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    {x y : EuclideanSpace ℝ (Fin 2)} {M R : ℝ}
    (hM : 0 ≤ M) (hx : |x 0 * x 1| ≤ M) (hy : |y 0 * y 1| ≤ M)
    (hv : 1 ≤ |(y 0 - x 0) * (y 1 - x 1)|) (hR : ‖e (y - x)‖ ≤ R) :
    ‖e x‖ ≤ (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖) *
        (2 * M + 2) * R ∧
      ‖e y‖ ≤ (‖e.toContinuousLinearMap‖ * ‖e.symm.toContinuousLinearMap‖) *
        (2 * M + 2) * R := by
  have hd : ‖y - x‖ ≤ ‖e.symm.toContinuousLinearMap‖ * R := by
    calc
      ‖y - x‖ = ‖e.symm (e (y - x))‖ := by simp
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * ‖e (y - x)‖ :=
        e.symm.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖e.symm.toContinuousLinearMap‖ * R :=
        mul_le_mul_of_nonneg_left hR (norm_nonneg _)
  obtain ⟨h₁, h₂⟩ := real_minkowski_pair_radius hM hx hy hv hd
  constructor
  · calc
      ‖e x‖ ≤ ‖e.toContinuousLinearMap‖ * ‖x‖ := e.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖e.toContinuousLinearMap‖ * ((2 * M + 2) *
          (‖e.symm.toContinuousLinearMap‖ * R)) :=
        mul_le_mul_of_nonneg_left h₁ (norm_nonneg _)
      _ = _ := by ring
  · calc
      ‖e y‖ ≤ ‖e.toContinuousLinearMap‖ * ‖y‖ := e.toContinuousLinearMap.le_opNorm _
      _ ≤ ‖e.toContinuousLinearMap‖ * ((2 * M + 2) *
          (‖e.symm.toContinuousLinearMap‖ * R)) :=
        mul_le_mul_of_nonneg_left h₂ (norm_nonneg _)
      _ = _ := by ring

/-- The imaginary Minkowski case, expressed with the actual complex absolute
value. Here the field norm is the square of that absolute value. -/
theorem imaginary_minkowski_pair_radius {x y : ℂ} {M R : ℝ}
    (hM : 0 ≤ M) (hx : ‖x‖ ^ 2 ≤ M) (hy : ‖y‖ ^ 2 ≤ M)
    (hv : 1 ≤ ‖y - x‖ ^ 2) (hR : ‖y - x‖ ≤ R) :
    ‖x‖ ≤ (2 * M + 2) * R ∧ ‖y‖ ≤ (2 * M + 2) * R := by
  have hd : 1 ≤ ‖y - x‖ := by nlinarith [norm_nonneg (y - x)]
  have hR₁ : 1 ≤ R := hd.trans hR
  have hb : ∀ z : ℂ, ‖z‖ ^ 2 ≤ M → ‖z‖ ≤ 2 * M + 2 := by
    intro z hz
    by_contra hn
    have hl : 2 * M + 2 < ‖z‖ := lt_of_not_ge hn
    have hp : 0 ≤ (‖z‖ - 1) * ‖z‖ :=
      mul_nonneg (by linarith) (norm_nonneg z)
    nlinarith
  have hm : 2 * M + 2 ≤ (2 * M + 2) * R := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * M + 2) (sub_nonneg.mpr hR₁)]
  exact ⟨(hb x hx).trans hm, (hb y hy).trans hm⟩

/-- A discrete lattice embedded as a closed subset of Euclidean space has
finite balls. This uses compactness of genuine Euclidean closed balls. -/
theorem finite_balls_of_closedEmbedding {ι E : Type*} [TopologicalSpace ι]
    [DiscreteTopology ι] [NormedAddCommGroup E] [ProperSpace E] (f : ι → E)
    (hf : Topology.IsClosedEmbedding f) (T : ℝ) :
    {i : ι | ‖f i‖ ≤ T}.Finite := by
  have hc := hf.isCompact_preimage (isCompact_closedBall (0 : E) T)
  simpa only [Set.preimage, Metric.mem_closedBall, dist_zero_right] using hc.finite_of_discrete

/-- Every invertible real linear change of the coefficient lattice has a closed
discrete embedding in the Euclidean plane. -/
theorem coefficient_lattice_closedEmbedding
    (e : (Fin 2 → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)) :
    Topology.IsClosedEmbedding (fun z : Fin 2 → ℤ => e (fun i => (z i : ℝ))) := by
  exact e.toHomeomorph.isClosedEmbedding.comp
    (Topology.IsClosedEmbedding.piMap fun _ : Fin 2 => Real.isClosedEmbedding_intCast)

/-- Finite balls for an arbitrary full coefficient lattice embedding. -/
theorem coefficient_lattice_finite_balls
    (e : (Fin 2 → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2)) (T : ℝ) :
    {z : Fin 2 → ℤ | ‖e (fun i => (z i : ℝ))‖ ≤ T}.Finite :=
  finite_balls_of_closedEmbedding _ (coefficient_lattice_closedEmbedding e) T

/-- Bounded-norm elements need not form a finite set (real quadratic units give
an infinite example). Nevertheless their distinct close ordered pairs form a
finite set, provided lattice balls are finite and nonzero difference norms are
nonzero integers. These hypotheses expose the lattice and arithmetic bridges
needed to apply the real-coordinate radius theorem to an order. -/
theorem finite_real_minkowski_close_pairs {ι : Type*}
    (f : ι → EuclideanSpace ℝ (Fin 2))
    (hballs : ∀ T : ℝ, {i : ι | ‖f i‖ ≤ T}.Finite)
    (hintegral : ∀ i j : ι, i ≠ j →
      ∃ n : ℤ, (f j 0 - f i 0) * (f j 1 - f i 1) = (n : ℝ) ∧ n ≠ 0)
    {M R : ℝ} (hM : 0 ≤ M) :
    {p : ι × ι | p.1 ≠ p.2 ∧ |f p.1 0 * f p.1 1| ≤ M ∧
      |f p.2 0 * f p.2 1| ≤ M ∧ ‖f p.2 - f p.1‖ ≤ R}.Finite := by
  apply ((hballs ((2 * M + 2) * R)).prod (hballs ((2 * M + 2) * R))).subset
  rintro ⟨i, j⟩ ⟨hne, hi, hj, hd⟩
  obtain ⟨n, hn, hn0⟩ := hintegral i j hne
  have hv : 1 ≤ |(f j 0 - f i 0) * (f j 1 - f i 1)| := by
    apply one_le_abs_of_nonzero_integer ⟨n, hn⟩
    rw [hn]
    exact_mod_cast hn0
  exact real_minkowski_pair_radius hM hi hj hv hd

/-- The close-pair finiteness result with a standard topological lattice
hypothesis rather than a separately supplied finite-ball bound. -/
theorem finite_real_minkowski_close_pairs_of_closedEmbedding
    {ι : Type*} [TopologicalSpace ι] [DiscreteTopology ι]
    (f : ι → EuclideanSpace ℝ (Fin 2)) (hf : Topology.IsClosedEmbedding f)
    (hintegral : ∀ i j : ι, i ≠ j →
      ∃ n : ℤ, (f j 0 - f i 0) * (f j 1 - f i 1) = (n : ℝ) ∧ n ≠ 0)
    {M R : ℝ} (hM : 0 ≤ M) :
    {p : ι × ι | p.1 ≠ p.2 ∧ |f p.1 0 * f p.1 1| ≤ M ∧
      |f p.2 0 * f p.2 1| ≤ M ∧ ‖f p.2 - f p.1‖ ≤ R}.Finite :=
  finite_real_minkowski_close_pairs f (finite_balls_of_closedEmbedding f hf) hintegral hM

/-- In imaginary Minkowski coordinates bounded field norm already bounds the
actual complex absolute value, so the bounded-norm lattice points themselves
are finite. -/
theorem finite_imaginary_minkowski_bounded_norm
    {ι : Type*} [TopologicalSpace ι] [DiscreteTopology ι]
    (f : ι → ℂ) (hf : Topology.IsClosedEmbedding f) {M : ℝ} (hM : 0 ≤ M) :
    {i : ι | ‖f i‖ ^ 2 ≤ M}.Finite := by
  apply (finite_balls_of_closedEmbedding f hf (2 * M + 2)).subset
  intro i hi
  change ‖f i‖ ^ 2 ≤ M at hi
  change ‖f i‖ ≤ 2 * M + 2
  by_contra hn
  have hl : 2 * M + 2 < ‖f i‖ := lt_of_not_ge hn
  have hp : 0 ≤ (‖f i‖ - 1) * ‖f i‖ :=
    mul_nonneg (by linarith) (norm_nonneg _)
  nlinarith

/-- The all-coefficient-lattice specialization of real close-pair isolation. -/
theorem finite_coefficient_minkowski_close_pairs
    (e : (Fin 2 → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin 2))
    (hintegral : ∀ i j : Fin 2 → ℤ, i ≠ j →
      ∃ n : ℤ,
        (e (fun k => (j k : ℝ)) 0 - e (fun k => (i k : ℝ)) 0) *
          (e (fun k => (j k : ℝ)) 1 - e (fun k => (i k : ℝ)) 1) = (n : ℝ) ∧ n ≠ 0)
    {M R : ℝ} (hM : 0 ≤ M) :
    {p : (Fin 2 → ℤ) × (Fin 2 → ℤ) | p.1 ≠ p.2 ∧
      |e (fun k => (p.1 k : ℝ)) 0 * e (fun k => (p.1 k : ℝ)) 1| ≤ M ∧
      |e (fun k => (p.2 k : ℝ)) 0 * e (fun k => (p.2 k : ℝ)) 1| ≤ M ∧
      ‖e (fun k => (p.2 k : ℝ)) - e (fun k => (p.1 k : ℝ))‖ ≤ R}.Finite :=
  finite_real_minkowski_close_pairs_of_closedEmbedding _
    (coefficient_lattice_closedEmbedding e) hintegral hM

end Entry002
