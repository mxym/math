import SymmetricSupport.FiberFactorial
import SymmetricSupport.Density
import SymmetricSupport.PhaseAverage
import SymmetricSupport.ExponentialMoments

open scoped BigOperators ComplexOrder
open Matrix MeasureTheory Set

namespace SymmetricSupport

noncomputable section

theorem occupationExponent_le {D k : ℕ} (s : Sym (Fin D) k) (d : Fin D) :
    occupationExponent s d ≤ k := by
  change Multiset.count d s.val ≤ k
  exact (Multiset.count_le_card _ _).trans_eq s.property

theorem occupation_amplitude_eq_product {D k : ℕ} (s : Sym (Fin D) k)
    (z : Fin D → ℂ) :
    (s.val.map z).prod = ∏ d : Fin D, z d ^ occupationExponent s d := by
  rw [← eval_monomial_multiset, MvPolynomial.eval_monomial]
  simp only [one_mul]
  exact Finsupp.prod_fintype _ _ (by simp)

theorem purePower_eq_product_occupation (D k : ℕ) (z : Fin D → ℂ) (w : Word D k) :
    purePower D k z w = ∏ d : Fin D, z d ^ occupationExponent (occupation D k w) d := by
  rw [← occupation_amplitude_eq_product (occupation D k w) z]
  change _ = (((List.Vector.ofFn w).toList : List (Fin D)).map z).prod
  simp [purePower, List.Vector.toList_ofFn, List.prod_ofFn]

theorem phase_multi_correlation (D L : ℕ) (hL : 0 < L)
    (a b : Fin D → ℕ) (ha : ∀ d, a d < L) (hb : ∀ d, b d < L) :
    (∑ θ : Fin D → Fin L,
      ∏ d : Fin D, (phaseRoot L ^ (θ d).val) ^ a d *
        star ((phaseRoot L ^ (θ d).val) ^ b d)) =
      if a = b then ((L ^ D : ℕ) : ℂ) else 0 := by
  classical
  rw [← Fintype.prod_sum (fun (d : Fin D) (j : Fin L) =>
    (phaseRoot L ^ j.val) ^ a d * star ((phaseRoot L ^ j.val) ^ b d))]
  simp_rw [phase_correlation_star hL _ _ (ha _) (hb _)]
  by_cases hab : a = b
  · subst b
    simp
  · rw [ite_eq_right hab]
    obtain ⟨d, hd⟩ : ∃ d, a d ≠ b d := Function.ne_iff.mp hab
    exact Finset.prod_eq_zero (Finset.mem_univ d) (by simp [hd])

def phaseRadialVector (D L : ℕ) (x : Fin D → ℝ) (θ : Fin D → Fin L) : Fin D → ℂ :=
  fun d => (Real.sqrt (x d) : ℂ) * phaseRoot L ^ (θ d).val

/-- An explicit finite phase average, still on the original tensor coordinates. -/
def phaseRadialAverage (D k L : ℕ) (x : Fin D → ℝ) :
    Matrix (Word D k) (Word D k) ℂ :=
  ((L ^ D : ℕ) : ℂ)⁻¹ •
    ∑ θ : Fin D → Fin L, purePowerDensity D k (phaseRadialVector D L x θ)

theorem phaseRadialAverage_apply (D k L : ℕ) (hL : k < L)
    (x : Fin D → ℝ) (hx : ∀ d, 0 ≤ x d) (v w : Word D k) :
    phaseRadialAverage D k L x v w =
      if occupation D k v = occupation D k w then
        ∏ d : Fin D, (x d : ℂ) ^ occupationExponent (occupation D k v) d else 0 := by
  classical
  let a := occupationExponent (occupation D k v)
  let b := occupationExponent (occupation D k w)
  have ha : ∀ d, a d < L := fun d => (occupationExponent_le _ d).trans_lt hL
  have hb : ∀ d, b d < L := fun d => (occupationExponent_le _ d).trans_lt hL
  have hterm : ∀ θ : Fin D → Fin L,
      purePowerDensity D k (phaseRadialVector D L x θ) v w =
        (∏ d : Fin D, ((Real.sqrt (x d) : ℂ) ^ a d *
          star ((Real.sqrt (x d) : ℂ) ^ b d))) *
        (∏ d : Fin D, (phaseRoot L ^ (θ d).val) ^ a d *
          star ((phaseRoot L ^ (θ d).val) ^ b d)) := by
    intro θ
    simp only [purePowerDensity, Matrix.vecMulVec_apply, Pi.star_apply,
      purePower_eq_product_occupation, phaseRadialVector, mul_pow, star_prod, star_mul]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro d _
    dsimp only [a, b]
    ring
  simp only [phaseRadialAverage, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  simp_rw [hterm]
  rw [← Finset.mul_sum, phase_multi_correlation D L (Nat.zero_le k |>.trans_lt hL) _ _ ha hb]
  have heq : a = b ↔ occupation D k v = occupation D k w :=
    (occupationExponent_injective D k).eq_iff
  have heqf : (a : Fin D → ℕ) = (b : Fin D → ℕ) ↔
      occupation D k v = occupation D k w := by
    exact ⟨fun h => heq.mp (DFunLike.coe_injective h),
      fun h => congrArg DFunLike.coe (heq.mpr h)⟩
  by_cases hab : occupation D k v = occupation D k w
  · rw [ite_eq_left hab, ite_eq_left (heqf.mpr hab)]
    have hn : (((L ^ D : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast pow_ne_zero D (Nat.ne_of_gt (Nat.zero_le k |>.trans_lt hL))
    have hrad : (∏ d : Fin D, (Real.sqrt (x d) : ℂ) ^ a d *
        star ((Real.sqrt (x d) : ℂ) ^ b d)) =
        ∏ d : Fin D, (x d : ℂ) ^ a d := by
      apply Finset.prod_congr rfl
      intro d _
      rw [heq.mpr hab]
      simp only [map_pow, Complex.star_def, Complex.conj_ofReal]
      rw [← mul_pow]
      congr 1
      exact_mod_cast Real.mul_self_sqrt (hx d)
    rw [hrad]
    field_simp
    rfl
  · rw [ite_eq_right hab, ite_eq_right (fun h => hab (heqf.mp h))]
    simp

def radialMeasure (D : ℕ) : Measure (Fin D → ℝ) :=
  Measure.pi (fun _ : Fin D => volume.restrict (Ioi 0))

def radialWeight (D : ℕ) (x : Fin D → ℝ) : ℝ :=
  ∏ d : Fin D, Real.exp (-x d)

def radialMoment (D : ℕ) (a : Fin D → ℕ) (x : Fin D → ℝ) : ℝ :=
  ∏ d : Fin D, (x d) ^ a d * Real.exp (-x d)

theorem radialMeasure_ae_positive (D : ℕ) :
    ∀ᵐ x : Fin D → ℝ ∂radialMeasure D, ∀ d, 0 < x d := by
  apply Filter.eventually_all.mpr
  intro d
  exact (Measure.tendsto_eval_ae_ae
    (μ := fun _ : Fin D => volume.restrict (Ioi 0)) (i := d)).eventually
      (self_mem_ae_restrict measurableSet_Ioi)

theorem radialMoment_integrable (D : ℕ) (a : Fin D → ℕ) :
    Integrable (radialMoment D a) (radialMeasure D) :=
  MeasureTheory.Integrable.fintype_prod_dep (fun d => integrable_exponential_moment (a d))

theorem radialMoment_integral (D : ℕ) (a : Fin D → ℕ) :
    (∫ x, radialMoment D a x ∂radialMeasure D) = ∏ d : Fin D, ((a d).factorial : ℝ) :=
  integral_product_exponential_moment a

theorem phaseRadialAverage_weighted_ae (D k L : ℕ) (hL : k < L) (v w : Word D k) :
    (fun x => (radialWeight D x : ℂ) * phaseRadialAverage D k L x v w) =ᵐ[radialMeasure D]
      (fun x => if occupation D k v = occupation D k w then
        (radialMoment D (occupationExponent (occupation D k v)) x : ℂ) else 0) := by
  classical
  filter_upwards [radialMeasure_ae_positive D] with x hx
  rw [phaseRadialAverage_apply D k L hL x (fun d => (hx d).le)]
  by_cases hab : occupation D k v = occupation D k w
  · simp only [ite_eq_left hab, radialWeight, radialMoment, Complex.ofReal_prod,
      Complex.ofReal_mul, Complex.ofReal_pow]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro d _
    ring
  · simp [hab]

theorem phaseRadialAverage_weighted_integrable (D k L : ℕ) (hL : k < L) (v w : Word D k) :
    Integrable (fun x => (radialWeight D x : ℂ) * phaseRadialAverage D k L x v w)
      (radialMeasure D) := by
  classical
  have h : Integrable (fun x => if occupation D k v = occupation D k w then
      (radialMoment D (occupationExponent (occupation D k v)) x : ℂ) else 0)
      (radialMeasure D) := by
    split_ifs
    · exact (radialMoment_integrable D _).ofReal
    · exact integrable_zero _ _ _
  exact h.congr (phaseRadialAverage_weighted_ae D k L hL v w).symm

/-- Exact Wick frame identity on actual tensor coordinates. A finite phase set and
positive exponential radial density replace the full unitary-group Haar theory. -/
theorem phaseRadialAverage_weighted_integral (D k L : ℕ) (hL : k < L) (v w : Word D k) :
    (∫ x, (radialWeight D x : ℂ) * phaseRadialAverage D k L x v w ∂radialMeasure D) =
      (k.factorial : ℂ) * symmetricProjector D k v w := by
  classical
  rw [integral_congr_ae (phaseRadialAverage_weighted_ae D k L hL v w)]
  change _ = (k.factorial : ℂ) * partitionProjector (occupation D k) v w
  rw [partitionProjector_apply]
  by_cases hab : occupation D k v = occupation D k w
  · simp only [ite_eq_left hab]
    rw [integral_complex_ofReal, radialMoment_integral]
    push_cast
    have hf := fiberCard_mul_occupation_factorials D k (occupation D k v)
    have hn : (fiberCard (occupation D k) (occupation D k v) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (fiberCard_pos _ (occupation_surjective D k) _)
    have hfC : (fiberCard (occupation D k) (occupation D k v) : ℂ) *
        (∏ d : Fin D, ((occupationExponent (occupation D k v) d).factorial : ℂ)) =
          (k.factorial : ℂ) := by exact_mod_cast hf
    rw [← hfC]
    field_simp
  · simp [hab]

end
end SymmetricSupport
