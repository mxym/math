import RationalProjection
import Oscillation

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {I J : Type*} [Fintype I] [Nonempty I] [Fintype J]

def rationalFeatures (A : J → I → ℚ) : J → I → ℝ := fun j g => (A j g : ℝ)

def rationalLaw (p : I → ℚ) : I → ℝ := fun g => (p g : ℝ)

/-- Rationalize a zero-gap primal/dual witness simultaneously.  Applying a
rational-linear map separately to arbitrarily rounded data would not suffice. -/
theorem rationalize_pair_dual (A : J → I → ℚ) (i : I)
    (p q : I → ℝ) (coeff : J → ℝ) (a b : ℝ)
    (hp : Probability p) (hq : Probability q) (hm : Match (rationalFeatures A) p q)
    (hr : ∀ g, a ≤ dualScore (rationalFeatures A) i coeff g ∧
      dualScore (rationalFeatures A) i coeff g ≤ b)
    (hgap : p i - q i = b - a) :
    ∃ f : ℝ →ₗ[ℚ] ℚ, f 1 = 1 ∧
      Probability (fun g => (f (p g) : ℝ)) ∧
      Probability (fun g => (f (q g) : ℝ)) ∧
      Match (rationalFeatures A) (fun g => (f (p g) : ℝ)) (fun g => (f (q g) : ℝ)) ∧
      (f (p i) : ℝ) - (f (q i) : ℝ) = (f b : ℝ) - (f a : ℝ) ∧
      ∀ g, (f a : ℝ) ≤ dualScore (rationalFeatures A) i (fun j => (f (coeff j) : ℝ)) g ∧
        dualScore (rationalFeatures A) i (fun j => (f (coeff j) : ℝ)) g ≤ (f b : ℝ) := by
  classical
  let lower : I → ℝ := fun g => dualScore (rationalFeatures A) i coeff g - a
  let upper : I → ℝ := fun g => b - dualScore (rationalFeatures A) i coeff g
  let s : Finset ℝ := Finset.univ.image p ∪ Finset.univ.image q ∪
    Finset.univ.image lower ∪ Finset.univ.image upper
  obtain ⟨f, hf1, hf⟩ := finite_rational_projection s
  have hprob (v : I → ℝ) (hv : Probability v) (hvs : ∀ g, v g ∈ s) :
      Probability (fun g => (f (v g) : ℝ)) := by
    constructor
    · intro g
      change 0 ≤ (f (v g) : ℝ)
      exact_mod_cast hf (v g) (hvs g) (hv.1 g)
    · have he : ∑ g, f (v g) = 1 := by rw [← map_sum, hv.2, hf1]
      change (∑ g, (f (v g) : ℝ)) = 1
      exact_mod_cast he
  have hp' := hprob p hp (fun g => by simp [s])
  have hq' := hprob q hq (fun g => by simp [s])
  have hm' : Match (rationalFeatures A) (fun g => (f (p g) : ℝ))
      (fun g => (f (q g) : ℝ)) := by
    intro j
    have he : (∑ g, A j g * f (p g)) = ∑ g, A j g * f (q g) := by
      have hh := congrArg f (hm j)
      simpa only [rationalFeatures, map_sum, rational_projection_mul] using hh
    change (∑ g, (A j g : ℝ) * (f (p g) : ℝ)) = ∑ g, (A j g : ℝ) * (f (q g) : ℝ)
    exact_mod_cast he
  let scoreQ : I → ℚ := fun g => (if g = i then 1 else 0) - ∑ j, f (coeff j) * A j g
  have hscore (g : I) : f (dualScore (rationalFeatures A) i coeff g) = scoreQ g := by
    simp only [dualScore, rationalFeatures, map_sub, map_sum, scoreQ]
    congr 1
    · split_ifs <;> simp [hf1]
    · apply Finset.sum_congr rfl
      intro j _
      simpa only [mul_comm] using rational_projection_mul f (A j g) (coeff j)
  have hcast (g : I) : dualScore (rationalFeatures A) i (fun j => (f (coeff j) : ℝ)) g =
      (scoreQ g : ℝ) := by
    by_cases h : g = i <;> simp [dualScore, rationalFeatures, scoreQ, h]
  refine ⟨f, hf1, hp', hq', hm', ?_, ?_⟩
  · have he := congrArg f hgap
    simp only [map_sub] at he
    exact_mod_cast he
  · intro g
    have hlo := hf (lower g) (by simp [s]) (sub_nonneg.mpr (hr g).1)
    have hup := hf (upper g) (by simp [s]) (sub_nonneg.mpr (hr g).2)
    simp only [lower, upper, map_sub, hscore] at hlo hup
    rw [hcast]
    constructor
    · exact_mod_cast (by linarith : f a ≤ scoreQ g)
    · exact_mod_cast (by linarith : scoreQ g ≤ f b)

/-- Every finite rational feature system has rational optimal primal and dual
solutions; no LP solver, vertex-existence axiom, or rationality premise is used. -/
theorem exact_rational_primal_dual (A : J → I → ℚ) (i : I) :
    ∃ C : ℚ, ∃ p q : I → ℚ, ∃ coeff : J → ℚ, ∃ a b : ℚ,
      0 ≤ C ∧ C ≤ 1 ∧
      Probability (rationalLaw p) ∧ Probability (rationalLaw q) ∧
      Match (rationalFeatures A) (rationalLaw p) (rationalLaw q) ∧
      p i - q i = C ∧ b - a = C ∧
      (∀ g, (a : ℝ) ≤ dualScore (rationalFeatures A) i (fun j => (coeff j : ℝ)) g ∧
        dualScore (rationalFeatures A) i (fun j => (coeff j : ℝ)) g ≤ (b : ℝ)) ∧
      PairBound (rationalFeatures A) i (C : ℝ) ∧
      UniformLawBound (rationalFeatures A) i (C : ℝ) := by
  obtain ⟨C, p, q, coeff, a, b, hC, hC1, hp, hq, hm, heq, hb, _, hr, hw⟩ :=
    exact_real_primal_dual (rationalFeatures A) i
  obtain ⟨f, _, hp', hq', hm', hg, hr'⟩ :=
    rationalize_pair_dual A i p q coeff a b hp hq hm hr (heq.trans hw.symm)
  let c : ℚ := f (p i) - f (q i)
  have hnew : PairBound (rationalFeatures A) i (c : ℝ) := by
    apply intervalDual_pairBound
    refine ⟨(fun j => (f (coeff j) : ℝ)), (f a : ℝ), (f b : ℝ), hr', ?_⟩
    dsimp [c]
    push_cast
    exact le_of_eq hg.symm
  have hc : (c : ℝ) = C := by
    have hle := hb _ _ hp' hq' hm'
    have hge := hnew p q hp hq hm
    dsimp [c] at hge ⊢
    push_cast at hge ⊢
    linarith [heq]
  refine ⟨c, (fun g => f (p g)), (fun g => f (q g)), (fun j => f (coeff j)),
    f a, f b, ?_, ?_, hp', hq', hm', rfl, ?_, hr', hnew, ?_⟩
  · exact_mod_cast hc ▸ hC
  · exact_mod_cast hc ▸ hC1
  · exact_mod_cast hg.symm
  · rw [hc]
    exact (uniformLawBound_iff_pairBound (rationalFeatures A) i C hC).mpr hb

end
end OrbitalMarginals
