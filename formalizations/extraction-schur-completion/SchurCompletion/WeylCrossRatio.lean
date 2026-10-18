import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

open scoped BigOperators Topology
open Filter

namespace ExtractionSchur

noncomputable section

/-- Cross-block shifts j-i, using zero-based i<s and j=s+j'. -/
def crossShift (s t : ℕ) (i : Fin s) (j : Fin t) : ℕ := s + j.val - i.val

theorem crossShift_pos (s t : ℕ) (i : Fin s) (j : Fin t) : 0 < crossShift s t i j := by
  unfold crossShift
  omega

def weylCrossRatio (s t : ℕ) (rows : Fin s → ℕ) : ℝ :=
  ∏ i : Fin s, ∏ j : Fin t,
    ((rows i : ℝ) + (crossShift s t i j : ℝ)) / (crossShift s t i j : ℝ)

def weylCrossDenominator (s t : ℕ) : ℝ :=
  ∏ i : Fin s, ∏ j : Fin t, (crossShift s t i j : ℝ)

/-- The manuscript's c_(D,s), with D=s+t and g=s*t. -/
def sharpSupportConstant (s t : ℕ) : ℝ :=
  ((s : ℝ)^(s*t))⁻¹ / weylCrossDenominator s t

theorem weylCrossDenominator_pos (s t : ℕ) : 0 < weylCrossDenominator s t := by
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  exact_mod_cast crossShift_pos s t i j

theorem sharpSupportConstant_pos (s t : ℕ) (hs : 0 < s) :
    0 < sharpSupportConstant s t := by
  exact div_pos (inv_pos.mpr (pow_pos (by exact_mod_cast hs) _))
    (weylCrossDenominator_pos s t)

theorem weylCrossRatio_ge_one (s t : ℕ) (rows : Fin s → ℕ) : 1 ≤ weylCrossRatio s t rows := by
  apply Finset.one_le_prod₀
  intro i _
  apply Finset.one_le_prod₀
  intro j _
  have hδ : 0 < (crossShift s t i j : ℝ) := by exact_mod_cast crossShift_pos s t i j
  apply (one_le_div hδ).mpr
  exact le_add_of_nonneg_left (Nat.cast_nonneg _)

def normalizedWeylCrossRatio (s t k : ℕ) (rows : Fin s → ℕ) : ℝ :=
  ∏ i : Fin s, ∏ j : Fin t,
    ((rows i : ℝ) / (k : ℝ) + (crossShift s t i j : ℝ) / (k : ℝ)) /
      (crossShift s t i j : ℝ)

theorem normalizedWeylCrossRatio_eq (s t k : ℕ) (rows : Fin s → ℕ) :
    normalizedWeylCrossRatio s t k rows = weylCrossRatio s t rows / (k : ℝ)^(s*t) := by
  have he (i : Fin s) (j : Fin t) :
      ((rows i : ℝ) / (k : ℝ) + (crossShift s t i j : ℝ) / (k : ℝ)) /
          (crossShift s t i j : ℝ) =
        (((rows i : ℝ) + (crossShift s t i j : ℝ)) / (crossShift s t i j : ℝ)) / k := by
    rw [← add_div]
    ring
  simp only [normalizedWeylCrossRatio, he, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, weylCrossRatio, ← pow_mul, Nat.mul_comm t s]

theorem product_uniform_limit_eq_constant (s t : ℕ) :
    (∏ i : Fin s, ∏ j : Fin t, ((s : ℝ)⁻¹ / (crossShift s t i j : ℝ))) =
      sharpSupportConstant s t := by
  simp only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← pow_mul, inv_pow, Nat.mul_comm t s,
    sharpSupportConstant, weylCrossDenominator]

/-- Exact polynomial exponent and leading cross-Weyl constant along every
sequence of row lengths whose normalized coordinates approach uniformity.
This theorem does not assume a moment limit or the desired rank asymptotic. -/
theorem weylCrossRatio_uniform_limit (s t : ℕ) (rows : ℕ → Fin s → ℕ)
    (hrows : ∀ i : Fin s, Tendsto (fun k => (rows k i : ℝ) / (k : ℝ)) atTop
      (𝓝 (s : ℝ)⁻¹)) :
    Tendsto (fun k => weylCrossRatio s t (rows k) / (k : ℝ)^(s*t)) atTop
      (𝓝 (sharpSupportConstant s t)) := by
  have hnorm : Tendsto (fun k => normalizedWeylCrossRatio s t k (rows k)) atTop
      (𝓝 (∏ i : Fin s, ∏ j : Fin t, ((s : ℝ)⁻¹ / (crossShift s t i j : ℝ)))) := by
    apply tendsto_finsetProd
    intro i _
    apply tendsto_finsetProd
    intro j _
    have hshift : Tendsto (fun k : ℕ => (crossShift s t i j : ℝ) / (k : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    simpa only [add_zero] using ((hrows i).add hshift).div_const (crossShift s t i j : ℝ)
  simpa only [normalizedWeylCrossRatio_eq, product_uniform_limit_eq_constant] using hnorm

theorem weylCrossRatio_reciprocal_uniform_limit (s t : ℕ) (hs : 0 < s)
    (rows : ℕ → Fin s → ℕ)
    (hrows : ∀ i : Fin s, Tendsto (fun k => (rows k i : ℝ) / (k : ℝ)) atTop
      (𝓝 (s : ℝ)⁻¹)) :
    Tendsto (fun k : ℕ => (k : ℝ)^(s*t) / weylCrossRatio s t (rows k)) atTop
      (𝓝 (sharpSupportConstant s t)⁻¹) := by
  simpa only [inv_div] using (weylCrossRatio_uniform_limit s t rows hrows).inv₀
    (sharpSupportConstant_pos s t hs).ne'

end
end ExtractionSchur
