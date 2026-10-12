import UniversalOrbitalTheorem
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

def identityIndicator (g : G) : ℝ := by
  classical
  exact if g = 1 then 1 else 0

def functionOscillation (f : G → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f - Finset.univ.inf' Finset.univ_nonempty f

theorem orbital_span_exact_minimum :
    ∃ φ : G → ℝ,
      φ ∈ Submodule.span ℝ (Set.range (orbitalFeatures (G := G) (Ω := Ω))) ∧
      sharpConstant (imageFeatures (G := G) (Ω := Ω)) (1 : G) =
        functionOscillation (fun g => identityIndicator g - φ g) ∧
      ∀ ψ : G → ℝ, ψ ∈ Submodule.span ℝ (Set.range (orbitalFeatures (G := G) (Ω := Ω))) →
        sharpConstant (imageFeatures (G := G) (Ω := Ω)) (1 : G) ≤
          functionOscillation (fun g => identityIndicator g - ψ g) := by
  classical
  obtain ⟨C, p, q, coeff, _, _, _, _, _, _, hs, ho, _, _, _, hmin, _⟩ :=
    universal_orbital_theorem (G := G) (Ω := Ω)
  let φ : G → ℝ := ∑ o, (coeff o : ℝ) • orbitalFeatures o
  have hφ : φ ∈ Submodule.span ℝ (Set.range (orbitalFeatures (G := G) (Ω := Ω))) := by
    apply Submodule.sum_mem
    intro o _
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self o))
  refine ⟨φ, hφ, ?_, ?_⟩
  · have he : φ = fun g => ∑ o, (coeff o : ℝ) * orbitalFeatures o g := by
      funext g
      simp [φ]
    rw [← hs, ho, he]
    rfl
  · intro ψ hψ
    obtain ⟨other, he⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hψ
    have he' : ψ = fun g => ∑ o, other o * orbitalFeatures o g := by
      rw [← he]
      funext g
      simp
    rw [he', ← hs]
    exact hmin other

end
end OrbitalMarginals
