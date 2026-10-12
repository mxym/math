import Oscillation
import Mathlib.Algebra.Group.Action.Basic

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

def imageFeatures (xy : Ω × Ω) (g : G) : ℝ :=
  if g • xy.1 = xy.2 then 1 else 0

def imageMass (p : G → ℝ) (x y : Ω) : ℝ :=
  ∑ g, if g • x = y then p g else 0

omit [Fintype Ω] in
theorem match_iff_imageMass (p q : G → ℝ) : Match (imageFeatures (G := G) (Ω := Ω)) p q ↔
    ∀ x y : Ω, imageMass p x y = imageMass q x y := by
  constructor
  · intro h x y
    simpa [imageFeatures, imageMass] using h (x, y)
  · intro h xy
    simpa [imageFeatures, imageMass] using h xy.1 xy.2

def translate (σ : G) (v : G → ℝ) (g : G) : ℝ := v (σ * g)

theorem sum_translate (σ : G) (v : G → ℝ) :
    (∑ g, translate σ v g) = ∑ g, v g := by
  simpa [translate] using Equiv.sum_comp (Equiv.mulLeft σ) v

theorem tv_translate (σ : G) (v : G → ℝ) : TV (translate σ v) = TV v := by
  dsimp [TV, translate]
  congr 1
  simpa using Equiv.sum_comp (Equiv.mulLeft σ) (fun g => |v g|)

omit [Fintype G] [Fintype Ω] in
theorem imageFeature_translate (σ g : G) (x y : Ω) :
    imageFeatures (x, y) g = imageFeatures (x, σ • y) (σ * g) := by
  simp [imageFeatures, mul_smul, smul_left_cancel_iff]

theorem kernel_translate (σ : G) (v : G → ℝ) (hv : Kernel (imageFeatures (G := G) (Ω := Ω)) v) :
    Kernel (imageFeatures (G := G) (Ω := Ω)) (translate σ v) := by
  constructor
  · exact (sum_translate σ v).trans hv.1
  · rintro ⟨x, y⟩
    calc
      (∑ g, imageFeatures (x, y) g * translate σ v g) =
          ∑ g, imageFeatures (x, σ • y) (σ * g) * v (σ * g) := by
        apply Finset.sum_congr rfl
        intro g _
        rw [imageFeature_translate σ g x y]
        rfl
      _ = ∑ g, imageFeatures (x, σ • y) g * v g := by
        simpa using Equiv.sum_comp (Equiv.mulLeft σ)
          (fun g => imageFeatures (x, σ • y) g * v g)
      _ = 0 := hv.2 (x, σ • y)

theorem signedBound_all_atoms (C : ℝ) (h : SignedBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) C) :
    ∀ σ : G, SignedBound (imageFeatures (G := G) (Ω := Ω)) σ C := by
  intro σ v hv
  have hh := h (translate σ v) (kernel_translate σ v hv)
  simpa only [translate, mul_one, tv_translate] using hh

theorem uniformBound_all_atoms (C : ℝ) (h : UniformLawBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) C) :
    ∀ σ : G, UniformLawBound (imageFeatures (G := G) (Ω := Ω)) σ C := by
  intro σ
  apply (uniformLawBound_iff_signedBound (imageFeatures (G := G) (Ω := Ω)) σ C).mpr
  exact signedBound_all_atoms C
    ((uniformLawBound_iff_signedBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) C).mp h) σ

/-- Actual finite-group image constraints and actual probability laws.
The sharp real primal/dual response applies without faithfulness or transitivity. -/
theorem group_action_exact_response :
    ∃ p q : G → ℝ, ∃ coeff : Ω × Ω → ℝ,
      Probability p ∧ Probability q ∧
      (∀ x y : Ω, imageMass p x y = imageMass q x y) ∧
      p 1 - q 1 = oscillation (imageFeatures (G := G) (Ω := Ω)) (1 : G) coeff ∧
      (∀ σ : G, ∀ ν : G → ℝ, Probability ν →
        (∀ x y : Ω, imageMass ν x y = imageMass (uniform : G → ℝ) x y) →
        |ν σ - uniform σ| ≤ (p 1 - q 1) * TV (fun g => ν g - uniform g)) ∧
      ∀ otherCoeff : Ω × Ω → ℝ, p 1 - q 1 ≤ oscillation (imageFeatures (G := G) (Ω := Ω)) (1 : G) otherCoeff := by
  obtain ⟨p, q, coeff, hp, hq, hm, ho, _, hu, hmin⟩ :=
    exact_oscillation_duality (imageFeatures (G := G) (Ω := Ω)) (1 : G)
  refine ⟨p, q, coeff, hp, hq, (match_iff_imageMass p q).mp hm, ho, ?_, hmin⟩
  intro σ ν hν hmatch
  exact uniformBound_all_atoms (p 1 - q 1) hu σ ν hν
    ((match_iff_imageMass ν uniform).mpr hmatch)

end
end OrbitalMarginals
