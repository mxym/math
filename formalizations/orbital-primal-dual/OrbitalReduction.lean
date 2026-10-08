import SharpAttainment
import Mathlib.GroupTheory.GroupAction.Defs

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

abbrev Orbitals (G Ω : Type*) [Group G] [MulAction G Ω] :=
  MulAction.orbitRel.Quotient G (Ω × Ω)

noncomputable instance : Fintype (Orbitals G Ω) := Fintype.ofFinite _

noncomputable instance : DecidableEq (Orbitals G Ω) := Classical.decEq _

def orbitalOf (xy : Ω × Ω) : Orbitals G Ω := Quotient.mk'' xy

theorem orbitalOf_smul (h : G) (xy : Ω × Ω) :
    orbitalOf (G := G) (h • xy) = orbitalOf (G := G) xy :=
  MulAction.orbitRel.Quotient.quotient_smul_eq

def orbitalFeatures (o : Orbitals G Ω) (g : G) : ℝ :=
  ∑ x : Ω, if orbitalOf (G := G) (x, g • x) = o then 1 else 0

def averagedCoefficient (coeff : Ω × Ω → ℝ) (xy : Ω × Ω) : ℝ :=
  (∑ h : G, coeff (h • xy)) / (Fintype.card G : ℝ)

theorem averagedCoefficient_smul (coeff : Ω × Ω → ℝ) (s : G) (xy : Ω × Ω) :
    averagedCoefficient (G := G) coeff (s • xy) = averagedCoefficient (G := G) coeff xy := by
  dsimp [averagedCoefficient]
  congr 1
  have hh := Equiv.sum_comp (Equiv.mulRight s) (fun h => coeff (h • xy))
  change (∑ h, coeff ((h * s) • xy)) = ∑ h, coeff (h • xy) at hh
  simpa only [mul_smul] using hh

def orbitalCoefficient (coeff : Ω × Ω → ℝ) : Orbitals G Ω → ℝ :=
  Quotient.lift (averagedCoefficient (G := G) coeff) (by
    intro xy zw hr
    obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp hr)
    rw [← hh]
    exact averagedCoefficient_smul coeff h zw)

theorem orbitalCoefficient_apply (coeff : Ω × Ω → ℝ) (xy : Ω × Ω) :
    orbitalCoefficient coeff (orbitalOf (G := G) xy) = averagedCoefficient (G := G) coeff xy := rfl

theorem orbital_score_expansion (coeff : Orbitals G Ω → ℝ) (g : G) :
    (∑ o, coeff o * orbitalFeatures o g) =
      ∑ xy : Ω × Ω, coeff (orbitalOf (G := G) xy) * imageFeatures xy g := by
  classical
  calc
    (∑ o, coeff o * orbitalFeatures o g) =
        ∑ x : Ω, coeff (orbitalOf (G := G) (x, g • x)) := by
      simp only [orbitalFeatures, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      simp [eq_comm]
    _ = ∑ xy : Ω × Ω, coeff (orbitalOf (G := G) xy) * imageFeatures xy g := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      simp [imageFeatures, eq_comm]

theorem averaged_score (coeff : Ω × Ω → ℝ) (g : G) :
    dualScore (imageFeatures (G := G) (Ω := Ω)) (1 : G) (averagedCoefficient (G := G) coeff) g =
      (∑ h : G, dualScore (imageFeatures (G := G) (Ω := Ω)) (1 : G) coeff
        (h * g * h⁻¹)) / (Fintype.card G : ℝ) := by
  classical
  have hc : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hid (h : G) : (h * g * h⁻¹ = 1) ↔ g = 1 := by
    constructor
    · intro he
      calc
        g = h⁻¹ * (h * g * h⁻¹) * h := by group
        _ = 1 := by rw [he]; group
    · intro he
      rw [he]
      group
  have hexpand :
      (∑ xy : Ω × Ω, averagedCoefficient (G := G) coeff xy * imageFeatures xy g) =
        (∑ h : G, ∑ xy : Ω × Ω, coeff xy * imageFeatures xy (h * g * h⁻¹)) /
          (Fintype.card G : ℝ) := by
    simp only [averagedCoefficient, div_mul_eq_mul_div, Finset.sum_mul, ← Finset.sum_div]
    rw [Finset.sum_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro h _
    calc
      (∑ xy : Ω × Ω, coeff (h • xy) * imageFeatures xy g) =
          ∑ xy : Ω × Ω, coeff (h • xy) * imageFeatures (h • xy) (h * g * h⁻¹) := by
        apply Finset.sum_congr rfl
        rintro ⟨x, y⟩ _
        rw [imageFeature_conjugate h g x y]
        rfl
      _ = ∑ xy : Ω × Ω, coeff xy * imageFeatures xy (h * g * h⁻¹) := by
        exact Equiv.sum_comp (MulAction.toPerm h : Equiv.Perm (Ω × Ω))
          (fun xy : Ω × Ω => coeff xy * imageFeatures xy (h * g * h⁻¹))
  simp only [dualScore, hid, Finset.sum_sub_distrib]
  rw [hexpand]
  by_cases he : g = 1 <;> simp [sub_div, he, hc, neg_div]

theorem orbital_dual_range (coeff : Ω × Ω → ℝ) (a b : ℝ)
    (hr : ∀ g : G, a ≤ dualScore (imageFeatures (G := G) (Ω := Ω)) (1 : G) coeff g ∧
      dualScore (imageFeatures (G := G) (Ω := Ω)) (1 : G) coeff g ≤ b) :
    ∀ g : G, a ≤ dualScore (orbitalFeatures (G := G) (Ω := Ω)) (1 : G)
        (orbitalCoefficient coeff) g ∧
      dualScore (orbitalFeatures (G := G) (Ω := Ω)) (1 : G)
        (orbitalCoefficient coeff) g ≤ b := by
  classical
  have hc : 0 < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  intro g
  have hs : dualScore (orbitalFeatures (G := G) (Ω := Ω)) (1 : G)
      (orbitalCoefficient coeff) g =
      (∑ h : G, dualScore (imageFeatures (G := G) (Ω := Ω)) (1 : G) coeff
        (h * g * h⁻¹)) / (Fintype.card G : ℝ) := by
    rw [← averaged_score]
    simp only [dualScore, orbital_score_expansion, orbitalCoefficient_apply]
  rw [hs]
  constructor
  · apply (le_div_iff₀ hc).mpr
    calc
      a * (Fintype.card G : ℝ) = ∑ _h : G, a := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun h _ => (hr _).1
  · apply (div_le_iff₀ hc).mpr
    calc
      _ ≤ ∑ _h : G, b := Finset.sum_le_sum fun h _ => (hr _).2
      _ = b * (Fintype.card G : ℝ) := by simp [mul_comm]

theorem match_image_implies_orbital (p q : G → ℝ)
    (hm : Match (imageFeatures (G := G) (Ω := Ω)) p q) :
    Match (orbitalFeatures (G := G) (Ω := Ω)) p q := by
  classical
  intro o
  have hexpand (v : G → ℝ) :
      (∑ g, orbitalFeatures o g * v g) =
        ∑ xy : Ω × Ω, (if orbitalOf (G := G) xy = o then 1 else 0) *
          (∑ g, imageFeatures xy g * v g) := by
    have hh (g : G) := orbital_score_expansion
      (fun o' => if o' = o then 1 else 0) g
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hh
    simp_rw [hh, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro xy _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro g _
    split_ifs <;> ring
  rw [hexpand p, hexpand q]
  apply Finset.sum_congr rfl
  intro xy _
  rw [hm xy]

/-- The unreduced real primal has an optimal orbital dual, with all moments and
all probability laws interpreted by their actual finite sums. -/
theorem exact_orbital_duality :
    ∃ p q : G → ℝ, ∃ coeff : Orbitals G Ω → ℝ,
      Probability p ∧ Probability q ∧ Central p ∧ Central q ∧
      Match (imageFeatures (G := G) (Ω := Ω)) p q ∧
      p 1 - q 1 = oscillation (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) coeff ∧
      PairBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) (p 1 - q 1) ∧
      ∀ otherCoeff : Orbitals G Ω → ℝ,
        p 1 - q 1 ≤ oscillation (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) otherCoeff := by
  classical
  obtain ⟨p, q, raw, hp, hq, hpc, hqc, hm, ho, hb, _⟩ :=
    group_action_central_primal (G := G) (Ω := Ω)
  have hmatch := (match_iff_imageMass p q).mpr hm
  let coeff : Orbitals G Ω → ℝ := orbitalCoefficient raw
  have hr := orbital_dual_range raw
    (scoreMin (imageFeatures (G := G) (Ω := Ω)) (1 : G) raw)
    (scoreMax (imageFeatures (G := G) (Ω := Ω)) (1 : G) raw)
    (score_range _ _ _)
  have hupper : oscillation (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) coeff ≤ p 1 - q 1 := by
    rw [ho]
    dsimp [oscillation]
    have h1 : scoreMax (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) coeff ≤
        scoreMax (imageFeatures (G := G) (Ω := Ω)) (1 : G) raw :=
      Finset.sup'_le _ _ fun g _ => (hr g).2
    have h2 : scoreMin (imageFeatures (G := G) (Ω := Ω)) (1 : G) raw ≤
        scoreMin (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) coeff :=
      Finset.le_inf' _ _ fun g _ => (hr g).1
    linarith
  have hpair := match_image_implies_orbital p q hmatch
  have hmin (other : Orbitals G Ω → ℝ) :
      p 1 - q 1 ≤ oscillation (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) other :=
    (oscillation_pairBound _ _ other) p q hp hq hpair
  exact ⟨p, q, coeff, hp, hq, hpc, hqc, hmatch, le_antisymm (hmin coeff) hupper, hb, hmin⟩

end
end OrbitalMarginals
