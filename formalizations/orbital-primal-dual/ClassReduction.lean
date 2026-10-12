import OrbitalConstraints
import FiniteFibers
import RationalDuality
import Mathlib.Algebra.Group.ConjFinite

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

noncomputable instance : Fintype (ConjClasses G) := Fintype.ofFinite _
noncomputable instance : DecidableEq (ConjClasses G) := Classical.decEq _

def orbitalFeaturesQ (o : Orbitals G Ω) (g : G) : ℚ :=
  ∑ x : Ω, if orbitalOf (G := G) (x, g • x) = o then 1 else 0

theorem cast_orbitalFeaturesQ (o : Orbitals G Ω) (g : G) :
    (orbitalFeaturesQ o g : ℝ) = orbitalFeatures o g := by
  simp only [orbitalFeaturesQ, orbitalFeatures, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> norm_num

def classFeaturesQ (o : Orbitals G Ω) : ConjClasses G → ℚ :=
  Quotient.lift (orbitalFeaturesQ o) (by
    intro g k h
    obtain ⟨s, hs⟩ := isConj_iff.mp h
    apply Rat.cast_injective (α := ℝ)
    simp only [cast_orbitalFeaturesQ]
    rw [← hs, orbitalFeatures_conjugate])

theorem classFeaturesQ_mk (o : Orbitals G Ω) (g : G) :
    classFeaturesQ o (ConjClasses.mk g) = orbitalFeaturesQ o g := rfl

theorem real_classFeatures_mk (o : Orbitals G Ω) (g : G) :
    rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)) o (ConjClasses.mk g) =
      orbitalFeatures o g := cast_orbitalFeaturesQ o g

theorem class_mk_conjugate (h g : G) :
    ConjClasses.mk (h * g * h⁻¹) = ConjClasses.mk g := by
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  apply IsConj.symm
  exact isConj_iff.mpr ⟨h, rfl⟩

theorem class_identity_iff (g : G) : ConjClasses.mk g = (1 : ConjClasses G) ↔ g = 1 := by
  rw [ConjClasses.one_eq_mk_one, ConjClasses.mk_eq_mk_iff_isConj, isConj_one_left]

theorem class_fiber_identity : fiber (ConjClasses.mk : G → ConjClasses G) 1 = {1} := by
  classical
  ext g
  simp [fiber, class_identity_iff]

theorem class_lift_identity (p : ConjClasses G → ℝ) :
    liftLaw ConjClasses.mk p (1 : G) = p 1 := by
  simp [liftLaw, fiberSize, ← ConjClasses.one_eq_mk_one, class_fiber_identity]

theorem class_push_identity (p : G → ℝ) : pushLaw ConjClasses.mk p 1 = p (1 : G) := by
  simp [pushLaw, class_fiber_identity]

theorem class_lift_central (p : ConjClasses G → ℝ) : Central (liftLaw ConjClasses.mk p) := by
  intro h g
  simp only [liftLaw, class_mk_conjugate]

theorem central_class_constant (p : G → ℝ) (hp : Central p) (g k : G)
    (he : ConjClasses.mk g = ConjClasses.mk k) : p g = p k := by
  obtain ⟨h, hh⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp he)
  rw [← hh, hp h g]

theorem class_lift_push (p : G → ℝ) (hp : Central p) :
    liftLaw ConjClasses.mk (pushLaw ConjClasses.mk p) = p :=
  liftLaw_pushLaw _ p (central_class_constant p hp)

/-- This matrix is exactly the original mean of the integer orbital counts on
an actual conjugacy class, including its nonzero normalization denominator. -/
theorem class_matrix_is_average (o : Orbitals G Ω) (c : ConjClasses G) :
    (classFeaturesQ o c : ℝ) =
      (∑ g ∈ fiber ConjClasses.mk c, orbitalFeatures o g) / fiberSize ConjClasses.mk c := by
  have hc := fiberSize_pos (ConjClasses.mk : G → ConjClasses G) ConjClasses.mk_surjective c
  have hs : (∑ g ∈ fiber ConjClasses.mk c, orbitalFeatures o g) =
      fiberSize ConjClasses.mk c * (classFeaturesQ o c : ℝ) := by
    calc
      _ = ∑ _g ∈ fiber ConjClasses.mk c, (classFeaturesQ o c : ℝ) := by
        apply Finset.sum_congr rfl
        intro g hg
        rw [← real_classFeatures_mk]
        change (classFeaturesQ o (ConjClasses.mk g) : ℝ) = (classFeaturesQ o c : ℝ)
        rw [(Finset.mem_filter.mp hg).2]
      _ = _ := by simp [fiberSize]
  rw [hs]
  field_simp

theorem class_lift_match (p q : ConjClasses G → ℝ) :
    Match (imageFeatures (G := G) (Ω := Ω)) (liftLaw ConjClasses.mk p) (liftLaw ConjClasses.mk q) ↔
      Match (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω))) p q := by
  rw [central_match_iff_orbital _ _ (class_lift_central p) (class_lift_central q)]
  have he : orbitalFeatures (G := G) (Ω := Ω) =
      fun o g => rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)) o (ConjClasses.mk g) := by
    funext o g
    exact (real_classFeatures_mk o g).symm
  rw [he]
  exact lift_match ConjClasses.mk ConjClasses.mk_surjective _ p q

theorem central_class_match (p q : G → ℝ) (hp : Central p) (hq : Central q) :
    Match (imageFeatures (G := G) (Ω := Ω)) p q ↔
      Match (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)))
        (pushLaw ConjClasses.mk p) (pushLaw ConjClasses.mk q) := by
  rw [← class_lift_match, class_lift_push p hp, class_lift_push q hq]

theorem orbital_score_class (coeff : Orbitals G Ω → ℝ) (g : G) :
    dualScore (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) coeff g =
      dualScore (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)))
        (1 : ConjClasses G) coeff (ConjClasses.mk g) := by
  classical
  simp only [dualScore, real_classFeatures_mk, class_identity_iff]

theorem class_oscillation (coeff : Orbitals G Ω → ℝ) :
    oscillation (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) coeff =
      oscillation (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)))
        (1 : ConjClasses G) coeff := by
  have hmax : scoreMax (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) coeff =
      scoreMax (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)))
        (1 : ConjClasses G) coeff := by
    apply le_antisymm
    · apply Finset.sup'_le
      intro g _
      rw [orbital_score_class]
      exact (score_range _ _ _ _).2
    · apply Finset.sup'_le
      intro c _
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      rw [← orbital_score_class]
      exact (score_range _ _ _ _).2
  have hmin : scoreMin (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) coeff =
      scoreMin (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)))
        (1 : ConjClasses G) coeff := by
    apply le_antisymm
    · apply Finset.le_inf'
      intro c _
      obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
      rw [← orbital_score_class]
      exact (score_range _ _ _ _).1
    · apply Finset.le_inf'
      intro g _
      rw [orbital_score_class]
      exact (score_range _ _ _ _).1
  simp only [oscillation, hmax, hmin]

end
end OrbitalMarginals
