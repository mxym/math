import ClassReduction
import SharpConstant

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

/-- The complete sharp response statement: actual rational optimizers on
conjugacy classes, the actual orbital matrix, the signed-kernel supremum,
all atom locations, and disjoint sharp probability perturbations. -/
theorem universal_orbital_theorem :
    ∃ C : ℚ, ∃ p q : ConjClasses G → ℚ, ∃ coeff : Orbitals G Ω → ℚ,
      0 ≤ C ∧ C ≤ 1 ∧
      Probability (rationalLaw p) ∧ Probability (rationalLaw q) ∧
      Match (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)))
        (rationalLaw p) (rationalLaw q) ∧ p 1 - q 1 = C ∧
      (C : ℝ) = sharpConstant (imageFeatures (G := G) (Ω := Ω)) (1 : G) ∧
      (C : ℝ) = oscillation (orbitalFeatures (G := G) (Ω := Ω)) (1 : G)
        (fun o => (coeff o : ℝ)) ∧
      (C : ℝ) = oscillation (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)))
        (1 : ConjClasses G) (fun o => (coeff o : ℝ)) ∧
      PairBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) (C : ℝ) ∧
      PairBound (rationalFeatures (classFeaturesQ (G := G) (Ω := Ω)))
        (1 : ConjClasses G) (C : ℝ) ∧
      (∀ other : Orbitals G Ω → ℝ, (C : ℝ) ≤
        oscillation (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) other) ∧
      (∀ σ : G, UniformLawBound (imageFeatures (G := G) (Ω := Ω)) σ (C : ℝ)) ∧
      (let P := liftLaw ConjClasses.mk (rationalLaw p)
       let Q := liftLaw ConjClasses.mk (rationalLaw q)
       Probability P ∧ Probability Q ∧ Central P ∧ Central Q ∧
       Match (imageFeatures (G := G) (Ω := Ω)) P Q ∧ P 1 - Q 1 = (C : ℝ) ∧
       ((0 : ℚ) < C →
         (∀ g, P g = 0 ∨ Q g = 0) ∧
         ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 ≤ δ → δ ≤ ε →
           Probability (fun g => uniform g + δ * (P g - Q g)) ∧
           Match (imageFeatures (G := G) (Ω := Ω))
             (fun g => uniform g + δ * (P g - Q g)) uniform ∧
           TV (fun g => (uniform g + δ * (P g - Q g)) - uniform g) = δ ∧
           (uniform (1 : G) + δ * (P 1 - Q 1)) - uniform (1 : G) = (C : ℝ) * δ)) := by
  classical
  let M := classFeaturesQ (G := G) (Ω := Ω)
  obtain ⟨C, p, q, coeff, a, b, hC, hC1, hp, hq, hm, hobj, hw, hr, hb, _⟩ :=
    exact_rational_primal_dual M (1 : ConjClasses G)
  let P := liftLaw ConjClasses.mk (rationalLaw p)
  let Q := liftLaw ConjClasses.mk (rationalLaw q)
  have hP : Probability P := liftLaw_probability _ ConjClasses.mk_surjective _ hp
  have hQ : Probability Q := liftLaw_probability _ ConjClasses.mk_surjective _ hq
  have hPC : Central P := class_lift_central _
  have hQC : Central Q := class_lift_central _
  have hmatch : Match (imageFeatures (G := G) (Ω := Ω)) P Q :=
    (class_lift_match _ _).mpr hm
  have heq : P 1 - Q 1 = (C : ℝ) := by
    simp only [P, Q, class_lift_identity, rationalLaw]
    exact_mod_cast hobj
  have hwidth : (b : ℝ) - (a : ℝ) = (C : ℝ) := by exact_mod_cast hw
  have horange : ∀ g : G, (a : ℝ) ≤
        dualScore (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) (fun o => (coeff o : ℝ)) g ∧
      dualScore (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) (fun o => (coeff o : ℝ)) g ≤ (b : ℝ) := by
    intro g
    rw [orbital_score_class]
    exact hr (ConjClasses.mk g)
  have hob : PairBound (orbitalFeatures (G := G) (Ω := Ω)) (1 : G) (C : ℝ) :=
    intervalDual_pairBound _ _ _ ⟨(fun o => (coeff o : ℝ)), a, b, horange, hwidth.le⟩
  have hib : PairBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) (C : ℝ) := by
    intro v w hv hww hmw
    exact hob v w hv hww (match_image_implies_orbital v w hmw)
  have hoptimal : PairBound (imageFeatures (G := G) (Ω := Ω)) (1 : G) (P 1 - Q 1) := by
    rw [heq]
    exact hib
  have hs := sharpConstant_eq_optimum (imageFeatures (G := G) (Ω := Ω)) (1 : G)
    P Q hP hQ hmatch hoptimal
  have ho : (C : ℝ) = oscillation (orbitalFeatures (G := G) (Ω := Ω)) (1 : G)
      (fun o => (coeff o : ℝ)) := by
    apply le_antisymm
    · rw [← heq]
      exact oscillation_pairBound _ _ _ P Q hP hQ (match_image_implies_orbital P Q hmatch)
    · have hmax : scoreMax (orbitalFeatures (G := G) (Ω := Ω)) (1 : G)
          (fun o => (coeff o : ℝ)) ≤ (b : ℝ) :=
        Finset.sup'_le _ _ (fun g _ => (horange g).2)
      have hmin : (a : ℝ) ≤ scoreMin (orbitalFeatures (G := G) (Ω := Ω)) (1 : G)
          (fun o => (coeff o : ℝ)) :=
        Finset.le_inf' _ _ (fun g _ => (horange g).1)
      dsimp [oscillation]
      linarith [hwidth]
  refine ⟨C, p, q, coeff, hC, hC1, hp, hq, hm, hobj, ?_, ho, ?_, hib, hb, ?_, ?_, ?_⟩
  · exact (hs.trans heq).symm
  · exact ho.trans (class_oscillation _)
  · intro other
    rw [← heq]
    exact oscillation_pairBound _ _ other P Q hP hQ (match_image_implies_orbital P Q hmatch)
  · exact uniformBound_all_atoms _ ((uniformLawBound_iff_pairBound
      (imageFeatures (G := G) (Ω := Ω)) (1 : G) (C : ℝ) (by exact_mod_cast hC)).mpr hib)
  · refine ⟨hP, hQ, hPC, hQC, hmatch, heq, ?_⟩
    intro hpos
    have hpositive : 0 < P 1 - Q 1 := by rw [heq]; exact_mod_cast hpos
    refine ⟨probability_parts_disjoint_of_tv_one P Q hP hQ
      (optimal_pair_tv_one _ _ P Q hP hQ hmatch hpositive hoptimal), ?_⟩
    simpa only [P, Q, class_lift_identity, rationalLaw, ← Rat.cast_sub, hobj] using positive_optimum_attained_locally
      (imageFeatures (G := G) (Ω := Ω)) (1 : G) P Q hP hQ hmatch hpositive hoptimal

end
end OrbitalMarginals
