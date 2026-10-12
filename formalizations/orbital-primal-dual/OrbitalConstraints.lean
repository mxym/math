import OrbitalReduction

open scoped BigOperators

namespace OrbitalMarginals

noncomputable section

variable {G Ω : Type*} [Group G] [Fintype G] [Fintype Ω] [DecidableEq Ω]
  [MulAction G Ω]

theorem orbital_moment_expansion (o : Orbitals G Ω) (v : G → ℝ) :
    (∑ g, orbitalFeatures o g * v g) =
      ∑ xy : Ω × Ω, (if orbitalOf (G := G) xy = o then (1 : ℝ) else 0) *
        (∑ g, imageFeatures xy g * v g) := by
  classical
  have hh (g : G) := orbital_score_expansion
    (fun o' : Orbitals G Ω => if o' = o then (1 : ℝ) else 0) g
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hh
  simp_rw [hh, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro xy _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  split_ifs <;> ring

theorem central_image_moment_smul (p : G → ℝ) (hp : Central p)
    (h : G) (xy : Ω × Ω) :
    (∑ g, imageFeatures (h • xy) g * p g) = ∑ g, imageFeatures xy g * p g := by
  calc
    (∑ g, imageFeatures (h • xy) g * p g) =
        ∑ g, imageFeatures (h • xy) (h * g * h⁻¹) * p (h * g * h⁻¹) :=
      (Equiv.sum_comp (conjugationEquiv h) _).symm
    _ = ∑ g, imageFeatures xy g * p g := by
      apply Finset.sum_congr rfl
      intro g _
      rw [hp h g]
      change imageFeatures (h • xy.1, h • xy.2) (h * g * h⁻¹) * p g =
        imageFeatures (xy.1, xy.2) g * p g
      rw [← imageFeature_conjugate h g xy.1 xy.2]

theorem central_image_moment_orbital (p : G → ℝ) (hp : Central p)
    (xy zw : Ω × Ω) (he : orbitalOf (G := G) xy = orbitalOf (G := G) zw) :
    (∑ g, imageFeatures xy g * p g) = ∑ g, imageFeatures zw g * p g := by
  obtain ⟨h, hh⟩ := MulAction.mem_orbit_iff.mp
    (MulAction.orbitRel_apply.mp (Quotient.exact he))
  rw [← hh]
  exact central_image_moment_smul p hp h zw

theorem central_match_iff_orbital (p q : G → ℝ) (hp : Central p) (hq : Central q) :
    Match (imageFeatures (G := G) (Ω := Ω)) p q ↔
      Match (orbitalFeatures (G := G) (Ω := Ω)) p q := by
  constructor
  · exact match_image_implies_orbital p q
  · intro hm xy
    classical
    let o := orbitalOf (G := G) xy
    let t : Finset (Ω × Ω) := Finset.univ.filter (fun zw => orbitalOf (G := G) zw = o)
    have ht : 0 < (t.card : ℝ) := by
      have hne : t.Nonempty := ⟨xy, by simp [t, o]⟩
      exact_mod_cast Finset.card_pos.mpr hne
    have hexpand (v : G → ℝ) (hv : Central v) :
        (∑ g, orbitalFeatures o g * v g) = (t.card : ℝ) * (∑ g, imageFeatures xy g * v g) := by
      rw [orbital_moment_expansion]
      calc
        (∑ zw : Ω × Ω, (if orbitalOf (G := G) zw = o then (1 : ℝ) else 0) *
            (∑ g, imageFeatures zw g * v g)) =
            ∑ zw ∈ t, (∑ g, imageFeatures zw g * v g) := by
          simp [t, Finset.sum_filter, ite_mul]
        _ = ∑ _zw ∈ t, (∑ g, imageFeatures xy g * v g) := by
          apply Finset.sum_congr rfl
          intro zw hzw
          exact central_image_moment_orbital v hv zw xy (Finset.mem_filter.mp hzw).2
        _ = _ := by simp
    have hh := hm o
    rw [hexpand p hp, hexpand q hq] at hh
    exact (mul_left_cancel₀ ht.ne') hh

theorem orbitalFeatures_conjugate (o : Orbitals G Ω) (h g : G) :
    orbitalFeatures o (h * g * h⁻¹) = orbitalFeatures o g := by
  classical
  dsimp [orbitalFeatures]
  calc
    (∑ x : Ω, if orbitalOf (G := G) (x, (h * g * h⁻¹) • x) = o then (1 : ℝ) else 0) =
        ∑ x : Ω, if orbitalOf (G := G) (h • x, (h * g * h⁻¹) • (h • x)) = o
          then (1 : ℝ) else 0 := (Equiv.sum_comp (MulAction.toPerm h) _).symm
    _ = ∑ x : Ω, if orbitalOf (G := G) (x, g • x) = o then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      have hxy : (h • x, (h * g * h⁻¹) • (h • x)) = h • (x, g • x) := by
        simp [mul_smul]
      rw [hxy, orbitalOf_smul]

end
end OrbitalMarginals
