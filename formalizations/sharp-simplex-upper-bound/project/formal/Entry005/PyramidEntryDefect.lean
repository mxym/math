import Entry005.PyramidLiftedMoment

noncomputable section
open Metric MeasureTheory Module
open scoped BigOperators RealInnerProductSpace Pointwise
namespace Entry005
variable {ι : Type*} [Fintype ι] {d : ℕ} [Nontrivial (Space d)]

theorem finite_halfspace_projection_body_volume_pos (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hc : IsCompact (finiteHalfspaceSet n h)) :
    0 < (volume (projectionBodySet (finiteHalfspaceSet n h))).toReal := by
  obtain ⟨ε, hε, hbound⟩ := finite_uniform_positive h hh
  let c := ε⁻¹
  let K := finiteHalfspaceSet n h
  have hcpos : 0 < c := inv_pos.mpr hε
  have hcK : IsCompact (c • K) := by
    change IsCompact ((fun x : Space d => c • x) '' K)
    exact hc.image (continuous_id.const_smul c)
  have hb : closedBall (0 : Space d) 1 ⊆ c • K := by
    intro x hx
    have hxn : ‖x‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hx
    refine ⟨ε • x, ?_, ?_⟩
    · intro i
      rw [inner_smul_right]
      calc
        ε * inner ℝ (n i) x ≤ ε * (‖n i‖ * ‖x‖) :=
          mul_le_mul_of_nonneg_left (real_inner_le_norm _ _) hε.le
        _ ≤ ε := by rw [hn i, one_mul]; exact mul_le_of_le_one_right hε.le hxn
        _ ≤ h i := hbound i
    · change ε⁻¹ • (ε • x) = x
      rw [smul_smul, inv_mul_cancel₀ hε.ne', one_smul]
  obtain ⟨R, hR, hKR⟩ := hcK.isBounded.subset_closedBall_lt 1 (0 : Space d)
  have hp := normalized_projection_body_volume_pos (c • K) hcK hb R (by linarith) hKR
  rw [projection_body_positive_smul K c hcpos,
    real_volume_nonnegative_smul _ _ (pow_pos hcpos _).le] at hp
  exact (mul_pos_iff_of_pos_left (pow_pos (pow_pos hcpos _) _)).mp hp

/-- The published cone-law identity for actual finite halfspace bodies.
Both iid moments use the actual finiteHalfspaceConeLaw. Every geometric identity
and every denominator's positivity is derived in the proof. -/
theorem finite_halfspace_entryA_lifted_moment (n : ι → Space d) (h : ι → ℝ)
    (hn : ∀ i, ‖n i‖ = 1) (hh : ∀ i, 0 < h i) (hinj : Function.Injective n)
    (hc : IsCompact (finiteHalfspaceSet n h)) :
    entryA (finiteHalfspaceSet n h) =
      (∫ w : Fin (d + 1) → Fin d → ℝ,
        |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw (finiteHalfspaceConeLaw n h) (d + 1)) /
      ((d + 1 : ℝ) * (∫ w : Fin d → Fin d → ℝ,
        |horizontalDeterminant w| ∂iidLaw (finiteHalfspaceConeLaw n h) d)) := by
  let K := finiteHalfspaceSet n h
  let V := (volume K).toReal
  let Q := (volume (projectionBodySet K)).toReal
  let B := ∫ w : Fin (d + 1) → Fin d → ℝ,
    |liftedDeterminant (fun j => w j.succ) (w 0)| ∂iidLaw (finiteHalfspaceConeLaw n h) (d + 1)
  have hV : 0 < V := finite_halfspace_volume_pos n h hn hh hc
  have hQ : 0 < Q := finite_halfspace_projection_body_volume_pos n h hn hh hc
  have hd : finrank ℝ (Space d) = d := by simp [Space]
  have hdN : 0 < d := by simpa only [hd] using (finrank_pos : 0 < finrank ℝ (Space d))
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hdN.ne'
  have hdp : (d + 1 : ℝ) ≠ 0 := by positivity
  have hfact : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hPP := pyramid_projection_body_volume_decomposition n h hn hh hinj hc
  rw [pyramid_side_zonotope_volume_lifted_moment n h hn hh hinj hc, hd] at hPP
  change (volume (projectionBodySet (pyramidSet K))).toReal =
    V ^ (d + 1) / ((d + 1).factorial : ℝ) * B + V * (1 / (d : ℝ)) ^ d * Q at hPP
  have hPV := pyramid_finite_halfspace_volume n h hc
  rw [hd] at hPV
  have hA := finite_halfspace_horizontal_first_moment n h hn hh hinj hc
  change _ = (d.factorial : ℝ) / ((d : ℝ) * V) ^ d * Q at hA
  change entryA K = B / ((d + 1 : ℝ) * _)
  rw [hA]
  unfold entryA projectionRatio
  rw [hPP, hPV, finrank_lifted_space, hd]
  simp only [Nat.add_sub_cancel]
  have hpV : V ^ d = V ^ (d - 1) * V := by
    rw [← pow_succ]
    congr 1
    omega
  simp only [div_pow, mul_pow, one_pow, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  change ((d : ℝ) ^ d / (d + 1 : ℝ) ^ d) *
    ((V ^ (d + 1) / ((d + 1 : ℝ) * d.factorial) * B + V * (1 / (d : ℝ) ^ d) * Q) /
      (V ^ d / (d + 1 : ℝ) ^ d)) / (Q / V ^ (d - 1)) - 1 = _
  rw [pow_succ, hpV]
  field_simp [hV.ne', hQ.ne', hdR, hdp, hfact]
  ring

end Entry005
