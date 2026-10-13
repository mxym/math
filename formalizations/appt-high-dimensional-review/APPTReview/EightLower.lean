import APPTReview.EightEnergy

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- The coefficient-eight lower bound for actual APPT density matrices.
For each tolerance the finite hierarchy is fixed first; one dimension threshold
then works for every larger second factor. No exchange with a growing hierarchy
or unproved projection/graph interface occurs in the final statement. -/
theorem appt_growing_dimension_eight_lower (ε : ℝ) (hε : 0<ε) :
    ∃ M : ℕ, 2≤M ∧ ∀ m n : ℕ, M≤m → m≤n →
      ∃ A : Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ,
      APPT.Quantum.IsDensity A ∧ APPT.Quantum.AbsolutelyPPT A ∧
      8-ε≤((m:ℝ)*n)^2*(APPT.Quantum.purity A-1/((m:ℝ)*n)) := by
  obtain ⟨h,hh⟩ := exists_nat_gt (max (1:ℝ) (48/ε))
  have hhR : (1:ℝ)≤h := (le_max_left _ _).trans hh.le
  have hhN : 1≤h := by exact_mod_cast hhR
  have heps : 48/ε<(h:ℝ) := (le_max_right _ _).trans_lt hh
  have hmul : 48<(h:ℝ)*ε := (div_lt_iff₀ hε).mp heps
  have hp : (0:ℝ)<(h:ℝ)+1 := by linarith
  have hsmall : 24/((h:ℝ)+1)≤ε/2 := (div_le_iff₀ hp).2 (by nlinarith)
  let ds := geometricScales (2*h^2)
  let e : ℝ → ℝ := fun _ => hierarchyEnergy h
  let B := hierarchyEnergy (h:ℝ)
  let a := hierarchySpike (h:ℝ)
  have hB : 0≤B := by unfold B hierarchyEnergy; positivity
  have ha : 0≤a ∧ a<2 := hierarchy_spike_range (h:ℝ) hhR
  have hbudget : scaleEnergyBound ds e B=a := geometric_hierarchy_budget h hhN
  have hd1 : ∀ d∈ds,d<1 := by
    intro d hd
    have ht := (geometricScales_range (2*h^2) d hd).2
    linarith
  obtain ⟨M,hM2,hM⟩ := canonical_lacunary_energy_lower ds (geometricScales_lacunary _) hd1 e B a hB
    (fun _ _ => hB) (fun _ _ => le_rfl) ha.1 ha.2 (by rw [hbudget];exact ha.2)
    (ε/2) (by positivity)
  refine ⟨M,hM2,?_⟩
  intro m n hm hmn
  obtain ⟨A,hA,hP,hlo⟩ := hM m n hm hmn
  refine ⟨A,hA,hP,?_⟩
  have hsum : (∑ d∈ds.toFinset,e d)=(2*(h:ℝ)^2)*hierarchyEnergy h := geometric_hierarchy_energy h
  rw [hsum] at hlo
  have hnear := hierarchy_deficit_bound (h:ℝ) hhR
  change (hierarchySpike h)^2+(2*(h:ℝ)^2)*hierarchyEnergy h-ε/2≤_ at hlo
  linarith

end APPTReview
