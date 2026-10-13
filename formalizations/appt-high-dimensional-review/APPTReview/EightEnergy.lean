import APPTReview.GeometricScales

open scoped BigOperators
namespace APPTReview

noncomputable def hierarchyEnergy (h : ℝ) : ℝ := 2*h^2/(h+1)^4
noncomputable def hierarchySpike (h : ℝ) : ℝ := 2*h/(h+1)

theorem sqrt_eq_of_nonnegative_square (x y : ℝ) (hx : 0≤x) (hy : 0≤y) (hy2 : y^2=x) :
    Real.sqrt x=y := by
  have hs := Real.sq_sqrt hx
  have hn := Real.sqrt_nonneg x
  nlinarith

theorem hierarchy_energy_bound (h : ℝ) (hh : 1≤h) :
    Real.sqrt ((2*h^2)*hierarchyEnergy h)+Real.sqrt (2*hierarchyEnergy h)=hierarchySpike h := by
  have hp : 0<h+1 := by linarith
  have he : 0≤hierarchyEnergy h := by unfold hierarchyEnergy; positivity
  have h1 : Real.sqrt ((2*h^2)*hierarchyEnergy h)=2*h^2/(h+1)^2 := by
    apply sqrt_eq_of_nonnegative_square
    · positivity
    · positivity
    · unfold hierarchyEnergy
      field_simp
  have h2 : Real.sqrt (2*hierarchyEnergy h)=2*h/(h+1)^2 := by
    apply sqrt_eq_of_nonnegative_square
    · positivity
    · positivity
    · unfold hierarchyEnergy
      field_simp
  rw [h1,h2]
  unfold hierarchySpike
  field_simp

theorem hierarchy_spike_range (h : ℝ) (hh : 1≤h) :
    0≤hierarchySpike h ∧ hierarchySpike h<2 := by
  have hp : 0<h+1 := by linarith
  unfold hierarchySpike
  exact ⟨by positivity,(div_lt_iff₀ hp).2 (by linarith)⟩

theorem hierarchy_total_energy (h : ℝ) (hh : 1≤h) :
    (hierarchySpike h)^2+(2*h^2)*hierarchyEnergy h=
      4*(h/(h+1))^2+4*(h/(h+1))^4 := by
  have hp : h+1≠0 := ne_of_gt (by linarith : 0<h+1)
  unfold hierarchySpike hierarchyEnergy
  field_simp
  ring

theorem hierarchy_deficit_bound (h : ℝ) (hh : 1≤h) :
    8-24/(h+1)≤(hierarchySpike h)^2+(2*h^2)*hierarchyEnergy h := by
  rw [hierarchy_total_energy h hh]
  let z := h/(h+1)
  have hp : h+1≠0 := ne_of_gt (by linarith : 0<h+1)
  have hz : 1-z=1/(h+1) := by dsimp [z]; field_simp; ring
  have hs : 0≤4*(1-z)^2*((z+1)^2+3) := by positivity
  have ht : 8-24*(1-z)≤4*z^2+4*z^4 := by nlinarith
  rw [hz] at ht
  simpa only [mul_one_div] using ht

/-- Exact finite-list energy, including its distinct-scale cardinality. -/
theorem geometric_hierarchy_energy (h : ℕ) :
    (∑ d∈(geometricScales (2*h^2)).toFinset,hierarchyEnergy h)=
      (2*(h:ℝ)^2)*hierarchyEnergy h := by
  simp only [Finset.sum_const,nsmul_eq_mul,geometricScales_card,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]

theorem geometric_hierarchy_budget (h : ℕ) (hh : 1≤h) :
    scaleEnergyBound (geometricScales (2*h^2)) (fun _ => hierarchyEnergy h) (hierarchyEnergy h)=hierarchySpike h := by
  rw [scaleEnergyBound,geometric_hierarchy_energy]
  exact hierarchy_energy_bound (h:ℝ) (by exact_mod_cast hh)

end APPTReview
