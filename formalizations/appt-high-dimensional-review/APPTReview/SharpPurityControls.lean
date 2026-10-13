import APPTReview.SharpAspectLimit

open scoped BigOperators ComplexOrder Topology
open Matrix Filter
namespace APPTReview

/-- The final square-system coefficient is eight for the actual APPT maximum. -/
theorem appt_balanced_excess_limit :
    Tendsto (fun m : ℕ => (m:ℝ)^4*(apptPuritySup m m-1/(m:ℝ)^2))
      atTop (𝓝 (8:ℝ)) := by
  have hr : Tendsto (fun k : ℕ => (k:ℝ)/(k:ℝ)) atTop (𝓝 (1:ℝ)) := by
    apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [eventually_ge_atTop (1:ℕ)] with k hk
    have hn : (k:ℝ)≠0 := by exact_mod_cast (by omega : k≠0)
    simp [hn]
  have hh := appt_all_aspect_purity_limit (fun k => k) (fun k => k) 1 (by norm_num)
    tendsto_id (Filter.Eventually.of_forall (fun _ => le_rfl)) hr
  norm_num at hh
  convert hh using 1 <;> unfold excessPuritySup <;> congr 1 <;> funext k <;> ring

/-- Each fixed hierarchy has a strictly positive deficit; the limiting value
cannot be asserted at a finite number of scales merely by setting slack to zero. -/
theorem hierarchy_energy_strictly_below_eight (h : ℝ) (hh : 1≤h) :
    (hierarchySpike h)^2+(2*h^2)*hierarchyEnergy h<8 := by
  have hp : 0<h+1 := by linarith
  have hz0 : 0≤h/(h+1) := by positivity
  have hz1 : h/(h+1)<1 := (div_lt_one hp).2 (by linarith)
  have hs : (h/(h+1))^2<1 := by nlinarith
  have hq : ((h/(h+1))^2)^2<1 := by nlinarith [sq_nonneg (h/(h+1))]
  rw [hierarchy_total_energy h hh]
  nlinarith

/-- Exact floor loss is present before the dimension limit. -/
theorem floor_rank_is_not_real_rank : (⌊(3/2:ℝ)⌋₊:ℝ)=1 ∧ (⌊(3/2:ℝ)⌋₊:ℝ)<3/2 := by
  have hf : ⌊(3/2:ℝ)⌋₊=1 := (Nat.floor_eq_iff (by norm_num : (0:ℝ)≤3/2)).2 ⟨by norm_num,by norm_num⟩
  rw [hf]
  norm_num

/-- Positive cross moments cannot be replaced by an equality of diagonal moments. -/
theorem positive_cross_moments_not_zero :
    let X : Matrix (Fin 1) (Fin 1) ℂ := 1
    X.PosSemidef ∧ (X*X).trace.re+(X*X).trace.re<((X+X)*(X+X)).trace.re := by
  dsimp only
  refine ⟨Matrix.PosSemidef.one,?_⟩
  have he : ((1 : Matrix (Fin 1) (Fin 1) ℂ)+1)*(1+1)=1+1+1+1 := by noncomm_ring
  rw [he]
  simp only [Matrix.one_mul,Matrix.trace_add,Matrix.trace_one,Fintype.card_fin,Complex.add_re,Complex.natCast_re]
  norm_num

/-- Trace centering and normalization are not optional in the purity excess. -/
theorem centering_loss_cannot_be_deleted :
    ((2:ℝ)-2^2/4)/(1+2/4)^2=4/9 ∧
    ((2:ℝ)-2^2/4)/(1+2/4)^2<2/(1+2/4)^2 := by norm_num

/-- The two asymptotic branches cross at four, not at one. -/
theorem sharp_branch_regression :
    max (8:ℝ) (4+1)=8 ∧ max (8:ℝ) (4+4)=8 ∧ max (8:ℝ) (4+5)=9 := by norm_num

end APPTReview
