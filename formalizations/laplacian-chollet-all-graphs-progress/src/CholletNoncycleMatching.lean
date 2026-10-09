import CholletGraphHighDegree

/-! Full fractional matching feasibility for a vertex-robust block with
minimum degree two and a vertex of degree at least three. -/
set_option autoImplicit false
open scoped BigOperators
open OAI.MatchingEntropy
namespace Chollet.Matching
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable section

theorem full_sum_degreeDeficit_ge_two_thirds
    (hd : ∀ v,2 ≤ G.degree v)
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Connected)
    (hhigh : ∃ v,3 ≤ G.degree v) :
    (2 / 3 : ℝ) ≤ ∑ v,degreeDeficit G Finset.univ v := by
  obtain ⟨v,hv⟩ := hhigh
  obtain ⟨w,hwv,hw⟩ := another_high_degree G v hv hd (hr v)
  calc
    _ ≤ ∑ u ∈ ({v,w} : Finset V),degreeDeficit G Finset.univ u := by
      have h1 := degreeDeficit_ge_third_of_high_degree G Finset.univ v hv
      have h2 := degreeDeficit_ge_third_of_high_degree G Finset.univ w hw
      simp only [Finset.sum_pair hwv.symm]
      linarith
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun u _ _ => degreeDeficit_nonneg G hd Finset.univ u)

theorem fractional_ordinary_feasible_noncycle
    (hd : ∀ v,2 ≤ G.degree v)
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Connected)
    (hhigh : ∃ v,3 ≤ G.degree v) :
    OrdinaryFeasible (orientedLoopless G) (fractionalOrientedWeight G) := by
  refine ⟨fractionalOrientedWeight_nonneg G,?_,?_⟩
  · intro v
    exact (fractionalOrientedWeight_degree G hd v).trans (by norm_num)
  · intro S hodd
    by_cases hw : ∃ w : V,w ∉ S
    · exact fractional_proper_odd_set_bound G hd (fun v => (hr v).preconnected) S hodd hw
    · push_neg at hw
      have hS : S = Finset.univ := by ext v; simp [hw v]
      subst S
      rw [fractionalOrientedWeight_internal_mass]
      have hm := internal_degreeKernel_upper G Finset.univ
      have he := degreeDeficit_sum G Finset.univ
      have hb := full_sum_degreeDeficit_ge_two_thirds G hd hr hhigh
      have hn : 4 ≤ Fintype.card V := by
        obtain ⟨v,hv⟩ := hhigh
        have := G.degree_lt_card_verts v
        omega
      have hn' : (4 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
      simp only [Finset.card_univ] at *
      linarith

end
end Chollet.Matching
