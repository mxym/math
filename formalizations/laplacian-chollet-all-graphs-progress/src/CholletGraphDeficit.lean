import CholletGraphBoundary

/-! Quantitative internal-degree deficits used in the odd-set constraints. -/
set_option autoImplicit false
open scoped BigOperators
namespace Chollet.Matching
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable section

def internalDegree (S : Finset V) (v : V) : ℕ := (S.filter (G.Adj v)).card

theorem internalDegree_le_degree (S : Finset V) (v : V) :
    internalDegree G S v ≤ G.degree v := by
  apply Finset.card_le_card
  intro u hu
  exact (SimpleGraph.mem_neighborFinset G v u).mpr (Finset.mem_filter.mp hu).2

theorem internalDegree_lt_degree_of_boundary (S : Finset V) (v : V)
    (hv : v ∈ boundaryVertices G S) : internalDegree G S v + 1 ≤ G.degree v := by
  obtain ⟨_,w,hw,hadj⟩ := Finset.mem_filter.mp hv
  have hn : w ∉ S.filter (G.Adj v) := by simp [hw]
  have hs : insert w (S.filter (G.Adj v)) ⊆ G.neighborFinset v := by
    intro u hu
    rcases Finset.mem_insert.mp hu with he | he
    · subst u; exact (SimpleGraph.mem_neighborFinset G v w).mpr hadj
    · exact (SimpleGraph.mem_neighborFinset G v u).mpr (Finset.mem_filter.mp he).2
  have h := Finset.card_le_card hs
  simpa [Finset.card_insert_of_notMem hn,internalDegree] using h

def degreeDeficit (S : Finset V) (v : V) : ℝ :=
  1 - 2 * (internalDegree G S v : ℝ) / (G.degree v : ℝ)^2

theorem degreeDeficit_nonneg (hd : ∀ v,2 ≤ G.degree v) (S : Finset V) (v : V) :
    0 ≤ degreeDeficit G S v := by
  have hdv : (2 : ℝ) ≤ G.degree v := by exact_mod_cast hd v
  have hi : (internalDegree G S v : ℝ) ≤ G.degree v := by
    exact_mod_cast internalDegree_le_degree G S v
  unfold degreeDeficit
  have hp : (0 : ℝ) < (G.degree v : ℝ)^2 := by positivity
  apply sub_nonneg.mpr
  apply (div_le_iff₀ hp).mpr
  nlinarith

theorem degreeDeficit_ge_third_of_high_degree (S : Finset V) (v : V)
    (hv : 3 ≤ G.degree v) : (1 / 3 : ℝ) ≤ degreeDeficit G S v := by
  have hdv : (3 : ℝ) ≤ G.degree v := by exact_mod_cast hv
  have hi : (internalDegree G S v : ℝ) ≤ G.degree v := by
    exact_mod_cast internalDegree_le_degree G S v
  unfold degreeDeficit
  have hp : (0 : ℝ) < (G.degree v : ℝ)^2 := by positivity
  have ht : 2 * (internalDegree G S v : ℝ) / (G.degree v : ℝ)^2 ≤ 2 / 3 := by
    apply (div_le_iff₀ hp).mpr
    nlinarith
  linarith

theorem degreeDeficit_ge_third_of_boundary (hd : ∀ v,2 ≤ G.degree v)
    (S : Finset V) (v : V) (hv : v ∈ boundaryVertices G S) :
    (1 / 3 : ℝ) ≤ degreeDeficit G S v := by
  by_cases hhigh : 3 ≤ G.degree v
  · exact degreeDeficit_ge_third_of_high_degree G S v hhigh
  have hdv : G.degree v = 2 := by have := hd v; omega
  have hi : internalDegree G S v ≤ 1 := by
    have := internalDegree_lt_degree_of_boundary G S v hv; omega
  have hi' : (internalDegree G S v : ℝ) ≤ 1 := by exact_mod_cast hi
  unfold degreeDeficit
  rw [hdv]
  norm_num
  linarith

theorem sum_degreeDeficit_ge_two_thirds_proper
    (hd : ∀ v,2 ≤ G.degree v)
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Preconnected)
    (S : Finset V) (hS : 2 ≤ S.card) (hw : ∃ w : V,w ∉ S) :
    (2 / 3 : ℝ) ≤ ∑ v ∈ S,degreeDeficit G S v := by
  have hb := two_le_card_boundaryVertices G hr S hS hw
  obtain ⟨u,hu,w,hw',huw⟩ := Finset.one_lt_card.mp (by omega :
    1 < (boundaryVertices G S).card)
  have huS : u ∈ S := (Finset.mem_filter.mp hu).1
  have hwS : w ∈ S := (Finset.mem_filter.mp hw').1
  have hs : ({u,w} : Finset V) ⊆ S := by simp [Finset.insert_subset_iff,huS,hwS]
  calc
    _ ≤ ∑ v ∈ ({u,w} : Finset V),degreeDeficit G S v := by
      have h1 := degreeDeficit_ge_third_of_boundary G hd S u hu
      have h2 := degreeDeficit_ge_third_of_boundary G hd S w hw'
      simp only [Finset.sum_pair huw]
      linarith
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hs (fun v _ _ =>
      degreeDeficit_nonneg G hd S v)

theorem degreeKernel_young (u v : V) :
    2 * degreeKernel G u v ≤ 1 / (G.degree u : ℝ)^2 + 1 / (G.degree v : ℝ)^2 := by
  simp only [degreeKernel,one_div,mul_inv_rev,← inv_pow]
  nlinarith [sq_nonneg ((G.degree u : ℝ)⁻¹ - (G.degree v : ℝ)⁻¹)]

theorem internalDegree_constant_sum (S : Finset V) (v : V) (a : ℝ) :
    (∑ u ∈ S,if G.Adj v u then a else 0) = (internalDegree G S v : ℝ) * a := by
  rw [← Finset.sum_filter]
  simp [internalDegree]

theorem internal_degreeKernel_upper (S : Finset V) :
    2 * (∑ u ∈ S,∑ v ∈ S,if G.Adj u v then degreeKernel G u v else 0) ≤
      2 * (∑ u ∈ S,(internalDegree G S u : ℝ) / (G.degree u : ℝ)^2) := by
  have hsym (u v : V) (a : ℝ) :
      (if G.Adj u v then a else 0) = (if G.Adj v u then a else 0) := by
    by_cases h : G.Adj u v
    · simp [h,h.symm]
    · have h' : ¬G.Adj v u := fun h' => h h'.symm
      simp [h,h']
  have hrev : (∑ u ∈ S,∑ v ∈ S,if G.Adj u v then 1 / (G.degree v : ℝ)^2 else 0) =
      ∑ u ∈ S,(internalDegree G S u : ℝ) / (G.degree u : ℝ)^2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro u _
    have hi (v : V) : (if G.Adj v u then 1 / (G.degree u : ℝ)^2 else 0) =
        (if G.Adj u v then 1 / (G.degree u : ℝ)^2 else 0) := hsym v u _
    simp_rw [hi]
    rw [internalDegree_constant_sum]
    ring
  calc
    _ ≤ ∑ u ∈ S,∑ v ∈ S,
        ((if G.Adj u v then 1 / (G.degree u : ℝ)^2 else 0) +
        (if G.Adj u v then 1 / (G.degree v : ℝ)^2 else 0)) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro u _
      apply Finset.sum_le_sum
      intro v _
      by_cases h : G.Adj u v
      · simpa [h] using degreeKernel_young G u v
      · simp [h]
    _ = 2 * (∑ u ∈ S,(internalDegree G S u : ℝ) / (G.degree u : ℝ)^2) := by
      simp only [Finset.sum_add_distrib]
      rw [hrev]
      simp_rw [internalDegree_constant_sum]
      simp only [div_eq_mul_inv,one_div]
      ring

theorem internalDegree_add_one_le_card (S : Finset V) (v : V) (hv : v ∈ S) :
    internalDegree G S v + 1 ≤ S.card := by
  have hs : S.filter (G.Adj v) ⊆ S.erase v := by
    intro u hu
    obtain ⟨hu,ha⟩ := Finset.mem_filter.mp hu
    exact Finset.mem_erase.mpr ⟨ha.ne.symm,hu⟩
  have h := Finset.card_le_card hs
  have he := Finset.card_erase_add_one hv
  unfold internalDegree
  omega

theorem degreeDeficit_ge_half_of_card_three_boundary
    (hd : ∀ v,2 ≤ G.degree v) (S : Finset V) (hS : S.card = 3)
    (v : V) (hv : v ∈ boundaryVertices G S) :
    (1 / 2 : ℝ) ≤ degreeDeficit G S v := by
  have hi : internalDegree G S v ≤ 2 := by
    have := internalDegree_add_one_le_card G S v (Finset.mem_filter.mp hv).1
    omega
  have hi' : (internalDegree G S v : ℝ) ≤ 2 := by exact_mod_cast hi
  by_cases hhigh : 3 ≤ G.degree v
  · have hdv : (3 : ℝ) ≤ G.degree v := by exact_mod_cast hhigh
    unfold degreeDeficit
    have ht : 2 * (internalDegree G S v : ℝ) / (G.degree v : ℝ)^2 ≤ 1 / 2 := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < (G.degree v : ℝ)^2)).mpr
      nlinarith
    linarith
  · have hdv : G.degree v = 2 := by have := hd v; omega
    have hi : internalDegree G S v ≤ 1 := by
      have := internalDegree_lt_degree_of_boundary G S v hv; omega
    have hi' : (internalDegree G S v : ℝ) ≤ 1 := by exact_mod_cast hi
    unfold degreeDeficit
    rw [hdv]
    norm_num
    linarith

theorem sum_degreeDeficit_ge_one_proper_three
    (hd : ∀ v,2 ≤ G.degree v)
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Preconnected)
    (S : Finset V) (hS : S.card = 3) (hw : ∃ w : V,w ∉ S) :
    (1 : ℝ) ≤ ∑ v ∈ S,degreeDeficit G S v := by
  have hb := two_le_card_boundaryVertices G hr S (by omega) hw
  obtain ⟨u,hu,w,hw',huw⟩ := Finset.one_lt_card.mp (by omega :
    1 < (boundaryVertices G S).card)
  have huS : u ∈ S := (Finset.mem_filter.mp hu).1
  have hwS : w ∈ S := (Finset.mem_filter.mp hw').1
  have hs : ({u,w} : Finset V) ⊆ S := by simp [Finset.insert_subset_iff,huS,hwS]
  calc
    _ ≤ ∑ v ∈ ({u,w} : Finset V),degreeDeficit G S v := by
      have h1 := degreeDeficit_ge_half_of_card_three_boundary G hd S hS u hu
      have h2 := degreeDeficit_ge_half_of_card_three_boundary G hd S hS w hw'
      simp only [Finset.sum_pair huw]
      linarith
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hs (fun v _ _ =>
      degreeDeficit_nonneg G hd S v)

theorem degreeDeficit_sum (S : Finset V) :
    (∑ v ∈ S,degreeDeficit G S v) = (S.card : ℝ) -
      2 * (∑ v ∈ S,(internalDegree G S v : ℝ) / (G.degree v : ℝ)^2) := by
  simp [degreeDeficit,Finset.sum_sub_distrib,← Finset.mul_sum,mul_div_assoc]

theorem fractionalOrientedWeight_internal_mass (S : Finset V) :
    internalMass (orientedLoopless G) (fractionalOrientedWeight G) S =
      (9 / 10 : ℝ) * (∑ u ∈ S,∑ v ∈ S,if G.Adj u v then degreeKernel G u v else 0) := by
  unfold fractionalOrientedWeight
  rw [oriented_internal_mass G (fun u v => (9 / 10 : ℝ) * degreeKernel G u v) S]
  simp [Finset.mul_sum,mul_ite]

theorem fractional_proper_odd_set_bound
    (hd : ∀ v,2 ≤ G.degree v)
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Preconnected)
    (S : Finset V) (hodd : Odd S.card) (hw : ∃ w : V,w ∉ S) :
    internalMass (orientedLoopless G) (fractionalOrientedWeight G) S ≤
      ((S.card : ℝ) - 1) / 2 := by
  rw [fractionalOrientedWeight_internal_mass]
  by_cases h1 : S.card = 1
  · obtain ⟨v,hv⟩ := Finset.card_eq_one.mp h1
    rw [hv]
    simp
  have hm := internal_degreeKernel_upper G S
  have he := degreeDeficit_sum G S
  by_cases h3 : S.card = 3
  · have hb := sum_degreeDeficit_ge_one_proper_three G hd hr S h3 hw
    have hn : (S.card : ℝ) = 3 := by exact_mod_cast h3
    rw [hn] at he ⊢
    linarith
  · have hn : 5 ≤ S.card := by obtain ⟨k,hk⟩ := hodd; omega
    have hn' : (5 : ℝ) ≤ S.card := by exact_mod_cast hn
    have hb := sum_degreeDeficit_ge_two_thirds_proper G hd hr S (by omega) hw
    linarith

end
end Chollet.Matching
