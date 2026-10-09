import CholletRegularTriangleFree

/-! Uniform scaled fractional matching in a small degree-two block. -/
set_option autoImplicit false
open scoped BigOperators
open OAI.MatchingEntropy
namespace Chollet.Matching
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
noncomputable section

theorem degree_scaling (H : LooplessGraph V E) (x : E → ℝ) (a : ℝ) (v : V) :
    H.degree (fun e => a*x e) v = a*H.degree x v := by
  simp [LooplessGraph.degree,Finset.mul_sum,mul_ite]

theorem internalMass_scaling (H : LooplessGraph V E) (x : E → ℝ) (a : ℝ) (S : Finset V) :
    internalMass H (fun e => a*x e) S = a*internalMass H x S := by
  simp [internalMass,Finset.mul_sum,mul_ite]

def regularMatchingScale (n : ℕ) : ℝ := (10/9 : ℝ)*((n : ℝ)-1)/(n : ℝ)

theorem regularMatchingScale_nonneg (n : ℕ) (hn : 4 ≤ n) : 0 ≤ regularMatchingScale n := by
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : (0 : ℝ) < n := by linarith
  have hm : (0 : ℝ) ≤ (n : ℝ)-1 := by linarith
  unfold regularMatchingScale
  exact div_nonneg (mul_nonneg (by norm_num) hm) hp.le

theorem regularMatchingScale_le_one (n : ℕ) (hn : 4 ≤ n) (hn' : n ≤ 10) :
    regularMatchingScale n ≤ 1 := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hu : (n : ℝ) ≤ 10 := by exact_mod_cast hn'
  unfold regularMatchingScale
  apply (div_le_iff₀ hp).mpr
  linarith

theorem regularMatchingScale_lower_coefficient (n : ℕ) (hn : 4 ≤ n) :
    (5/8 : ℝ) ≤ regularMatchingScale n*(4/5 : ℝ) := by
  have hp : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hl : (4 : ℝ) ≤ n := by exact_mod_cast hn
  unfold regularMatchingScale
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hp).mpr
  linarith

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem regular_two_oriented_card (hd : ∀ v,G.degree v=2) :
    (Fintype.card (OrientedEdges G) : ℝ) = 2*(Fintype.card V : ℝ) := by
  have h := sum_oriented_edges G (fun _ _ => (1 : ℝ))
  have hr (v : V) : (∑ u,if G.Adj v u then (1 : ℝ) else 0) = 2 := by
    rw [← G.degree_eq_sum_if_adj (R := ℝ) v,hd v]
    norm_num
  simp only [hr,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at h
  linarith

theorem regular_two_full_internal_mass (hd : ∀ v,G.degree v=2) :
    internalMass (orientedLoopless G) (fractionalOrientedWeight G) Finset.univ =
      (9/20 : ℝ)*(Fintype.card V : ℝ) := by
  have h := regular_two_oriented_card G hd
  simp [internalMass,fractionalOrientedWeight,degreeKernel,hd]
  linarith

theorem fractional_ordinary_feasible_regular_small (hd : ∀ v,G.degree v=2)
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Preconnected)
    (hn : 4 ≤ Fintype.card V) (hn' : Fintype.card V ≤ 10) :
    OrdinaryFeasible (orientedLoopless G)
      (fun e => regularMatchingScale (Fintype.card V)*fractionalOrientedWeight G e) := by
  let a := regularMatchingScale (Fintype.card V)
  have ha : 0 ≤ a := regularMatchingScale_nonneg _ hn
  have ha' : a ≤ 1 := regularMatchingScale_le_one _ hn hn'
  have hdeg : ∀ v,2 ≤ G.degree v := fun v => by rw [hd v]
  refine ⟨fun e => mul_nonneg ha (fractionalOrientedWeight_nonneg G e),?_,?_⟩
  · intro v
    rw [degree_scaling]
    have h := mul_le_mul_of_nonneg_left (fractionalOrientedWeight_degree G hdeg v) ha
    have h' := mul_le_mul_of_nonneg_right ha' (by norm_num : (0 : ℝ) ≤ 9/10)
    linarith
  · intro S hodd
    rw [internalMass_scaling]
    by_cases hw : ∃ w : V,w ∉ S
    · have h := mul_le_mul_of_nonneg_left (fractional_proper_odd_set_bound G hdeg hr S hodd hw) ha
      have hpos : 0 ≤ ((S.card : ℝ)-1)/2 := by
        obtain ⟨k,hk⟩ := hodd
        have hs : 1 ≤ S.card := by omega
        have hs' : (1 : ℝ) ≤ S.card := by exact_mod_cast hs
        linarith
      have h' := mul_le_mul_of_nonneg_right ha' hpos
      linarith
    · push_neg at hw
      have hS : S=Finset.univ := by ext v; simp [hw v]
      rw [hS,regular_two_full_internal_mass G hd,Finset.card_univ]
      have hp : (Fintype.card V : ℝ) ≠ 0 := by
        have h : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
        exact h.ne'
      change regularMatchingScale (Fintype.card V)*((9/20 : ℝ)*(Fintype.card V : ℝ)) ≤ _
      unfold regularMatchingScale
      field_simp [hp]
      ring_nf
      exact le_rfl

end
end Chollet.Matching
