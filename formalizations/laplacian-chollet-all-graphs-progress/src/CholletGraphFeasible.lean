import CholletGraphDeficit

/-! Full ordinary matching feasibility for all even-order or large
vertex-robust graphs of minimum degree two. Small odd blocks remain separate. -/
set_option autoImplicit false
open scoped BigOperators
open OAI.MatchingEntropy
namespace Chollet.Matching
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable section

theorem fractional_large_set_bound (hd : ∀ v,2 ≤ G.degree v)
    (S : Finset V) (hS : 10 ≤ S.card) :
    internalMass (orientedLoopless G) (fractionalOrientedWeight G) S ≤
      ((S.card : ℝ) - 1) / 2 := by
  have hh := weighted_handshake (orientedLoopless G) (fractionalOrientedWeight G) S
  have hc : 0 ≤ (orientedLoopless G).cutMass (fractionalOrientedWeight G) S := by
    unfold LooplessGraph.cutMass
    exact Finset.sum_nonneg fun e _ => fractionalOrientedWeight_nonneg G e
  have hs := Finset.sum_le_sum (s := S) (fun v _ => fractionalOrientedWeight_degree G hd v)
  simp only [Finset.sum_const,nsmul_eq_mul] at hs
  have hn : (10 : ℝ) ≤ S.card := by exact_mod_cast hS
  linarith

theorem fractional_ordinary_feasible_even (hd : ∀ v,2 ≤ G.degree v)
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Preconnected)
    (heven : Even (Fintype.card V)) :
    OrdinaryFeasible (orientedLoopless G) (fractionalOrientedWeight G) := by
  refine ⟨fractionalOrientedWeight_nonneg G,?_,?_⟩
  · intro v
    exact (fractionalOrientedWeight_degree G hd v).trans (by norm_num)
  · intro S hodd
    apply fractional_proper_odd_set_bound G hd hr S hodd
    by_contra hn
    push_neg at hn
    have hS : S = Finset.univ := by ext v; simp [hn v]
    rw [hS,Finset.card_univ] at hodd
    obtain ⟨k,hk⟩ := hodd
    obtain ⟨n,hn⟩ := heven
    omega

theorem fractional_ordinary_feasible_large (hd : ∀ v,2 ≤ G.degree v)
    (hr : ∀ v,(G.induce {w : V | w ≠ v}).Preconnected)
    (hlarge : 10 ≤ Fintype.card V) :
    OrdinaryFeasible (orientedLoopless G) (fractionalOrientedWeight G) := by
  refine ⟨fractionalOrientedWeight_nonneg G,?_,?_⟩
  · intro v
    exact (fractionalOrientedWeight_degree G hd v).trans (by norm_num)
  · intro S hodd
    by_cases hw : ∃ w : V,w ∉ S
    · exact fractional_proper_odd_set_bound G hd hr S hodd hw
    · push_neg at hw
      have hS : S = Finset.univ := by ext v; simp [hw v]
      apply fractional_large_set_bound G hd S
      simpa [hS] using hlarge

end
end Chollet.Matching
