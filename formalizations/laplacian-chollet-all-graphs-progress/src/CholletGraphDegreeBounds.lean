import CholletSimpleGraphModel

/-! Actual simple-graph degree bounds for the normalized fractional edges.
Both oriented model edges carry half the unordered-edge weight. -/
set_option autoImplicit false
open scoped BigOperators
open OAI.MatchingEntropy
namespace Chollet.Matching
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable section

def degreeKernel (u v : V) : ℝ :=
  1 / ((G.degree u : ℝ) * (G.degree v : ℝ))

theorem degreeKernel_symm (u v : V) : degreeKernel G u v = degreeKernel G v u := by
  simp [degreeKernel,mul_comm]

theorem degreeKernel_nonneg (u v : V) : 0 ≤ degreeKernel G u v := by
  unfold degreeKernel; positivity

theorem degreeKernel_le_quarter (hd : ∀ v, 2 ≤ G.degree v) (u v : V) :
    degreeKernel G u v ≤ 1 / 4 := by
  have hu : (2 : ℝ) ≤ G.degree u := by exact_mod_cast hd u
  have hv : (2 : ℝ) ≤ G.degree v := by exact_mod_cast hd v
  unfold degreeKernel
  apply (div_le_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 4)).mpr
  nlinarith

theorem degreeKernel_row_le_half (hd : ∀ v, 2 ≤ G.degree v) (v : V) :
    (∑ u,if G.Adj v u then degreeKernel G v u else 0) ≤ 1 / 2 := by
  have hv : (2 : ℝ) ≤ G.degree v := by exact_mod_cast hd v
  have hvp : (0 : ℝ) < G.degree v := by linarith
  calc
    _ ≤ ∑ u,if G.Adj v u then 1 / (2 * (G.degree v : ℝ)) else 0 := by
      apply Finset.sum_le_sum
      intro u _
      split_ifs
      · have hu : (2 : ℝ) ≤ G.degree u := by exact_mod_cast hd u
        unfold degreeKernel
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        nlinarith
      · rfl
    _ = (G.degree v : ℝ) * (1 / (2 * (G.degree v : ℝ))) := by
      rw [G.degree_eq_sum_if_adj (R := ℝ) v,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro u _
      split_ifs <;> simp
    _ = 1 / 2 := by field_simp

def fractionalOrientedWeight (e : OrientedEdges G) : ℝ :=
  (9 / 10 : ℝ) * degreeKernel G e.val.1 e.val.2

theorem fractionalOrientedWeight_nonneg (e : OrientedEdges G) :
    0 ≤ fractionalOrientedWeight G e :=
  mul_nonneg (by norm_num) (degreeKernel_nonneg G _ _)

theorem fractionalOrientedWeight_degree (hd : ∀ v, 2 ≤ G.degree v) (v : V) :
    (orientedLoopless G).degree (fractionalOrientedWeight G) v ≤ 9 / 10 := by
  unfold fractionalOrientedWeight
  rw [oriented_degree G (fun u w => (9 / 10 : ℝ) * degreeKernel G u w) v]
  have hi (u : V) :
      (if G.Adj u v then (9 / 10 : ℝ) * degreeKernel G u v else 0) =
      (if G.Adj v u then (9 / 10 : ℝ) * degreeKernel G v u else 0) := by
    by_cases huv : G.Adj u v
    · simp [huv,huv.symm,degreeKernel_symm G u v]
    · have hvu : ¬G.Adj v u := fun h => huv h.symm
      simp [huv,hvu]
  simp_rw [hi]
  have hh : (∑ u,if G.Adj v u then (9 / 10 : ℝ) * degreeKernel G v u else 0) =
      (9 / 10 : ℝ) * (∑ u,if G.Adj v u then degreeKernel G v u else 0) := by
    simp [Finset.mul_sum,mul_ite]
  rw [hh]
  have h := degreeKernel_row_le_half G hd v
  linarith

/-- The lower permanent estimate in the doubled-orientation convention. -/
theorem oriented_normalized_log_permanent_lower
    (A : Matrix V V ℝ) (hA : A.PosSemidef) (hd : ∀ v, A v v = 1)
    (hs : ∀ e : OrientedEdges G, (A e.val.1 e.val.2)^2 ≤ 1 / 4)
    (hx : OrdinaryFeasible (orientedLoopless G)
      (fun e => (9 / 10 : ℝ) * (A e.val.1 e.val.2)^2)) :
    (4 / 5 : ℝ) * (∑ e : OrientedEdges G, ((A e.val.1 e.val.2)^2)^2) ≤
      Real.log A.permanent := by
  apply le_trans _ (log_permanent_ge_fractional (orientedLoopless G) _ hx A hA hd)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have h := mul_le_mul_of_nonneg_left
    (log_one_add_ge_eight_ninths (sq_nonneg _) (hs e))
    (show 0 ≤ (9 / 10 : ℝ) * (A e.val.1 e.val.2)^2 by positivity)
  change (4 / 5 : ℝ) * ((A e.val.1 e.val.2)^2)^2 ≤
    (9 / 10 : ℝ) * (A e.val.1 e.val.2)^2 * Real.log (1 + (A e.val.1 e.val.2)^2)
  change (9 / 10 : ℝ) * (A e.val.1 e.val.2)^2 * ((8 / 9 : ℝ) *
    (A e.val.1 e.val.2)^2) ≤ _ at h
  nlinarith

end
end Chollet.Matching
