import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/- Scalar exports only: neither covers nor the published f(6) input
   are postulated or formalized in this project. -/
namespace RankSixTwenty

theorem degree_chord (d M : ℝ) (hd : 2 ≤ d) (hM : d ≤ M) :
    d*(d-1) ≤ 2+(M+1)*(d-2) := by
  have h := mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hM)
  nlinarith

theorem integer_codegree (b : ℤ) : 2*(b-1) ≤ b*(b-1) := by
  have hp : 0 ≤ (b-1)*(b-2) := by
    by_cases h : b ≤ 1
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
    · exact mul_nonneg (by omega) (by omega)
  nlinarith

theorem first_edge_budget (N : ℤ) (h : N-1 ≤ 6*(N-14)) : 17 ≤ N := by omega

theorem four_vertex_budget (U P : ℝ) (hl : 24-P ≤ U) (hu : U ≤ 16) : 8 ≤ P := by
  linarith

theorem summed_budget (P : ℝ) (h : 15*8 ≤ 6*P) : 20 ≤ P := by linarith

theorem selected_pair_budget (P Q : ℝ) (hP : 20 ≤ P) (hQ : P-15 ≤ Q) :
    5 ≤ Q := by linarith

theorem appendix_degree_chord (d : ℝ) (hd : 1 ≤ d) (hu : d ≤ 3) :
    d*(d-1) ≤ 3*(d-1) := by
  have hp := mul_nonneg (sub_nonneg.mpr hd) (sub_nonneg.mpr hu)
  nlinarith

theorem appendix_first_edge (N : ℤ) (h : N-1 ≤ 6*(N-9)) : 11 ≤ N := by omega

theorem appendix_equality (n x3 x4 S : ℝ) (hn : 30 ≤ n)
    (hx4 : x4 ≤ 6) (hx3 : x3 ≤ 18-2*x4)
    (hS : S = 72-n+x3+3*x4) (hl : 66 ≤ S) :
    n = 30 ∧ x3 = 6 ∧ x4 = 6 ∧ S = 66 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

#print axioms degree_chord
#print axioms integer_codegree
#print axioms first_edge_budget
#print axioms four_vertex_budget
#print axioms summed_budget
#print axioms selected_pair_budget
#print axioms appendix_degree_chord
#print axioms appendix_first_edge
#print axioms appendix_equality

end RankSixTwenty
