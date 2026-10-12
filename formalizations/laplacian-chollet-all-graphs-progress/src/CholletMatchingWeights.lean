import CholletInterfaces
import Mathlib.Data.Finset.SymmDiff

set_option autoImplicit false
open scoped BigOperators symmDiff
open OAI.MatchingEntropy

namespace Chollet
namespace Matching

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
noncomputable section

def IsOrdinaryMatching (G : LooplessGraph V E) (M : Finset E) : Prop :=
  ∀ v e f, e ∈ M → f ∈ M → G.Incident v e → G.Incident v f → e = f

abbrev OrdinaryMatching (G : LooplessGraph V E) := {M : Finset E // IsOrdinaryMatching G M}

def internalMass (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) : ℝ :=
  ∑ e, if G.left e ∈ S ∧ G.right e ∈ S then x e else 0

def OrdinaryFeasible (G : LooplessGraph V E) (x : E → ℝ) : Prop :=
  (∀ e, 0 ≤ x e) ∧ (∀ v, G.degree x v ≤ 1) ∧
    ∀ S : Finset V, Odd S.card → internalMass G x S ≤ ((S.card : ℝ) - 1) / 2

theorem weighted_incidence_sum (G : LooplessGraph V E) (x : E → ℝ)
    (e : E) (S : Finset V) :
    (∑ v ∈ S, if G.Incident v e then x e else 0) =
      (if G.left e ∈ S then x e else 0) + (if G.right e ∈ S then x e else 0) := by
  have hv : ∀ v, (if G.Incident v e then x e else 0) =
      (if v = G.left e then x e else 0) + (if v = G.right e then x e else 0) := by
    intro v
    by_cases hl : v = G.left e <;> by_cases hr : v = G.right e
    · exact ((G.loopless e) (hl.symm.trans hr)).elim
    · simp [LooplessGraph.Incident, hl, G.loopless e, Ne.symm (G.loopless e)]
    · simp [LooplessGraph.Incident, hr, G.loopless e, Ne.symm (G.loopless e)]
    · simp [LooplessGraph.Incident, Ne.symm hl, Ne.symm hr, hl, hr]
  simp_rw [hv, Finset.sum_add_distrib]
  simp

theorem cutMass_sum (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) :
    G.cutMass x S = ∑ e, if G.Crosses S e then x e else 0 := by
  simp [LooplessGraph.cutMass, LooplessGraph.cut, Finset.sum_filter]

theorem weighted_handshake (G : LooplessGraph V E) (x : E → ℝ) (S : Finset V) :
    (∑ v ∈ S, G.degree x v) = 2 * internalMass G x S + G.cutMass x S := by
  unfold LooplessGraph.degree
  rw [Finset.sum_comm]
  simp_rw [weighted_incidence_sum]
  rw [internalMass, cutMass_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;>
    simp [hl, hr, LooplessGraph.Crosses] <;> ring

theorem odd_cut_with_slack (G : LooplessGraph V E) (x : E → ℝ)
    (hx : OrdinaryFeasible G x) (S : Finset V) (hS : Odd S.card) :
    1 ≤ G.cutMass x S + ∑ v ∈ S, (1 - G.degree x v) := by
  have h := hx.2.2 S hS
  have he := weighted_handshake G x S
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith

theorem cutMass_symmDiff_le (G : LooplessGraph V E) (x : E → ℝ)
    (hx : ∀ e, 0 ≤ x e) (A B : Finset V) :
    G.cutMass x (A ∆ B) ≤ G.cutMass x A + G.cutMass x B := by
  simp only [cutMass_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro e he
  have hn := hx e
  by_cases hla : G.left e ∈ A <;> by_cases hra : G.right e ∈ A <;>
    by_cases hlb : G.left e ∈ B <;> by_cases hrb : G.right e ∈ B <;>
    simp [LooplessGraph.Crosses, Finset.mem_symmDiff, hla, hra, hlb, hrb, hn]

end
end Matching
end Chollet
