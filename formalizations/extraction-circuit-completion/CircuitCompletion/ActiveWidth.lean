import CircuitCompletion.OccupationRecurrence
import Mathlib.Data.Nat.Log

open SymmetricSupport
namespace CircuitCompletion

def occupationRank (j : ℕ) : ℕ := (j+3).choose 3

theorem occupationRank_actual (j : ℕ) :
    (symmetricProjector 4 j).rank=occupationRank j := by
  simpa [occupationRank,Nat.add_sub_assoc] using
    symmetricProjector_rank_choose_complement 4 j (by decide)

theorem occupationRank_card (j : ℕ) : Fintype.card (Sym (Fin 4) j)=occupationRank j := by
  rw [← occupationRank_actual,SymmetricSupport.symmetricProjector,
    partitionProjector_rank _ (occupation_surjective 4 j)]

theorem occupationRank_pos (j : ℕ) : 0<occupationRank j := Nat.choose_pos (by omega)

theorem occupationRank_le_power (j : ℕ) : occupationRank j≤4^j := by
  rw [← occupationRank_actual]
  exact (Matrix.rank_le_card_width _).trans_eq (by simp [Word,Fintype.card_pi_const])

theorem occupationRank_step (j : ℕ) : occupationRank (j+1)≤4*occupationRank j := by
  have hs : Function.Surjective (fun p : Fin 4×Sym (Fin 4) j => Sym.cons p.1 p.2) := by
    intro ν
    obtain ⟨i,mu,h⟩ := Sym.exists_eq_cons_of_succ ν
    exact ⟨(i,mu),h.symm⟩
  have h := Fintype.card_le_of_surjective _ hs
  simpa only [Fintype.card_prod,Fintype.card_fin,occupationRank_card] using h

def encodingPairs (j : ℕ) : ℕ := Nat.clog 4 (occupationRank j)

theorem encodingPairs_le_copy (j : ℕ) : encodingPairs j≤j :=
  Nat.clog_le_of_le_pow (occupationRank_le_power j)

theorem encodingPairs_step (j : ℕ) : encodingPairs (j+1)≤encodingPairs j+1 := by
  apply Nat.clog_le_of_le_pow
  calc
    occupationRank (j+1)≤4*occupationRank j := occupationRank_step j
    _ ≤ 4*(4^encodingPairs j) := Nat.mul_le_mul_left _ (Nat.le_pow_clog (by decide) _)
    _ = 4^(encodingPairs j+1) := by rw [Nat.pow_succ];omega

theorem pow_clog_le_four_mul (r : ℕ) (hr : 0<r) : 4^Nat.clog 4 r≤4*r := by
  by_cases h : r≤1
  · have he : r=1 := by omega
    simp [he]
  · have hr' : 1<r := by omega
    have hc : 0<Nat.clog 4 r := Nat.clog_pos (by decide) hr'
    have hp := Nat.pow_pred_clog_lt_self (by decide : 1<4) hr'
    have he : Nat.clog 4 r=(Nat.clog 4 r-1)+1 := by omega
    rw [Nat.pred_eq_sub_one] at hp
    rw [he,Nat.pow_succ]
    nlinarith

def activeWires (j : ℕ) : ℕ := 2*(encodingPairs j+1)

theorem activeWires_available (j : ℕ) : activeWires j≤2*(j+1) := by
  have h := encodingPairs_le_copy j
  unfold activeWires
  omega

theorem activeDimension_bound (j : ℕ) : 2^activeWires j≤16*occupationRank j := by
  have hp := pow_clog_le_four_mul (occupationRank j) (occupationRank_pos j)
  change 2^(2*(encodingPairs j+1))≤_
  rw [Nat.pow_mul]
  change 4^(encodingPairs j+1)≤_
  rw [Nat.pow_succ]
  change 4^(Nat.clog 4 (occupationRank j))*4≤_
  nlinarith

theorem encodingPairs_log_bound (j : ℕ) : encodingPairs j≤3*Nat.clog 2 (j+3) := by
  apply (Nat.clog_anti_left (by decide : 1<2) (by decide : 2≤4)).trans
  apply Nat.clog_le_of_le_pow
  calc
    occupationRank j≤(j+3)^3 := Nat.choose_le_pow _ _
    _ ≤ (2^Nat.clog 2 (j+3))^3 := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _
    _ = 2^(3*Nat.clog 2 (j+3)) := by rw [Nat.mul_comm 3,Nat.pow_mul]

theorem activeWires_log_bound (j : ℕ) : activeWires j≤6*Nat.clog 2 (j+3)+2 := by
  have h := encodingPairs_log_bound j
  unfold activeWires
  omega

theorem activeDimension_polynomial (j : ℕ) : 2^activeWires j≤16*(j+3)^3 :=
  (activeDimension_bound j).trans (Nat.mul_le_mul_left _ (Nat.choose_le_pow _ _))

end CircuitCompletion
