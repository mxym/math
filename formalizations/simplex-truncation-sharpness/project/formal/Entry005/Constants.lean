import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

noncomputable section

namespace Entry005

def R0 (d : ℕ) : ℝ := (d : ℝ) * (d + 1)
def b (d : ℕ) : ℝ := 1 / (4 * ((d : ℝ) * R0 d) ^ d)
def M (d : ℕ) : ℝ := 1 / b d
-- b^(-4d) is written as M^(4d), an exactly equivalent rational expression.
def Q (d : ℕ) : ℝ := (d + 1) * (d + 2) * (8 : ℝ) ^ d * M d ^ (4 * d)
def L (d : ℕ) : ℝ := (d - 1 : ℕ) * (M d + 1)
def J (d : ℕ) : ℝ := (d : ℝ) / 2 * (2 * R0 d) ^ d *
  (1 + M d + (d : ℝ) * (2 : ℝ) ^ (d - 1) * M d)
def rSharp (d : ℕ) : ℝ := min (b d) (1 / (J d * (8 * M d * d * L d) ^ (d - 1)))
def eSharp (d : ℕ) : ℝ := rSharp d / (Q d * (d + 1))
def aSharp (d : ℕ) : ℝ := 4 * M d * d * L d *
  (J d * Q d * (d + 1)) ^ (1 / ((d - 1 : ℕ) : ℝ))
def gSharp (d : ℕ) : ℝ := max (aSharp d)
  ((R0 d - 1) * (eSharp d) ^ (-(1 / ((d - 1 : ℕ) : ℝ))))

theorem R0_pos {d : ℕ} (hd : 1 ≤ d) : 0 < R0 d := by
  have : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  unfold R0
  positivity

theorem b_pos {d : ℕ} (hd : 1 ≤ d) : 0 < b d := by
  have : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have := R0_pos hd
  unfold b
  positivity

theorem M_pos {d : ℕ} (hd : 1 ≤ d) : 0 < M d := by
  unfold M
  exact one_div_pos.mpr (b_pos hd)

theorem Q_pos {d : ℕ} (hd : 1 ≤ d) : 0 < Q d := by
  have := M_pos hd
  unfold Q
  positivity

theorem L_pos {d : ℕ} (hd : 2 ≤ d) : 0 < L d := by
  have hm : 0 < d - 1 := by omega
  have := M_pos (le_trans (by decide : 1 ≤ 2) hd)
  unfold L
  positivity

theorem J_pos {d : ℕ} (hd : 1 ≤ d) : 0 < J d := by
  have : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd)
  have := R0_pos hd
  have := M_pos hd
  unfold J
  positivity

theorem rSharp_pos {d : ℕ} (hd : 2 ≤ d) : 0 < rSharp d := by
  have hd1 : 1 ≤ d := le_trans (by decide : 1 ≤ 2) hd
  have : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
  have := b_pos hd1
  have := J_pos hd1
  have := M_pos hd1
  have := L_pos hd
  unfold rSharp
  positivity

theorem eSharp_pos {d : ℕ} (hd : 2 ≤ d) : 0 < eSharp d := by
  have := rSharp_pos hd
  have := Q_pos (le_trans (by decide : 1 ≤ 2) hd)
  unfold eSharp
  positivity

theorem aSharp_pos {d : ℕ} (hd : 2 ≤ d) : 0 < aSharp d := by
  have hd1 : 1 ≤ d := le_trans (by decide : 1 ≤ 2) hd
  have : 0 < (d : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hd1)
  have := M_pos hd1
  have := J_pos hd1
  have := Q_pos hd1
  have := L_pos hd
  unfold aSharp
  positivity

theorem gSharp_pos {d : ℕ} (hd : 2 ≤ d) : 0 < gSharp d := by
  exact lt_of_lt_of_le (aSharp_pos hd) (le_max_left _ _)

end Entry005
