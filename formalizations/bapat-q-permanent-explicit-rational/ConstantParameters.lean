import DefinitionBridge

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BapatExplicit

def gamma : ℕ := 19900 * Nat.factorial 200 * 200 * 1601 ^ 199
def secondBound : ℕ := 19900 * 19899 * Nat.factorial 200 * 1601 ^ 200
def epsilon : ℚ := 1 / (4 * (gamma : ℚ))
def intervalLength : ℚ := 1 / (8 * (secondBound : ℚ))
def q0 : ℚ := 1 - intervalLength

theorem cast_triple_pow (a b c d e : ℕ) :
    ((a * b * c * d ^ e : ℕ) : ℝ) =
      (a : ℝ) * (b : ℝ) * (c : ℝ) * (d : ℝ) ^ e := by
  simp only [Nat.cast_mul, Nat.cast_pow]

theorem gamma_cast : (gamma : ℝ) =
    (Nat.choose 200 2 : ℝ) * (Nat.factorial 200 : ℝ) * ((200 : ℕ) : ℝ) *
      ((1600 : ℝ) + 1) ^ (200 - 1 : ℕ) := by
  have hn : Nat.choose 200 2 = 19900 := by norm_num [Nat.choose_two_right]
  calc
    _ = (19900 : ℝ) * (Nat.factorial 200 : ℝ) * 200 * (1601 : ℝ) ^ (199 : ℕ) :=
      cast_triple_pow 19900 (Nat.factorial 200) 200 1601 199
    _ = _ := by rw [hn, show (1600 : ℝ) + 1 = 1601 by norm_num]; rfl

theorem secondBound_cast : (secondBound : ℝ) =
    (Nat.choose 200 2 : ℝ) * ((Nat.choose 200 2 - 1 : ℕ) : ℝ) *
      (Nat.factorial 200 : ℝ) * ((1600 : ℝ) + 1) ^ (200 : ℕ) := by
  have hn : Nat.choose 200 2 = 19900 := by norm_num [Nat.choose_two_right]
  calc
    _ = (19900 : ℝ) * 19899 * (Nat.factorial 200 : ℝ) * (1601 : ℝ) ^ (200 : ℕ) :=
      cast_triple_pow 19900 19899 (Nat.factorial 200) 1601 200
    _ = _ := by rw [hn, show (1600 : ℝ) + 1 = 1601 by norm_num]; rfl

theorem epsilon_cast : (epsilon : ℝ) = 1 / (4 * (gamma : ℝ)) := by
  simp only [epsilon, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]

theorem intervalLength_cast : (intervalLength : ℝ) = 1 / (8 * (secondBound : ℝ)) := by
  simp only [intervalLength, Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_natCast]

theorem q0_cast : (q0 : ℝ) = 1 - 1 / (8 * (secondBound : ℝ)) := by
  simp only [q0, Rat.cast_sub, Rat.cast_one, intervalLength_cast]

theorem q0_complex_cast : ((q0 : ℝ) : ℂ) = (q0 : ℂ) := by norm_cast

theorem epsilon_positive : (0 : ℚ) < epsilon := by
  have hf : 0 < Nat.factorial 200 := Nat.factorial_pos 200
  have hg : 0 < gamma := by unfold gamma; positivity
  unfold epsilon
  positivity

theorem intervalLength_positive : (0 : ℚ) < intervalLength := by
  have hf : 0 < Nat.factorial 200 := Nat.factorial_pos 200
  have hk : 0 < secondBound := by unfold secondBound; positivity
  unfold intervalLength
  positivity

end BapatExplicit
