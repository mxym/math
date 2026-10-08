import Definitions
import Alpha

set_option maxHeartbeats 0
set_option maxRecDepth 10000

namespace EntropyCounterexample

noncomputable def A (x : ℝ) : ℝ := 11 * (1-x^10)^11 * P x
noncomputable def B (x : ℝ) : ℝ := 10 * (1-x^11)^11 * (Q x / 11)

theorem p_special (a x : ℝ) : p 11 10 a x = a * A x - B x := by
  rw [p, h_eleven_eleven, h_eleven_ten]
  norm_num [A, B]
  ring

theorem p_strictMono_parameter {x : ℝ} (hx : 0 < A x) :
    StrictMono (fun a : ℝ => p 11 10 a x) := by
  intro a b hab
  simp only [p_special]
  exact sub_lt_sub_right (mul_lt_mul_of_pos_right hab hx) _

theorem sample_one_fifth : 0 < p 11 10 alpha (1/5) := by
  have hA : 0 < A (1/5) := by norm_num [A, P]
  have hlo : 0 < p 11 10 (117/125) (1/5) := by
    rw [p_special]
    norm_num [A, B, P, Q]
  exact lt_trans hlo (p_strictMono_parameter hA alpha_lower)

theorem sample_two_fifths : p 11 10 alpha (2/5) < 0 := by
  have hA : 0 < A (2/5) := by norm_num [A, P]
  have hhi : p 11 10 (937/1000) (2/5) < 0 := by
    rw [p_special]
    norm_num [A, B, P, Q]
  exact lt_trans (p_strictMono_parameter hA alpha_upper) hhi

theorem sample_three_fifths : 0 < p 11 10 alpha (3/5) := by
  have hA : 0 < A (3/5) := by norm_num [A, P]
  have hlo : 0 < p 11 10 (117/125) (3/5) := by
    rw [p_special]
    norm_num [A, B, P, Q]
  exact lt_trans hlo (p_strictMono_parameter hA alpha_lower)

theorem sample_two_thirds : p 11 10 alpha (2/3) < 0 := by
  have hA : 0 < A (2/3) := by norm_num [A, P]
  have hhi : p 11 10 (937/1000) (2/3) < 0 := by
    rw [p_special]
    norm_num [A, B, P, Q]
  exact lt_trans (p_strictMono_parameter hA alpha_upper) hhi

theorem sample_four_fifths : 0 < p 11 10 alpha (4/5) := by
  have hA : 0 < A (4/5) := by norm_num [A, P]
  have hlo : 0 < p 11 10 (117/125) (4/5) := by
    rw [p_special]
    norm_num [A, B, P, Q]
  exact lt_trans hlo (p_strictMono_parameter hA alpha_lower)

end EntropyCounterexample
