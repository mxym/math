import EntropyWakhare.Core
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp

namespace EntropyRoot

private def g (z : ℝ) : ℝ := z^10*(1+z)

private lemma g_continuous : Continuous g := by
  unfold g
  fun_prop

private lemma g_below : g (117/125) < 1 := by
  norm_num [g]

private lemma g_above : 1 < g (937/1000) := by
  norm_num [g]

theorem alpha_exists :
    ∃ α : ℝ, 117/125 < α ∧ α < 937/1000 ∧ g α = 1 := by
  have hlt : (117/125 : ℝ) ≤ 937/1000 := by norm_num
  have hlo : (117/125 : ℝ) ∈ Set.Icc (117/125 : ℝ) (937/1000 : ℝ) :=
    ⟨le_rfl,hlt⟩
  have hhi : (937/1000 : ℝ) ∈ Set.Icc (117/125 : ℝ) (937/1000 : ℝ) :=
    ⟨hlt,le_rfl⟩
  obtain ⟨α,hα,hroot⟩ :=
    (isPreconnected_Icc).intermediate_value₂ hlo hhi
      g_continuous.continuousOn continuousOn_const
      (le_of_lt g_below) (le_of_lt g_above)
  rcases hα with ⟨hl,hu⟩
  have hs : (117/125 : ℝ) < α := by
    rcases lt_or_eq_of_le hl with h | h
    · exact h
    · rw [←h] at hroot
      linarith [g_below]
  have ht : α < (937/1000 : ℝ) := by
    rcases lt_or_eq_of_le hu with h | h
    · exact h
    · rw [h] at hroot
      linarith [g_above]
  exact ⟨α,hs,ht,hroot⟩

private lemma g_strict (a b : ℝ) (ha : 0 ≤ a) (hab : a < b) :
    g a < g b := by
  have hb : 0 < b := lt_of_le_of_lt ha hab
  have hp : a^10 < b^10 := by
    exact pow_lt_pow_left₀ hab ha (by norm_num)
  unfold g
  calc
    a^10*(1+a) < b^10*(1+a) :=
      mul_lt_mul_of_pos_right hp (by linarith)
    _ ≤ b^10*(1+b) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)

theorem alpha_positive_unique (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hga : g a = 1) (hgb : g b = 1) : a=b := by
  rcases lt_trichotomy a b with h | h | h
  · have hp := g_strict a b ha.le h
    rw [hga,hgb] at hp
    exact (False.elim (lt_irrefl _ hp))
  · exact h
  · have hp := g_strict b a hb.le h
    rw [hga,hgb] at hp
    exact (False.elim (lt_irrefl _ hp))

noncomputable def alpha : ℝ := Classical.choose alpha_exists

theorem alpha_interval :
    117/125 < alpha ∧ alpha < 937/1000 ∧ alpha^10*(1+alpha)=1 :=
  Classical.choose_spec alpha_exists

theorem alpha_is_unique (z : ℝ) (hz : 0 < z)
    (hroot : z^10*(1+z)=1) : z=alpha := by
  exact alpha_positive_unique z alpha hz (by
    have h := alpha_interval.1
    norm_num at h
    linarith) hroot alpha_interval.2.2

end EntropyRoot
