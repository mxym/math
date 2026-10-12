import CofactorSharpLower
import CofactorUpperMain

/-! Sharp logarithmic limits for the unrestricted and exact-rank-two variational problems. -/
set_option autoImplicit false
open scoped Topology
open Filter
namespace CofactorSpectral
noncomputable section

theorem tendsto_of_eventual_two_sided_bounds (f : ℕ → ℝ) (a : ℝ)
    (hl : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, a-ε ≤ f n)
    (hu : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, f n ≤ a+ε) :
    Tendsto f atTop (𝓝 a) := by
  apply tendsto_order.2
  constructor
  · intro l hla
    obtain ⟨N,hN⟩ := hl ((a-l)/2) (by linarith)
    apply eventually_atTop.2
    refine ⟨N,?_⟩
    intro n hn
    have h := hN n hn
    linarith
  · intro u hau
    obtain ⟨N,hN⟩ := hu ((u-a)/2) (by linarith)
    apply eventually_atTop.2
    refine ⟨N,?_⟩
    intro n hn
    have h := hN n hn
    linarith

theorem complexExtremum_log_tendsto :
    Tendsto (fun N : ℕ => complexExtremum N/Real.log (N : ℝ)) atTop (𝓝 1) := by
  apply tendsto_of_eventual_two_sided_bounds
  · intro ε hε
    obtain ⟨N,hN⟩ := four_extrema_eventual_sharp_log_lower ε hε
    exact ⟨N,fun n hn => (hN n hn).1⟩
  · exact complexExtremum_eventual_log_upper

theorem realExtremum_log_tendsto :
    Tendsto (fun N : ℕ => realExtremum N/Real.log (N : ℝ)) atTop (𝓝 (1/2)) := by
  apply tendsto_of_eventual_two_sided_bounds
  · intro ε hε
    obtain ⟨N,hN⟩ := four_extrema_eventual_sharp_log_lower ε hε
    exact ⟨N,fun n hn => (hN n hn).2.1⟩
  · exact realExtremum_eventual_log_upper

theorem rankTwoComplexExtremum_log_tendsto :
    Tendsto (fun N : ℕ => rankTwoComplexExtremum N/Real.log (N : ℝ)) atTop (𝓝 1) := by
  apply tendsto_of_eventual_two_sided_bounds
  · intro ε hε
    obtain ⟨N,hN⟩ := four_extrema_eventual_sharp_log_lower ε hε
    exact ⟨N,fun n hn => (hN n hn).2.2.1⟩
  · exact rankTwoComplexExtremum_eventual_log_upper

theorem rankTwoRealExtremum_log_tendsto :
    Tendsto (fun N : ℕ => rankTwoRealExtremum N/Real.log (N : ℝ)) atTop (𝓝 (1/2)) := by
  apply tendsto_of_eventual_two_sided_bounds
  · intro ε hε
    obtain ⟨N,hN⟩ := four_extrema_eventual_sharp_log_lower ε hε
    exact ⟨N,fun n hn => (hN n hn).2.2.2⟩
  · exact rankTwoRealExtremum_eventual_log_upper

end
end CofactorSpectral
