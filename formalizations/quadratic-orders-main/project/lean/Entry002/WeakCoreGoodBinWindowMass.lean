import Entry002.WeakSupplyInterfaces
import Entry002.WeakSupplyWindowAveraging
import Entry002.WeakCoreWindowRates

/-! Cofinal logarithmic good-bin mass supplies cofinal actual integer window
bases. All finite truncation losses and ceiling endpoints are proved here.
The fixed 196-block window average is the separately checked finite lemma. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Entry002.WeakA5
open Filter
open scoped BigOperators Classical Topology

/-- Good bins beyond a fixed finite margin yield an actual base `m ≥ M`
with aggregate caught harmonic weight at least `q*β/2`. -/
theorem cofinal_good_bin_window_mass
    (P : Set ℕ) (δ β : ℝ) (hβ : 0 < β)
    (hsupply : ∀ J₀ : ℕ, ∃ J : ℕ, max J₀ 2 ≤ J ∧
      β * Real.log (J : ℝ) ≤ ∑ j ∈ goodDyadicBins P δ J, 1 / ((j : ℝ) + 1))
    (q M : ℕ) :
    ∃ m : ℕ, M ≤ m ∧ ∃ atoms : Finset ℕ,
      (∀ j ∈ atoms, 2 ≤ j ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1)) ≤ (dyadicPrimeBatch P j).card) ∧
      (q : ℝ)*β/2 ≤ weakWindowFiniteMass atoms
        (fun j => Real.log ((j : ℝ)*Real.log 2))
        (fun j => 1/((j : ℝ)+1)) q m := by
  let H : ℝ := (M : ℝ) + ((196*q : ℕ) : ℝ)*Real.log 100 + Real.log (21/20 : ℝ)
  have hlpos : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlle : Real.log (2 : ℝ) ≤ 1 := by
    simpa only [show (2 : ℝ)-1=1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hH : (M : ℝ) ≤ H := by
    have hL := weakSupplyWindow_log100_bounds.1
    have hh := independent_weak_window_log_width_lower
    have hq : (0 : ℝ) ≤ (196*q : ℕ) := Nat.cast_nonneg _
    dsimp only [H]
    nlinarith only [hL, hh, hq]
  obtain ⟨cut, hcut⟩ := exists_nat_ge (max 2 (Real.exp H/Real.log 2))
  have hcut2 : 2 ≤ cut := by exact_mod_cast (le_max_left _ _).trans hcut
  have hcutexp : Real.exp H ≤ (cut : ℝ)*Real.log 2 :=
    (div_le_iff₀ hlpos).mp ((le_max_right _ _).trans hcut)
  have hmargin {j : ℕ} (hj : cut ≤ j) : H ≤ Real.log ((j : ℝ)*Real.log 2) := by
    have hj' : (cut : ℝ) ≤ j := by exact_mod_cast hj
    have hh := Real.log_le_log (Real.exp_pos H)
      (hcutexp.trans (mul_le_mul_of_nonneg_right hj' hlpos.le))
    simpa only [Real.log_exp] using hh
  let C : ℝ := ∑ j ∈ Finset.range cut, 1/((j : ℝ)+1)
  have ht : Tendsto (fun j : ℕ => Real.log (j : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨J₀, hJ₀⟩ := eventually_atTop.mp
    (ht.eventually (eventually_ge_atTop (2*(C+β)/β)))
  obtain ⟨J, hJ, hmass⟩ := hsupply (max J₀ cut)
  have hJcut : cut ≤ J := (le_max_right J₀ cut).trans ((le_max_left _ _).trans hJ)
  have hJ0 : J₀ ≤ J := (le_max_left J₀ cut).trans ((le_max_left _ _).trans hJ)
  have hJ2 : 2 ≤ J := (le_max_right _ _).trans hJ
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hlarge : 2*(C+β) ≤ β*Real.log (J : ℝ) := by
    simpa only [mul_comm] using (div_le_iff₀ hβ).mp (hJ₀ J hJ0)
  let atoms := (goodDyadicBins P δ J).filter (fun j => cut ≤ j)
  have hatoms : ∀ j ∈ atoms, 2 ≤ j ∧
      δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1)) ≤ (dyadicPrimeBatch P j).card := by
    intro j hj
    have hg := (Finset.mem_filter.mp ((Finset.mem_filter.mp hj).1)).2
    exact ⟨hcut2.trans (Finset.mem_filter.mp hj).2, hg⟩
  have hother : (∑ j ∈ (goodDyadicBins P δ J).filter (fun j => ¬cut ≤ j),
      1/((j : ℝ)+1)) ≤ C := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj
      exact Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hj).2; omega)
    · intro j _ _
      positivity
  have hsplit := Finset.sum_filter_add_sum_filter_not (goodDyadicBins P δ J)
    (fun j => cut ≤ j) (fun j => (1 : ℝ)/((j : ℝ)+1))
  have hmass' : β/2*(Real.log (J : ℝ)+2) ≤ ∑ j ∈ atoms, 1/((j : ℝ)+1) := by
    dsimp only [atoms]
    nlinarith only [hmass, hother, hsplit, hlarge]
  let N : ℕ := ⌈Real.log ((J : ℝ)*Real.log 2)⌉₊
  have hcoord0 : 0 ≤ Real.log ((J : ℝ)*Real.log 2) :=
    (Nat.cast_nonneg M).trans (hH.trans (hmargin hJcut))
  have hcoord_le_N : Real.log ((J : ℝ)*Real.log 2) ≤ (N : ℝ) := Nat.le_ceil _
  have hMN : M ≤ N := by
    exact_mod_cast hH.trans ((hmargin hJcut).trans hcoord_le_N)
  have hcoord_le_log : Real.log ((J : ℝ)*Real.log 2) ≤ Real.log (J : ℝ) := by
    apply Real.log_le_log (mul_pos hJpos hlpos)
    nlinarith only [hJpos, hlle]
  have hN : (N : ℝ) ≤ Real.log (J : ℝ)+1 :=
    (Nat.ceil_lt_add_one hcoord0).le.trans (by linarith only [hcoord_le_log])
  have hden : ((N-M+1 : ℕ) : ℝ) ≤ Real.log (J : ℝ)+2 := by
    have hsub : ((N-M : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N M
    push_cast
    linarith only [hsub, hN]
  have hdenpos : (0 : ℝ) < ((N-M+1 : ℕ) : ℝ) := by positivity
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hmassden : β/2*((N-M+1 : ℕ) : ℝ) ≤ ∑ j ∈ atoms, 1/((j : ℝ)+1) :=
    (mul_le_mul_of_nonneg_left hden (by positivity : 0 ≤ β/2)).trans hmass'
  have havglower : (q : ℝ)*β/2 ≤
      ((q : ℝ)*∑ j ∈ atoms, 1/((j : ℝ)+1))/((N-M+1 : ℕ) : ℝ) := by
    apply (le_div_iff₀ hdenpos).mpr
    have hh := mul_le_mul_of_nonneg_left hmassden hq0
    nlinarith only [hh]
  obtain ⟨m, hm, _, havg⟩ := weakWindow_finite_average atoms
    (fun j => Real.log ((j : ℝ)*Real.log 2))
    (fun j => 1/((j : ℝ)+1)) q M N hMN
    (fun j _ => by positivity)
    (fun j hj => hmargin (Finset.mem_filter.mp hj).2)
    (by
      intro j hj
      have hjJ : j ≤ J := (Finset.mem_Icc.mp
        ((Finset.mem_filter.mp ((Finset.mem_filter.mp hj).1)).1)).2
      have hjpos : (0 : ℝ) < j := by
        exact_mod_cast (show 0 < j by have := (hatoms j hj).1; omega)
      exact (Real.log_le_log (mul_pos hjpos hlpos)
        (mul_le_mul_of_nonneg_right (by exact_mod_cast hjJ) hlpos.le)).trans hcoord_le_N)
  exact ⟨m, hm, atoms, hatoms, havglower.trans havg⟩

end Entry002.WeakA5
