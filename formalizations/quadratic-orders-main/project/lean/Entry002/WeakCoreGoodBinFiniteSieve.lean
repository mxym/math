import Entry002.WeakCoreGoodBinWindowMass
import Entry002.WeakSieveTargets

/-! A1--A4 and the genuine fixed-density logarithmic good-bin supply imply
the actual finite sieve. The selections use the literal integer base, original
windows, one globally thinned bin family, and the single common-window law.
The Dirichlet-to-good-bin implication remains an explicit premise in the final
conditional Dirichlet corollary; it is not asserted in this module. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Entry002.WeakA5
open Module Filter
open scoped BigOperators Classical Topology
variable {L : Type*} [AddCommGroup L]

/-- Cofinal harmonic good bins choose actual windows with aggregate rate
exceeding the finite step-alphabet budget. Empty windows are permitted. -/
theorem good_bin_selected_window_rate_excess
    (data : SignedResidueData L) (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (D a δ β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (K : ℕ) (hK : 0 < K)
    (hsupply : ∀ J₀ : ℕ, ∃ J : ℕ, max J₀ 2 ≤ J ∧
      β * Real.log (J : ℝ) ≤ ∑ j ∈ goodDyadicBins data.primes δ J, 1 / ((j : ℝ) + 1)) :
    ∃ W : ℕ, CofinalSelectedWindowRateExcess data b e D a δ K W := by
  let c : ℝ := topCoefficient a/4
  have hc : 0 < c := div_pos (topCoefficient_pos ha) (by norm_num)
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  let R : ℝ := (c/10000000)*(β/(2*(K : ℝ)))
  have hR : 0 < R := by dsimp only [R]; positivity
  obtain ⟨q, hq⟩ := exists_nat_gt ((Real.log (wordStepBall b e D).card+1)/R)
  have htarget : Real.log (wordStepBall b e D).card+1 < (q : ℝ)*R :=
    (div_lt_iff₀ hR).mp hq
  refine ⟨196*q, ?_⟩
  intro M
  obtain ⟨m, hm, atoms, hatoms, hmass⟩ :=
    cofinal_good_bin_window_mass data.primes δ β hβ hsupply q M
  let coord : ℕ → ℝ := fun j => Real.log ((j : ℝ)*Real.log 2)
  let weight : ℕ → ℝ := fun j => 1/((j : ℝ)+1)
  let B : Finset ℕ := (Finset.range (196*q)).biUnion
    (weakWindowSelectedBins atoms coord m)
  obtain ⟨r, _, hthinmass, hthinsep⟩ := independent_weighted_thin_bins B weight hK
  let T : Finset ℕ := B.filter (fun j => j % K = r)
  let J : ℕ → Finset ℕ := fun w => T.filter (fun j => weakWindowCatches (coord j) m w)
  have hBatom : ∀ j ∈ B, j ∈ atoms := by
    intro j hj
    obtain ⟨w, _, hjw⟩ := Finset.mem_biUnion.mp hj
    exact (Finset.mem_filter.mp hjw).1
  have hJatom : ∀ w, ∀ j ∈ J w, j ∈ atoms := by
    intro w j hj
    exact hBatom j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1
  have hunion : allBins (196*q) J = T := by
    ext j
    constructor
    · intro hj
      obtain ⟨w, _, hjw⟩ := Finset.mem_biUnion.mp hj
      exact (Finset.mem_filter.mp hjw).1
    · intro hj
      obtain ⟨w, hw, hjw⟩ := Finset.mem_biUnion.mp (Finset.mem_filter.mp hj).1
      exact Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_filter.mpr
        ⟨hj, (Finset.mem_filter.mp hjw).2⟩⟩
  have hfull : ∀ w < 196*q, ∀ j ∈ J w,
      (100:ℝ)^w*Real.exp m ≤ (j:ℝ)*Real.log 2 ∧
      (j:ℝ)*Real.log 2 ≤ 21/20*((100:ℝ)^w*Real.exp m) ∧
      δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1)) ≤ (dyadicPrimeBatch data.primes j).card := by
    intro w _ j hj
    have ha := hatoms j (hJatom w j hj)
    have hjpos : 0 < j := by omega
    have hwindow := (weakWindow_catches_log_bin_iff hjpos m w).mp
      (Finset.mem_filter.mp hj).2
    exact ⟨hwindow.1, hwindow.2, ha.2⟩
  have hsep : ∀ i ∈ allBins (196*q) J, ∀ j ∈ allBins (196*q) J,
      i < j → i+K ≤ j := by
    rw [hunion]
    exact hthinsep
  have hmassB : (q : ℝ)*β/2 ≤ ∑ j ∈ B, weight j := by
    rw [weakWindow_finite_mass_eq_union] at hmass
    exact hmass
  have hthin : ((q : ℝ)*β/2)/(K : ℝ) ≤ ∑ j ∈ T, weight j :=
    (div_le_div_of_nonneg_right hmassB hKr.le).trans hthinmass
  have hrate : (c/10000000)*(∑ j ∈ T, weight j) ≤
      ∑ j ∈ T, windowBatchRate c j := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    apply harmonic_weight_le_windowBatchRate hc.le
    have hj2 := (hatoms j (hBatom j (Finset.mem_filter.mp hj).1)).1
    omega
  have hexcess : Real.log (wordStepBall b e D).card+1 <
      ∑ j ∈ allBins (196*q) J, windowBatchRate (topCoefficient a/4) j := by
    rw [hunion]
    calc
      _ < (q : ℝ)*R := htarget
      _ = (c/10000000)*(((q : ℝ)*β/2)/(K : ℝ)) := by
        dsimp only [R]
        field_simp
      _ ≤ (c/10000000)*(∑ j ∈ T, weight j) :=
        mul_le_mul_of_nonneg_left hthin (by positivity)
      _ ≤ _ := hrate
  exact ⟨m, hm, J, hfull, hsep, hexcess⟩

/-- The genuine good-bin supply closes the core sieve with the literal `Q²`
component bound. All finite pool, geometry, charge, and law choices are proved. -/
theorem core_finite_sieve_of_log_good_bins
    {data : SignedResidueData L} {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} (A : ArithmeticCore data b e)
    (hsupply : PositiveUpperLogGoodBinSupply data.primes) :
    ∀ D : ℝ, 0 ≤ D → ∃ S : Finset ℕ,
      (∀ p ∈ S, p ∈ data.primes) ∧
      UniformComponentBound (latticeGraph b e D (avoiding data S)) (S.prod id ^ 2) := by
  obtain ⟨δ, hδ, β, hβ, hbins⟩ := hsupply
  obtain ⟨a, K, ha, ha1, haδ, hK, hgap, hcost⟩ := exists_window_gap_parameters hδ
  apply core_finite_sieve_of_selected_windows A
  intro D _
  obtain ⟨W, hselection⟩ := good_bin_selected_window_rate_excess data b e D a δ β
    ha hβ K hK hbins
  exact ⟨a, δ, K, W, ha, ha1, haδ, hK, hgap, hcost, hselection⟩

/-- A single explicit analytic bridge suffices to turn the proved good-bin
sieve into the new weak Dirichlet target. This theorem does not claim that
bridge, the new weak target, or the literal MainTarget unconditionally. -/
theorem weak_finite_sieve_of_dirichlet_good_bin_bridge
    (hbridge : ∀ P : Set ℕ, (∀ p ∈ P, Nat.Prime p) →
      PositiveUpperDirichletSupply P → PositiveUpperLogGoodBinSupply P) : WeakFiniteSieveTarget := by
  intro L _ b e data A
  exact core_finite_sieve_of_log_good_bins A.core (hbridge data.primes data.prime_mem A.upper_dirichlet_supply)

end Entry002.WeakA5
