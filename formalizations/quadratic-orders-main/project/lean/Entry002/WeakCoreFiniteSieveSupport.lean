import Entry002.WeakCoreCommonWindowCharge
import Entry002.GenericFiniteSieveEngine

/-! A core-only finite sieve support theorem. The actual cofinal bin selection
is a visible hypothesis. This module proves no unconditional weak-supply or
literal MainTarget result. The finite induction and telescope use the existing
closed same-law engine, with the new A1--A4 common-window local charge.
Bookkeeping is adapted from the round-five owned GenericFiniteSieveEngine;
its OpenAI family028 source provenance and Apache-2.0 license are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Entry002.WeakA5
open Filter Module OAI.GaussianMoat
open scoped BigOperators Classical Topology
variable {L : Type*} [AddCommGroup L]

/-- Cofinal actual windows with enough aggregate rate. It permits empty
individual windows, retaining the literal integer `m`, windows, and prime bins.
The finite pool is chosen before any walk is quantified. -/
def CofinalSelectedWindowRateExcess
    (data : SignedResidueData L) (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (D a δ : ℝ) (K W : ℕ) : Prop :=
  ∀ m₀ : ℕ, ∃ m : ℕ, m₀ ≤ m ∧ ∃ J : ℕ → Finset ℕ,
    (∀ w < W, ∀ j ∈ J w,
      (100:ℝ)^w*Real.exp m ≤ (j:ℝ)*Real.log 2 ∧
      (j:ℝ)*Real.log 2 ≤ 21/20*((100:ℝ)^w*Real.exp m) ∧
      δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1)) ≤ (dyadicPrimeBatch data.primes j).card) ∧
    (∀ i ∈ allBins W J, ∀ j ∈ allBins W J, i < j → i+K ≤ j) ∧
    Real.log (wordStepBall b e D).card+1 <
      ∑ j ∈ allBins W J, windowBatchRate (topCoefficient a/4) j

/-- Support endpoint conditional only on numerical parameters and the
explicit actual bin selection. Every entropy and charge input is derived
from ArithmeticCore; the old natural-density field is never constructed. -/
theorem core_large_step_prime_pool_no_walk_of_selected_bins
    {data : SignedResidueData L} {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} (A : ArithmeticCore data b e)
    {D a δ : ℝ} {K W : ℕ} (hD : 1 ≤ D)
    (ha : 0 < a) (ha1 : a ≤ 1) (haδ : 2*a ≤ δ) (hK : 0 < K)
    (hgap : a ≤ (2:ℝ)^K*topCoefficient a)
    (hcost : 4*Real.log 4/((2:ℝ)^K-1) ≤ (topCoefficient a/4)/10000)
    (hselection : CofinalSelectedWindowRateExcess data b e D a δ K W) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p ∈ data.primes) ∧
      ∀ z : ℕ → L, Function.Injective z →
      (∀ t, z t ∈ avoiding data S) →
      (∀ t, dist (planarEmbedding b e (z t))
        (planarEmbedding b e (z (t+1))) ≤ D) → False := by
  let c : ℝ := topCoefficient a/4
  have hcharges := eventually_common_window_batch_charge data b e A hD ha ha1 haδ hgap W
  have herrors := eventually_actual_window_telescope_errors data
    (Real.log (wordStepBall b e D).card) W
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp (hcharges.and herrors)
  obtain ⟨m, hm, J, hfull, hglobal, hexcess⟩ := hselection m₀
  obtain ⟨hcharge, herror⟩ := hm₀ m hm
  have hupper : ∀ w < W, ∀ j ∈ J w,
      (j:ℝ)*Real.log 2 ≤ 21/20*((100:ℝ)^w*Real.exp m) :=
    fun w hw j hj => (hfull w hw j hj).2.1
  have hsep : ∀ w < W, ∀ i ∈ J w, ∀ j ∈ J w, i < j → i+K ≤ j := by
    intro w hw i hi j hj hij
    exact hglobal i (Finset.mem_biUnion.mpr ⟨w,Finset.mem_range.mpr hw,hi⟩)
      j (Finset.mem_biUnion.mpr ⟨w,Finset.mem_range.mpr hw,hj⟩) hij
  have hball : 1 ≤ (wordStepBall b e D).card := by
    apply Finset.one_le_card.mpr
    exact ⟨0, by simpa only [mem_wordStepBall, planarEmbedding_zero, norm_zero]
      using (show 0 ≤ D by linarith only [hD])⟩
  have hlog : 0 ≤ Real.log (wordStepBall b e D).card :=
    Real.log_nonneg (by exact_mod_cast hball)
  have hcardpos : 0 < (allBins W J).card := by
    by_contra h
    have he : allBins W J = ∅ := Finset.card_eq_zero.mp (by omega)
    simp only [he, Finset.sum_empty] at hexcess
    linarith only [hexcess, hlog]
  obtain ⟨n, hcard⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcardpos)
  obtain ⟨herr, htotal⟩ := herror J hupper
  refine ⟨dyadicPrimePool data J W, dyadicPrimePool_mem_primes data J W, ?_⟩
  intro z hz havoid hs
  have hlocal : ∀ j ≤ n, ∀ F : Finset (ℕ × Bool),
      F ⊆ precedingDyadicLabels data (allBins W J) j →
      ∃ G : Finset (ℕ × Bool), F ⊆ G ∧
        G ⊆ F ∪ dyadicBatchLabels data (binEnum (allBins W J) j) ∧
        windowBatchRate c (binEnum (allBins W J) j) ≤
          residueWordCharge data ((TimeLaw.at 0).advance
            (commonSchedule z (commonBlocks a m W J) (windowSmoothing W m)))
            z (batchWordLength (binEnum (allBins W J) j)) F G := by
    intro j hj F hF
    have hjcard : j < (allBins W J).card := by omega
    have hjB := binEnum_mem (allBins W J) hjcard
    obtain ⟨w, hw, hjw⟩ := allBins_member_window J hjB
    have hpoolF : F ⊆ dyadicPoolLabels data J W := hF.trans
      (precedingDyadicLabels_subset_pool data J hjcard.le)
    have hbudget := predecessor_selected_family_budget data (allBins W J)
      hK hjcard hglobal hcost F hF
    obtain ⟨G, hFG, _, hG, _, _, hinfo⟩ := hcharge J hfull hsep z hz hs havoid
      w hw _ hjw F hpoolF hbudget
    exact ⟨G, hFG, hG, hinfo⟩
  have hbound := actual_selected_window_charge_sum_le b e data z D hs a c
    m W n J hcard hupper herr htotal hlocal
  exact (not_lt_of_ge hbound) hexcess

/-- The literal finite `Q²` component consequence, with the aggregate
selection premise visible for each sufficiently large step bound. This
conditional support theorem is independent of the former A5 density field. -/
theorem core_finite_sieve_of_selected_windows
    {data : SignedResidueData L} {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} (A : ArithmeticCore data b e)
    (hselect : ∀ D : ℝ, 1 ≤ D → ∃ a δ : ℝ, ∃ K W : ℕ,
      0 < a ∧ a ≤ 1 ∧ 2*a ≤ δ ∧ 0 < K ∧
      a ≤ (2:ℝ)^K*topCoefficient a ∧
      4*Real.log 4/((2:ℝ)^K-1) ≤ (topCoefficient a/4)/10000 ∧
      CofinalSelectedWindowRateExcess data b e D a δ K W) :
    ∀ D : ℝ, 0 ≤ D → ∃ S : Finset ℕ,
      (∀ p ∈ S, p ∈ data.primes) ∧
      UniformComponentBound (latticeGraph b e D (avoiding data S)) (S.prod id ^ 2) := by
  intro D _
  obtain ⟨a, δ, K, W, ha, ha1, haδ, hK, hgap, hcost, hselection⟩ :=
    hselect (max D 1) (le_max_right _ _)
  obtain ⟨S, hS, hno⟩ := core_large_step_prime_pool_no_walk_of_selected_bins
    A (le_max_right D 1) ha ha1 haδ hK hgap hcost hselection
  refine ⟨S, hS, avoiding_component_bound_of_no_infinite_walk b e data S hS D ?_⟩
  intro w hw hstep
  let z : ℕ → L := fun n => (w n).val
  have hz : Function.Injective z := by
    intro i j hij
    apply hw
    exact Subtype.ext hij
  apply hno z hz (fun n => (w n).property)
  intro n
  have hdist : dist (planarEmbedding b e (z n))
      (planarEmbedding b e (z (n+1))) ≤ D := by
    simpa only [dist_eq_norm] using (hstep n).2
  exact hdist.trans (le_max_left _ _)

end Entry002.WeakA5
