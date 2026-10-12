import Entry002.GenericWindowContradiction
import Entry002.GenericWindowLogBudget
import Entry002.GenericWindowSchedule
import Entry002.GenericCommonWindowCharge
import Entry002.GenericResidueGrowth
import Entry002.SieveReduction

/-!
# The actual common-window finite sieve engine

The finite growth and information summation use actual residues of the arbitrary
lattice and one literal common schedule. Auxiliary lemmas exposing local rates
are intermediate bridges; a universal finite-sieve result must derive their
inputs from ArithmeticInterface rather than assume an analytic certificate.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Entry002
open Filter Module OAI.GaussianMoat
open scoped BigOperators Classical Topology
variable {L : Type*} [AddCommGroup L]

lemma window_batchWordLength_le_smoothing (m W : ℕ) (J : ℕ → Finset ℕ)
    (hb : ∀ w<W, ∀ j∈J w, j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m))
    {j : ℕ} (hj : j∈allBins W J) : batchWordLength j≤windowSmoothing W m := by
  have hh := (batchWordLength_le_scale j).trans ((allBins_scale_bound J hb hj).trans
    ((Real.exp_le_exp.mpr (by
      have hp : 0≤(100:ℝ)^W*Real.exp m := by positivity
      nlinarith only [hp])).trans (windowSmoothing_bounds W m).1))
  exact_mod_cast hh

/-- Actual nested selections inside the predecessor labels give a shared-law
sum bound. This is the deterministic finite induction/telescope step; its local
rate input is discharged by the geometric common-window charge theorem. -/
theorem actual_selected_window_charge_sum_le
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (data : SignedResidueData L) (z : ℕ → L) (D : ℝ)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1)))≤D)
    (a c : ℝ) (m W n : ℕ) (J : ℕ → Finset ℕ)
    (hcard : (allBins W J).card=n+1)
    (hb : ∀ w<W, ∀ j∈J w, j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m))
    (herr : ∀ i∈allBins W J, ∀ j∈allBins W J, ∀ s<batchWordLength j,
      2*Real.binEntropy ((s:ℝ)/(windowSmoothing W m+1))+
        ((s:ℝ)/(windowSmoothing W m+1))*((batchWordLength i:ℝ)*
          Real.log (wordStepBall b e D).card+
          2*primeLabelWeight (dyadicPoolLabels data J W))≤Real.exp (-Real.exp m))
    (htotal : ((allBins W J).card:ℝ)*Real.exp (-Real.exp m)≤1)
    (hcharge : ∀ j≤n, ∀ F : Finset (ℕ × Bool),
      F⊆precedingDyadicLabels data (allBins W J) j →
      ∃ G : Finset (ℕ × Bool), F⊆G ∧
        G⊆F∪dyadicBatchLabels data (binEnum (allBins W J) j) ∧
        windowBatchRate c (binEnum (allBins W J) j)≤
          residueWordCharge data ((TimeLaw.at 0).advance
            (commonSchedule z (commonBlocks a m W J) (windowSmoothing W m)))
            z (batchWordLength (binEnum (allBins W J) j)) F G) :
    (∑ j∈allBins W J, windowBatchRate c j)≤
      Real.log (wordStepBall b e D).card+1 := by
  let B := allBins W J
  let Q := (TimeLaw.at 0).advance
    (commonSchedule z (commonBlocks a m W J) (windowSmoothing W m))
  let len := fun j => batchWordLength (binEnum B j)
  have hprefix (j : ℕ) : precedingDyadicLabels data B (j+1)=
      precedingDyadicLabels data B j∪dyadicBatchLabels data (binEnum B j) := by
    unfold precedingDyadicLabels
    rw [Finset.range_add_one,Finset.biUnion_insert]
    exact Finset.union_comm _ _
  have hmono (j : ℕ) : precedingDyadicLabels data B j⊆
      precedingDyadicLabels data B (j+1) := by
    rw [hprefix]
    exact Finset.subset_union_left
  obtain ⟨F,hFA,hFF,hR⟩ := greedy_finite_selection
    (precedingDyadicLabels data B) hmono n
    (fun j F G => windowBatchRate c (binEnum B j)≤
      residueWordCharge data Q z (len j) F G) (by
        intro j hj F hF
        obtain ⟨G,hFG,hlocal,hinfo⟩ := hcharge j hj F hF
        refine ⟨G,hFG,?_,hinfo⟩
        rw [hprefix]
        exact hlocal.trans (Finset.union_subset_union_left hF))
  have hprime : ∀ j i, i∈F j → i.1∈data.primes := by
    intro j i hi
    obtain ⟨k,_,hi⟩ := Finset.mem_biUnion.mp (hFA j hi)
    exact dyadicBatchLabels_mem_primes data _ i hi
  have hpool : ∀ j≤B.card, F j⊆dyadicPoolLabels data J W := by
    intro j hj i hi
    obtain ⟨k,hk,hi⟩ := Finset.mem_biUnion.mp (hFA j hi)
    have hk' : k<B.card := (Finset.mem_range.mp hk).trans_le hj
    have hkB := binEnum_mem B hk'
    have hip := (Finset.mem_product.mp hi).1
    exact Finset.mem_product.mpr ⟨Finset.mem_biUnion.mpr
      ⟨binEnum B k,hkB,hip⟩,Finset.mem_univ _⟩
  have herrF : ∀ j<n, ∀ s<len (j+1),
      2*Real.binEntropy ((s:ℝ)/(windowSmoothing W m+1))+
        ((s:ℝ)/(windowSmoothing W m+1))*((len j:ℝ)*
          Real.log (wordStepBall b e D).card+
          2*(F (j+1)).sum (fun i => Real.log i.1))≤Real.exp (-Real.exp m) := by
    intro j hj s hs'
    have hiB : binEnum B j∈B := binEnum_mem B (by dsimp [B]; omega)
    have hjB : binEnum B (j+1)∈B := binEnum_mem B (by dsimp [B]; omega)
    have hw := primeLabelWeight_mono data (hpool (j+1) (by dsimp [B]; omega))
      (dyadicPoolLabels_mem_primes data J W)
    have hbound := herr _ hiB _ hjB s hs'
    have ht : 0≤(s:ℝ)/(windowSmoothing W m+1) := by positivity
    have hmul := mul_le_mul_of_nonneg_left (show
      (len j:ℝ)*Real.log (wordStepBall b e D).card+2*primeLabelWeight (F (j+1))≤
      (len j:ℝ)*Real.log (wordStepBall b e D).card+
        2*primeLabelWeight (dyadicPoolLabels data J W) by linarith) ht
    dsimp only [primeLabelWeight] at hmul hbound
    change _ ≤ _ at hbound
    dsimp only [len] at hmul ⊢
    linarith only [hmul,hbound]
  have htel := schedule_lattice_information_telescope b e data z D hs
    (commonBlocks a m W J) (windowSmoothing W m) n F hprime hFF len
    (fun j _ => batchWordLength_pos _) (fun j hj =>
      enumerated_window_lengths_dvd J hcard hj)
    (fun j hj => window_batchWordLength_le_smoothing m W J hb
      (binEnum_mem B (by dsimp [B]; omega))) (Real.exp_nonneg _) herrF
  have hsum := Finset.sum_le_sum (s := Finset.range (n+1))
    (fun j hj => hR j (by have := Finset.mem_range.mp hj; omega))
  have hbudget : (n:ℝ)*Real.exp (-Real.exp m)≤1 := by
    have hn : (n:ℝ)≤(B.card:ℝ) := by exact_mod_cast (show n≤B.card by dsimp [B]; omega)
    exact (mul_le_mul_of_nonneg_right hn (Real.exp_nonneg _)).trans htotal
  have heq := binEnum_sum B (windowBatchRate c)
  rw [hcard] at heq
  rw [←heq]
  exact (hsum.trans htel).trans (by linarith only [hbudget])

/-- A genuine finite prime pool is chosen before every walk. All local
selected charges are derived from ArithmeticInterface by the proved common
window entropy, coverage, posterior selection and numerical estimates. -/
theorem ArithmeticInterface.large_step_prime_pool_no_walk
    {data : SignedResidueData L} {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} (A : ArithmeticInterface data b e)
    {D : ℝ} (hD : 1≤D) :
    ∃ S : Finset ℕ, (∀ p∈S, p∈data.primes) ∧
      ∀ z : ℕ → L, Function.Injective z →
      (∀ t, z t∈avoiding data S) →
      (∀ t, dist (planarEmbedding b e (z t))
        (planarEmbedding b e (z (t+1)))≤D) → False := by
  obtain ⟨a,δ,t,K,ha,ha1,haδ,hδ,ht,hK,hgap,hcost,hselection⟩ :=
    A.common_window_parameters
  let c : ℝ := topCoefficient a/4
  have hc : 0<c := div_pos (topCoefficient_pos ha) (by norm_num)
  obtain ⟨W,hW,hexcess⟩ := exists_window_rate_excess b e D hc ht
  have hcharges := eventually_common_window_batch_charge data b e A hD ha ha1 haδ hgap W
  have herrors := eventually_actual_window_telescope_errors data
    (Real.log (wordStepBall b e D).card) W
  obtain ⟨m,hm⟩ := (hselection.and (hcharges.and (herrors.and
    (eventually_common_window_large ((K:ℝ)*Real.log 2))))).exists
  obtain ⟨J,hJ⟩ := hm.1
  have hcharge := hm.2.1
  have herror := hm.2.2.1
  have hKscale : (K:ℝ)*Real.log 2≤Real.exp m := by
    simpa only [pow_zero,one_mul] using hm.2.2.2 0
  have hb : ∀ w<W, ∀ j∈J w,
      (100:ℝ)^w*Real.exp m≤(j:ℝ)*Real.log 2 ∧
      (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m) := by
    intro w _ j hj
    exact ⟨((hJ w).2.2 j hj).1,((hJ w).2.2 j hj).2.1⟩
  have hupper := fun w hw j hj => (hb w hw j hj).2
  have hdense := fun w (_ : w<W) => (hJ w).1
  have hsep := fun w (_ : w<W) => (hJ w).2.1
  have hfull : ∀ w<W, ∀ j∈J w,
      (100:ℝ)^w*Real.exp m≤(j:ℝ)*Real.log 2 ∧
      (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m) ∧
      δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dyadicPrimeBatch data.primes j).card := by
    intro w _
    exact (hJ w).2.2
  have hglobal := allBins_separated J (Real.exp_pos (m:ℝ)) hKscale hb hsep
  have hcardpos := allBins_card_pos_of_density J hW (Real.exp_pos (m:ℝ)) ht hdense
  obtain ⟨n,hcard⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcardpos)
  obtain ⟨herr,htotal⟩ := herror J hupper
  refine ⟨dyadicPrimePool data J W,dyadicPrimePool_mem_primes data J W,?_⟩
  intro z hz havoid hs
  have hlocal : ∀ j≤n, ∀ F : Finset (ℕ × Bool),
      F⊆precedingDyadicLabels data (allBins W J) j →
      ∃ G : Finset (ℕ × Bool), F⊆G ∧
        G⊆F∪dyadicBatchLabels data (binEnum (allBins W J) j) ∧
        windowBatchRate c (binEnum (allBins W J) j)≤
          residueWordCharge data ((TimeLaw.at 0).advance
            (commonSchedule z (commonBlocks a m W J) (windowSmoothing W m)))
            z (batchWordLength (binEnum (allBins W J) j)) F G := by
    intro j hj F hF
    have hjcard : j<(allBins W J).card := by omega
    have hjB := binEnum_mem (allBins W J) hjcard
    obtain ⟨w,hw,hjw⟩ := allBins_member_window J hjB
    have hpoolF : F⊆dyadicPoolLabels data J W := hF.trans
      (precedingDyadicLabels_subset_pool data J hjcard.le)
    have hbudget := predecessor_selected_family_budget data (allBins W J)
      hK hjcard hglobal hcost F hF
    obtain ⟨G,hFG,_,hG,_,_,hinfo⟩ := hcharge J hfull hsep z hz hs havoid
      w hw _ hjw F hpoolF hbudget
    exact ⟨G,hFG,hG,hinfo⟩
  have hbound := actual_selected_window_charge_sum_le b e data z D hs a c
    m W n J hcard hupper herr htotal hlocal
  have hlower := allBins_rate J (Real.exp_pos (m:ℝ)) hc hb hdense
  change (W:ℝ)*(c*t/10500000)≤∑ j∈allBins W J, windowBatchRate c j at hlower
  exact (not_lt_of_ge (hlower.trans hbound)) hexcess

/-- The generic finite planar sieve theorem follows from the derived large-step
engine and actual periodic component reduction. All smaller step bounds are
handled by edge monotonicity, without changing any metric normalization. -/
theorem finiteSieveTarget_proved : FiniteSieveTarget := by
  apply finiteSieveTarget_of_large_step_no_walk
  intro L _ b e data A
  refine ⟨1,by norm_num,?_⟩
  intro D hD
  obtain ⟨S,hS,hno⟩ := A.large_step_prime_pool_no_walk hD
  refine ⟨S,hS,?_⟩
  intro w hw hstep
  let z : ℕ → L := fun n => (w n).val
  have hz : Function.Injective z := by
    intro i j hij
    apply hw
    exact Subtype.ext hij
  apply hno z hz (fun n => (w n).property)
  intro n
  simpa only [dist_eq_norm] using (hstep n).2

end Entry002

