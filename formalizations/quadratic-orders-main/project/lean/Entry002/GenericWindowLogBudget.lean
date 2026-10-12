import Entry002.GenericDensityBands
import Entry002.GenericBatchSelection
import Entry002.GenericCommonWindowNumerics

/-!
# Actual signed-label costs for the selected common windows

Actual finite prime labels and their sum(log p) are used throughout. The finite
union/preceding-cost proofs adapt the generic bookkeeping in OpenAI family028
GaussianMoat/WindowParameters.lean and SeparatedParameters.lean; the final
smoothing estimates adapt SieveSmoothing.lean. Source maps distinguish all
adaptations from verbatim replay. Commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Apache-2.0. No budget or desired rate is introduced as an axiom.
-/
set_option autoImplicit false
namespace Entry002
open Filter Module
open scoped BigOperators Classical Topology
variable {L : Type*} [AddCommGroup L]

noncomputable def primeLabelWeight (F : Finset (ℕ × Bool)) : ℝ :=
  F.sum (fun i => Real.log i.1)

noncomputable def dyadicBatchLabels (data : SignedResidueData L) (j : ℕ) :
    Finset (ℕ × Bool) := dyadicPrimeBatch data.primes j ×ˢ (Finset.univ : Finset Bool)

noncomputable def precedingDyadicLabels (data : SignedResidueData L) (J : Finset ℕ)
    (n : ℕ) : Finset (ℕ × Bool) :=
  (Finset.range n).biUnion (fun k => dyadicBatchLabels data (binEnum J k))

noncomputable def dyadicPoolLabels (data : SignedResidueData L)
    (J : ℕ → Finset ℕ) (W : ℕ) : Finset (ℕ × Bool) :=
  dyadicPrimePool data J W ×ˢ (Finset.univ : Finset Bool)

lemma dyadicBatchLabels_mem_primes (data : SignedResidueData L) (j : ℕ) :
    ∀ i∈dyadicBatchLabels data j, i.1∈data.primes := by
  intro i hi
  exact ((mem_dyadicPrimeBatch _ _ _).mp (Finset.mem_product.mp hi).1).1

lemma dyadicPoolLabels_mem_primes (data : SignedResidueData L)
    (J : ℕ → Finset ℕ) (W : ℕ) :
    ∀ i∈dyadicPoolLabels data J W, i.1∈data.primes := by
  intro i hi
  exact dyadicPrimePool_mem_primes data J W i.1 (Finset.mem_product.mp hi).1

lemma primeLabelWeight_mono (data : SignedResidueData L)
    {F G : Finset (ℕ × Bool)} (hFG : F⊆G) (hG : ∀ i∈G, i.1∈data.primes) :
    primeLabelWeight F≤primeLabelWeight G := by
  apply Finset.sum_le_sum_of_subset_of_nonneg hFG
  intro i hi _
  exact Real.log_nonneg (by exact_mod_cast (data.prime_mem _ (hG i hi)).one_le)

lemma primeLabelWeight_product (S : Finset ℕ) :
    primeLabelWeight (S ×ˢ (Finset.univ : Finset Bool))=2*S.sum (fun p => Real.log p) := by
  simp only [primeLabelWeight,Finset.sum_product,Finset.sum_const,Finset.card_univ,
    Fintype.card_bool,nsmul_eq_mul,←Finset.mul_sum,Nat.cast_ofNat]

lemma dyadicBatchLabels_weight_le (data : SignedResidueData L) (j : ℕ) :
    primeLabelWeight (dyadicBatchLabels data j)≤(4*Real.log 4)*(2:ℝ)^j := by
  rw [dyadicBatchLabels,primeLabelWeight_product]
  exact dyadicPrimeBatch_signed_log_weight_le data j

lemma primeLabelWeight_biUnion_le {ι : Type*} [DecidableEq ι]
    (data : SignedResidueData L) (I : Finset ι) (A : ι → Finset (ℕ × Bool))
    (hp : ∀ j∈I, ∀ i∈A j, i.1∈data.primes) :
    primeLabelWeight (I.biUnion A)≤∑ j∈I, primeLabelWeight (A j) := by
  induction I using Finset.induction_on with
  | empty => simp [primeLabelWeight]
  | @insert a I ha ih =>
    rw [Finset.biUnion_insert,Finset.sum_insert ha]
    have hprime : ∀ i∈I.biUnion A, i.1∈data.primes := by
      intro i hi
      obtain ⟨j,hj,hi⟩ := Finset.mem_biUnion.mp hi
      exact hp j (Finset.mem_insert_of_mem hj) i hi
    exact (residueLabels_union_log_weight_le data (A a) (I.biUnion A) hprime).trans
      (add_le_add le_rfl (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj))))

/-- Genuine finite signed-label cost below a K-separated current dyadic scale. -/
theorem separated_dyadic_labels_cost (data : SignedResidueData L)
    (J : Finset ℕ) {K j : ℕ} (hK : 0<K)
    (hsep : ∀ a∈J, ∀ b∈J, a<b → a+K≤b)
    (hcap : ∀ a∈J, a+K≤j) :
    primeLabelWeight (J.biUnion (dyadicBatchLabels data))≤
      (4*Real.log 4/((2:ℝ)^K-1))*(2:ℝ)^j := by
  have hsum := Finset.sum_le_sum (fun a (_ : a∈J) => dyadicBatchLabels_weight_le data a)
  rw [←Finset.mul_sum] at hsum
  have hh := mul_le_mul_of_nonneg_left (separated_power_sum J hK hsep hcap)
    (show 0≤4*Real.log 4 by positivity)
  have ht := (primeLabelWeight_biUnion_le data J (dyadicBatchLabels data)
    (fun j _ => dyadicBatchLabels_mem_primes data j)).trans (hsum.trans hh)
  calc
    _ ≤ 4*Real.log 4*((2:ℝ)^j/(2^K-1)) := ht
    _ = _ := by ring

lemma precedingDyadicLabels_enum_subset (data : SignedResidueData L)
    (J : Finset ℕ) {n : ℕ} (hn : n<J.card) :
    precedingDyadicLabels data J n⊆
      (J.filter (·<binEnum J n)).biUnion (dyadicBatchLabels data) := by
  intro f hf
  obtain ⟨k,hk,hf⟩ := Finset.mem_biUnion.mp hf
  have hk' := Finset.mem_range.mp hk
  apply Finset.mem_biUnion.mpr
  exact ⟨binEnum J k,Finset.mem_filter.mpr
    ⟨binEnum_mem J (hk'.trans hn),binEnum_strictMono J hk' hn⟩,hf⟩

/-- The cost of every actual predecessor label, with no charged-growth premise. -/
theorem precedingDyadicLabels_enum_cost (data : SignedResidueData L)
    (J : Finset ℕ) {K n : ℕ} (hK : 0<K) (hn : n<J.card)
    (hsep : ∀ a∈J, ∀ b∈J, a<b → a+K≤b) :
    primeLabelWeight (precedingDyadicLabels data J n)≤
      (4*Real.log 4/((2:ℝ)^K-1))*(2:ℝ)^(binEnum J n) := by
  apply (primeLabelWeight_mono data (precedingDyadicLabels_enum_subset data J hn) ?_).trans
  · apply separated_dyadic_labels_cost data _ hK
    · intro a ha b hb hab
      exact hsep a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
    · intro a ha
      exact hsep a (Finset.mem_filter.mp ha).1 (binEnum J n)
        (binEnum_mem J hn) (Finset.mem_filter.mp ha).2
  · intro i hi
    obtain ⟨j,_,hi⟩ := Finset.mem_biUnion.mp hi
    exact dyadicBatchLabels_mem_primes data j i hi

/-- Any actual selected old family inherits the exact positive-rate budget. -/
theorem predecessor_selected_family_budget (data : SignedResidueData L)
    (J : Finset ℕ) {K n : ℕ} {c : ℝ} (hK : 0<K) (hn : n<J.card)
    (hsep : ∀ a∈J, ∀ b∈J, a<b → a+K≤b)
    (hcost : 4*Real.log 4/((2:ℝ)^K-1)≤c/10000)
    (F : Finset (ℕ × Bool)) (hF : F⊆precedingDyadicLabels data J n) :
    primeLabelWeight F≤c*(2:ℝ)^(binEnum J n)/10000 := by
  have hp : ∀ i∈precedingDyadicLabels data J n, i.1∈data.primes := by
    intro i hi
    obtain ⟨k,_,hi⟩ := Finset.mem_biUnion.mp hi
    exact dyadicBatchLabels_mem_primes data _ i hi
  have hb := (primeLabelWeight_mono data hF hp).trans
    (precedingDyadicLabels_enum_cost data J hK hn hsep)
  have hh := mul_le_mul_of_nonneg_right hcost (show 0≤(2:ℝ)^(binEnum J n) by positivity)
  exact hb.trans (by simpa only [div_mul_eq_mul_div] using hh)

/- Verbatim generic SieveSmoothing.lean lines 9--19. -/
lemma allBins_scale_bound {m W : ℕ} (J : ℕ → Finset ℕ)
    (hb : ∀ w<W, ∀ j∈J w, j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m))
    {j : ℕ} (hj : j∈allBins W J) :
    (2:ℝ)^j≤Real.exp (21/20*(100:ℝ)^W*Real.exp m) := by
  obtain ⟨w,hw,hj⟩ := Finset.mem_biUnion.mp hj
  have hw' := Finset.mem_range.mp hw
  have hp := mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤100) hw'.le) (Real.exp_nonneg (m:ℝ))
  rw [←Real.exp_log (by positivity : (0:ℝ)<2^j),Real.log_pow]
  apply Real.exp_le_exp.mpr
  nlinarith only [hb w hw' j hj,hp]

/-- The fixed finite pool has its genuine Chebyshev prime-log cap. -/
theorem dyadicPoolLabels_log_weight_cap (data : SignedResidueData L)
    {m W : ℕ} (J : ℕ → Finset ℕ)
    (hb : ∀ w<W, ∀ j∈J w, j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) :
    primeLabelWeight (dyadicPoolLabels data J W)≤
      (4*Real.log 4)*Real.exp (21/20*(100:ℝ)^W*Real.exp m) := by
  rw [dyadicPoolLabels,primeLabelWeight_product]
  have hcap := prime_log_mass_le_theta (dyadicPrimePool data J W)
    (U := 2*Real.exp (21/20*(100:ℝ)^W*Real.exp m)) (by positivity) (by
      intro p hp
      have hprime := data.prime_mem p (dyadicPrimePool_mem_primes data J W p hp)
      obtain ⟨j,hj,hpj⟩ := Finset.mem_biUnion.mp hp
      have hupper := (mem_dyadicPrimeBatch _ _ _).mp hpj
      have hjupper := allBins_scale_bound J hb hj
      refine ⟨hprime,?_⟩
      have hh := mul_le_mul_of_nonneg_left hjupper (show (0:ℝ)≤2 by norm_num)
      exact hupper.2.2.trans (by simpa only [pow_succ,mul_comm] using hh))
  nlinarith only [hcap]

/-- One scalar threshold bounds the actual finite signed prime pool before
all laws and walks, with the same window smoothing scale. -/
theorem eventually_dyadicPoolLabels_weight (data : SignedResidueData L) (W : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ → Finset ℕ,
      (∀ w<W, ∀ j∈J w, j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) →
      primeLabelWeight (dyadicPoolLabels data J W)≤Real.exp ((2*(100:ℝ)^W)*Real.exp m) := by
  have ht : Tendsto (fun m : ℕ => (100:ℝ)^W*Real.exp m) atTop atTop :=
    (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)
  filter_upwards [ht.eventually (eventually_mul_exp_le_exp
    (a := 21/20) (b := 2) (by norm_num) (4*Real.log 4))] with m hm
  intro J hb
  exact (dyadicPoolLabels_log_weight_cap data J hb).trans
    (by simpa only [mul_assoc] using hm)

/-- Actual finite-pool logarithmic weights satisfy every common-law telescope
error and the total error budget, using the literal `windowSmoothing W m`. -/
theorem eventually_actual_window_telescope_errors (data : SignedResidueData L)
    (H : ℝ) (W : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ → Finset ℕ,
      (∀ w<W, ∀ j∈J w, j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) →
      (∀ i∈allBins W J, ∀ j∈allBins W J, ∀ a<batchWordLength j,
        2*Real.binEntropy ((a:ℝ)/(windowSmoothing W m+1))+
          ((a:ℝ)/(windowSmoothing W m+1))*((batchWordLength i:ℝ)*H+
            2*primeLabelWeight (dyadicPoolLabels data J W))≤Real.exp (-Real.exp m)) ∧
      ((allBins W J).card:ℝ)*Real.exp (-Real.exp m)≤1 := by
  have hA : 1≤2*(100:ℝ)^W := by have := window_power_one W; linarith only [this]
  have ht : Tendsto (fun m : ℕ => Real.exp (m:ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_dyadicPoolLabels_weight data W,
    ht.eventually (eventually_smoothing_guard (H := H) hA),
    ht.eventually (eventually_smoothing_total (3*(W:ℝ)*(100:ℝ)^W)),
    ht.eventually (eventually_ge_atTop (2:ℝ))] with m hweight hsmooth htotal hm
  intro J hJ
  have hL (j : ℕ) (hj : j∈allBins W J) :
      (batchWordLength j:ℝ)≤Real.exp ((2*(100:ℝ)^W)*Real.exp m) := by
    apply (batchWordLength_le_scale j).trans ((allBins_scale_bound J hJ hj).trans _)
    apply Real.exp_le_exp.mpr
    have : 0≤(100:ℝ)^W*Real.exp m := by positivity
    nlinarith only [this]
  constructor
  · intro i hi j hj a ha
    apply hsmooth _ _ _ _ (Nat.cast_nonneg _)
      ((show (a:ℝ)≤batchWordLength j by exact_mod_cast ha.le).trans (hL j hj))
      (Nat.cast_nonneg _) (hL i hi) (hweight J hJ)
    convert (windowSmoothing_bounds W m).1 using 1
    congr 1
    ring
  · exact (mul_le_mul_of_nonneg_right (allBins_card_upper J hm hJ)
      (Real.exp_nonneg _)).trans htotal

@[simp] lemma precedingDyadicLabels_zero (data : SignedResidueData L) (J : Finset ℕ) :
    precedingDyadicLabels data J 0=∅ := by simp [precedingDyadicLabels]

lemma precedingDyadicLabels_succ (data : SignedResidueData L) (J : Finset ℕ) (n : ℕ) :
    precedingDyadicLabels data J (n+1)=precedingDyadicLabels data J n∪
      dyadicBatchLabels data (binEnum J n) := by
  simp only [precedingDyadicLabels,Finset.range_add_one,Finset.biUnion_insert,Finset.union_comm]

lemma precedingDyadicLabels_mono (data : SignedResidueData L) (J : Finset ℕ)
    {n k : ℕ} (hnk : n≤k) : precedingDyadicLabels data J n⊆precedingDyadicLabels data J k := by
  intro i hi
  obtain ⟨j,hj,hi⟩ := Finset.mem_biUnion.mp hi
  exact Finset.mem_biUnion.mpr ⟨j,Finset.range_mono hnk hj,hi⟩

lemma precedingDyadicLabels_mem_primes (data : SignedResidueData L)
    (J : Finset ℕ) (n : ℕ) :
    ∀ i∈precedingDyadicLabels data J n, i.1∈data.primes := by
  intro i hi
  obtain ⟨j,_,hi⟩ := Finset.mem_biUnion.mp hi
  exact dyadicBatchLabels_mem_primes data _ i hi

lemma dyadicBatchLabels_subset_pool (data : SignedResidueData L)
    (J : ℕ → Finset ℕ) {W j : ℕ} (hj : j∈allBins W J) :
    dyadicBatchLabels data j⊆dyadicPoolLabels data J W := by
  intro i hi
  obtain ⟨hp,hbool⟩ := Finset.mem_product.mp hi
  exact Finset.mem_product.mpr ⟨Finset.mem_biUnion.mpr ⟨j,hj,hp⟩,hbool⟩

lemma precedingDyadicLabels_subset_pool (data : SignedResidueData L)
    (J : ℕ → Finset ℕ) {W n : ℕ} (hn : n≤(allBins W J).card) :
    precedingDyadicLabels data (allBins W J) n⊆dyadicPoolLabels data J W := by
  intro i hi
  obtain ⟨k,hk,hi⟩ := Finset.mem_biUnion.mp hi
  have hk' : k<(allBins W J).card := (Finset.mem_range.mp hk).trans_le hn
  exact dyadicBatchLabels_subset_pool data J (binEnum_mem (allBins W J) hk') hi

lemma precedingDyadicLabels_all (data : SignedResidueData L)
    (J : ℕ → Finset ℕ) (W : ℕ) :
    precedingDyadicLabels data (allBins W J) (allBins W J).card=dyadicPoolLabels data J W := by
  apply Finset.Subset.antisymm (precedingDyadicLabels_subset_pool data J le_rfl)
  intro i hi
  obtain ⟨hp,hbool⟩ := Finset.mem_product.mp hi
  obtain ⟨j,hj,hpj⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨n,hn,he⟩ := binEnum_surj (allBins W J) hj
  apply Finset.mem_biUnion.mpr
  refine ⟨n,Finset.mem_range.mpr hn,?_⟩
  exact Finset.mem_product.mpr ⟨by simpa only [he] using hpj,hbool⟩

/-- The density constant is fixed first, so the gap can be chosen afterward
without changing any actual prime-density estimate. -/
theorem separated_dyadic_batches_of_uniform_density (P : Set ℕ)
    {δ : ℝ} {j₀ : ℕ}
    (hdense : ∀ j≥j₀, δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dyadicPrimeBatch P j).card)
    (K : ℕ) (hK : 0<K) :
    ∀ᶠ X : ℝ in atTop, ∃ J : Finset ℕ,
      (1/(80*Real.log 2*K))*X≤J.card ∧
      (∀ i∈J, ∀ j∈J, i<j → i+K≤j) ∧
      ∀ j∈J, X≤(j:ℝ)*Real.log 2 ∧ (j:ℝ)*Real.log 2≤21/20*X ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dyadicPrimeBatch P j).card := by
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hKR : (0:ℝ)<K := by exact_mod_cast hK
  filter_upwards [eventually_ge_atTop (max (80*Real.log 2) ((j₀:ℝ)*Real.log 2))]
    with X hX
  have hwindow := dyadicLogWindow_bounds ((le_max_left _ _).trans hX)
  obtain ⟨a,_,hcard,hsep⟩ := thin_bins (dyadicLogWindow X) hK
  refine ⟨(dyadicLogWindow X).filter (fun j => j%K=a),?_,hsep,?_⟩
  · have hh := (div_le_div_of_nonneg_right hwindow.1 hKR.le).trans hcard
    have he : (1/(80*Real.log 2*K))*X=(X/(80*Real.log 2))/K := by field_simp
    rwa [he]
  · intro j hj
    obtain ⟨hlo,hhi⟩ := hwindow.2 j (Finset.mem_filter.mp hj).1
    have hstart := (le_max_right _ _).trans hX
    have hj₀ : j₀≤j := by
      have hh : (j₀:ℝ)≤j := (mul_le_mul_iff_left₀ hl).mp (hstart.trans hlo)
      exact_mod_cast hh
    exact ⟨hlo,hhi,hdense j hj₀⟩

/-- A5 constructs numerical window parameters and actual dense separated
selections with one fixed density constant, before every law and walk. -/
theorem ArithmeticInterface.common_window_parameters
    {data : SignedResidueData L} {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} (A : ArithmeticInterface data b e) :
    ∃ a δ t : ℝ, ∃ K : ℕ,
      0<a ∧ a≤1 ∧ 2*a≤δ ∧ 0<δ ∧ 0<t ∧ 0<K ∧
      a≤(2:ℝ)^K*topCoefficient a ∧
      4*Real.log 4/((2:ℝ)^K-1)≤(topCoefficient a/4)/10000 ∧
      ∀ᶠ m : ℕ in atTop, ∃ J : ℕ → Finset ℕ, ∀ w : ℕ,
        t*((100:ℝ)^w*Real.exp m)≤(J w).card ∧
        (∀ i∈J w, ∀ j∈J w, i<j → i+K≤j) ∧
        ∀ j∈J w,
          (100:ℝ)^w*Real.exp m≤(j:ℝ)*Real.log 2 ∧
          (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m) ∧
          δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dyadicPrimeBatch data.primes j).card := by
  obtain ⟨δ,hδ,j₀,hdense⟩ := A.uniform_dyadic_density
  obtain ⟨a,K,ha,ha1,haδ,hK,hgap,hcost⟩ := exists_window_gap_parameters hδ
  let t : ℝ := 1/(80*Real.log 2*K)
  have ht : 0<t := by dsimp only [t]; positivity
  have hselection := separated_dyadic_batches_of_uniform_density data.primes hdense K hK
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp hselection
  have hexp : Tendsto (fun m : ℕ => Real.exp (m:ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨a,δ,t,K,ha,ha1,haδ,hδ,ht,hK,hgap,hcost,?_⟩
  filter_upwards [hexp.eventually (eventually_ge_atTop X₀)] with m hm
  have hsel (w : ℕ) := hX₀ ((100:ℝ)^w*Real.exp m)
    (hm.trans (by nlinarith only [window_power_one w,Real.exp_nonneg (m:ℝ)]))
  choose J hJ using hsel
  exact ⟨J,hJ⟩

end Entry002
