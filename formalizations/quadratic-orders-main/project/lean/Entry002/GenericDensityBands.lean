import Entry002.GenericGeometricBands

/-!
# Actual density-selected prime batches satisfy band guards

The mean and capacity proofs adapt the genuine scalar proofs in OpenAI
family028 GaussianMoat/AccurateScales.lean lines 198--217 and
WindowParameters.lean lines 35--59, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0.
All prime sets below are the actual `dyadicPrimeBatch data.primes j`.
Thresholds and selections precede every time law and walk quantifier.
-/
set_option autoImplicit false
namespace Entry002
open Filter Module
open OAI.GaussianMoat
open scoped BigOperators Classical Topology
variable {L : Type*} [AddCommGroup L]

lemma actual_batchMeanLog_bounds (S : Finset ℕ) (hne : S.Nonempty)
    {T : ℝ} (hT : 0<T)
    (hp : ∀ p∈S, T≤(p:ℝ) ∧ (p:ℝ)≤2*T) :
    Real.log T≤FreshEntropy.batchMeanLog S ∧
      FreshEntropy.batchMeanLog S≤Real.log (2*T) := by
  let _ : Nonempty (Fin S.card) := Fin.pos_iff_nonempty.mp (Finset.card_pos.mpr hne)
  constructor
  · have hh := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
      Real.log_le_log hT (hp _ (signedBatchPrime_mem S i)).1)
    simpa only [FreshEntropy.batchMeanLog,Fintype.expect_const] using hh
  · have hh := Finset.expect_le_expect (s := Finset.univ) (fun i _ =>
      Real.log_le_log (hT.trans_le (hp _ (signedBatchPrime_mem S i)).1)
        (hp _ (signedBatchPrime_mem S i)).2)
    simpa only [FreshEntropy.batchMeanLog,Fintype.expect_const] using hh

/- Adapted from AccurateScales.lean lines 198--217: actual S/mean interface. -/
lemma dense_actual_batch_cap (S : Finset ℕ) (hne : S.Nonempty) {T δ U : ℝ}
    (hT : 2≤T)
    (hp : ∀ p∈S, T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (hdense : δ*T/Real.log (2*T)≤ S.card)
    (hsize : 2*U≤δ*T) : ⌊U/FreshEntropy.batchMeanLog S⌋₊≤ S.card := by
  have hT0 : 0<T := by linarith only [hT]
  have hlogT : 0<Real.log T := Real.log_pos (by linarith only [hT])
  have hm := actual_batchMeanLog_bounds S hne hT0 hp
  have hmean : 0<FreshEntropy.batchMeanLog S := hlogT.trans_le hm.1
  have hl2 : Real.log 2≤Real.log T := Real.log_le_log (by norm_num) hT
  have hhlog : Real.log (2*T)≤2*FreshEntropy.batchMeanLog S := by
    rw [Real.log_mul (by norm_num) hT0.ne']
    linarith only [hl2,hm.1]
  have hlo : 0<Real.log (2*T) := Real.log_pos (by linarith only [hT])
  have hd : δ*T≤(S.card:ℝ)*Real.log (2*T) := (div_le_iff₀ hlo).mp hdense
  have hk : δ*T≤(S.card:ℝ)*(2*FreshEntropy.batchMeanLog S) := hd.trans
    (mul_le_mul_of_nonneg_left hhlog (Nat.cast_nonneg _))
  apply Nat.floor_le_of_le
  apply (div_le_iff₀ hmean).mpr
  nlinarith only [hsize,hk]

lemma bandSize_le_start {μ g U : ℝ} (hμ : 0<μ) (hg : 0≤g)
    (hg1 : g≤1) (hU : 0≤U) (k : ℕ) :
    bandSize μ g U k≤⌊U/μ⌋₊ := by
  apply Nat.floor_mono
  apply div_le_div_of_nonneg_right _ hμ.le
  simpa only [bandScale,pow_zero,one_mul] using
    bandScale_antitone hg hg1 hU (Nat.zero_le k)

/-- Verified guards for the actual batch and actual top-band schedule. -/
structure DyadicTopBandReady (data : SignedResidueData L) (a U₀ : ℝ) (j : ℕ) : Prop where
  nonempty : (dyadicPrimeBatch data.primes j).Nonempty
  prime_scale : 5≤(2:ℝ)^j
  mean_lower : 1≤FreshEntropy.batchMeanLog (dyadicPrimeBatch data.primes j)
  mean_upper : FreshEntropy.batchMeanLog (dyadicPrimeBatch data.primes j)≤
    2*((j:ℝ)*Real.log 2)
  scale_lower : ∀ k≤topIterations, U₀≤
    bandScale topParameter (a*(2:ℝ)^j) k
  relative : ∀ k≤topIterations, 1280*((j:ℝ)*Real.log 2)≤
    topParameter^5*bandScale topParameter (a*(2:ℝ)^j) k
  capacity : ∀ k≤topIterations,
    bandSize (FreshEntropy.batchMeanLog (dyadicPrimeBatch data.primes j))
      topParameter (a*(2:ℝ)^j) k≤(dyadicPrimeBatch data.primes j).card

/-- Density supplies every top-band guard in all sufficiently large actual bins. -/
theorem eventually_dense_dyadic_top_band_ready (data : SignedResidueData L)
    {δ a : ℝ} (hδ : 0<δ) (ha : 0<a) (haδ : 2*a≤δ) (U₀ : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ j : ℕ, x≤(j:ℝ)*Real.log 2 →
      δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dyadicPrimeBatch data.primes j).card →
      DyadicTopBandReady data a U₀ j := by
  have hc := topCoefficient_pos ha
  have hlarge := eventually_poly_le_exp 1280
    (a := topParameter^5*topCoefficient a) (mul_pos (pow_pos topParameter_pos _) hc) 1
  have hscale := eventually_poly_le_exp U₀ (a := topCoefficient a) hc 0
  obtain ⟨r,hr⟩ := eventually_atTop.mp (hlarge.and hscale)
  filter_upwards [eventually_ge_atTop (max 4 r)] with x hx
  intro j hxj hdense
  let S := dyadicPrimeBatch data.primes j
  let y : ℝ := (j:ℝ)*Real.log 2
  have hy : 4≤y := (le_max_left _ _).trans (hx.trans hxj)
  have hyr : r≤y := (le_max_right _ _).trans (hx.trans hxj)
  have heq : Real.exp y=(2:ℝ)^j := by
    dsimp only [y]
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  have hne := dyadicPrimeBatch_nonempty_of_dense data.primes j hδ hdense
  have hT : 5≤(2:ℝ)^j := by
    have hh := Real.add_one_le_exp y
    rw [heq] at hh
    linarith only [hh,hy]
  have hp : ∀ p∈S, (2:ℝ)^j≤(p:ℝ) ∧ (p:ℝ)≤2*(2:ℝ)^j := by
    intro p hp
    have hh := (mem_dyadicPrimeBatch data.primes j p).mp hp
    exact ⟨hh.2.1,by simpa only [pow_succ,mul_comm] using hh.2.2⟩
  have hm := actual_batchMeanLog_bounds S hne (by positivity) hp
  have hlog : Real.log ((2:ℝ)^j)=y := by simp only [Real.log_pow,y]
  have hμ : 1≤FreshEntropy.batchMeanLog S := by rw [hlog] at hm; linarith only [hm.1,hy]
  have hμp : 0<FreshEntropy.batchMeanLog S := by linarith only [hμ]
  have hμup : FreshEntropy.batchMeanLog S≤2*y := by
    rw [Real.log_mul (by norm_num) (by positivity),hlog] at hm
    have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [hm.2,hy,hl2]
  have hcapa := dense_actual_batch_cap S hne (by linarith only [hT]) hp
    (by simpa only [pow_succ,mul_comm] using hdense)
    (by nlinarith only [haδ,pow_pos (by norm_num : (0:ℝ)<2) j] :
      2*(a*(2:ℝ)^j)≤δ*(2:ℝ)^j)
  have hlast : bandScale topParameter (a*(2:ℝ)^j) topIterations=
      topCoefficient a*(2:ℝ)^j := by unfold bandScale topCoefficient; ring
  have hst (k : ℕ) (hk : k≤topIterations) :
      topCoefficient a*(2:ℝ)^j≤bandScale topParameter (a*(2:ℝ)^j) k := by
    rw [←hlast]
    exact bandScale_antitone topParameter_pos.le (by norm_num [topParameter])
      (by positivity) hk
  have hgrowth := hr y hyr
  rw [heq] at hgrowth
  simp only [pow_one,pow_zero,mul_one] at hgrowth
  refine ⟨hne,hT,hμ,hμup,?_,?_,?_⟩
  · intro k hk
    exact hgrowth.2.trans (hst k hk)
  · intro k hk
    exact hgrowth.1.trans (by simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (hst k hk) (pow_pos topParameter_pos 5).le)
  · intro k _
    exact (bandSize_le_start hμp topParameter_pos.le (by norm_num [topParameter])
      (by positivity) k).trans hcapa

/-- One density threshold and actual separated selections work in every window;
all capacities and lattice-threshold guards precede all walk quantifiers. -/
theorem ArithmeticInterface.uniform_multiscale_top_band_batches
    {data : SignedResidueData L} {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} (A : ArithmeticInterface data b e)
    (K : ℕ) (hK : 0<K) (U₀ : ℝ) :
    ∃ c δ a : ℝ, 0<c ∧ 0<δ ∧ 0<a ∧ 2*a≤δ ∧
      ∀ᶠ m : ℕ in atTop, ∃ J : ℕ → Finset ℕ, ∀ w : ℕ,
        c*((100:ℝ)^w*Real.exp m)≤(J w).card ∧
        (∀ i∈J w, ∀ j∈J w, i<j → i+K≤j) ∧
        ∀ j∈J w,
          (100:ℝ)^w*Real.exp m≤(j:ℝ)*Real.log 2 ∧
          (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m) ∧
          δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dyadicPrimeBatch data.primes j).card ∧
          DyadicTopBandReady data a U₀ j := by
  obtain ⟨c,δ,hc,hδ,hbins⟩ := A.uniform_multiscale_dyadic_batches K hK
  let a := δ/4
  have ha : 0<a := by dsimp [a]; positivity
  have haδ : 2*a≤δ := by dsimp [a]; linarith only [hδ]
  have hready := eventually_dense_dyadic_top_band_ready data hδ ha haδ U₀
  have ht : Tendsto (fun m : ℕ => Real.exp (m:ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨c,δ,a,hc,hδ,ha,haδ,?_⟩
  filter_upwards [hbins,ht.eventually hready] with m hm hr
  obtain ⟨J,hJ⟩ := hm
  refine ⟨J,?_⟩
  intro w
  refine ⟨(hJ w).1,(hJ w).2.1,?_⟩
  intro j hj
  obtain ⟨hlo,hhi,hdense⟩ := (hJ w).2.2 j hj
  refine ⟨hlo,hhi,hdense,hr j ?_ hdense⟩
  exact (by nlinarith only [window_power_one w,Real.exp_nonneg (m:ℝ)] :
    Real.exp m≤(100:ℝ)^w*Real.exp m).trans hlo

/-- Density chooses the actual prime batches before every walk; the endpoint
entropy is then proved for the literal top-band kernel schedule. -/
theorem ArithmeticInterface.uniform_multiscale_top_band_entropy
    {data : SignedResidueData L} {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} (A : ArithmeticInterface data b e)
    {D : ℝ} (hD : 1≤D) (K : ℕ) (hK : 0<K) :
    ∃ c δ a : ℝ, 0<c ∧ 0<δ ∧ 0<a ∧ 2*a≤δ ∧
      ∀ᶠ m : ℕ in atTop, ∃ J : ℕ → Finset ℕ, ∀ w : ℕ,
        c*((100:ℝ)^w*Real.exp m)≤(J w).card ∧
        (∀ i∈J w, ∀ j∈J w, i<j → i+K≤j) ∧
        ∀ j∈J w,
          (100:ℝ)^w*Real.exp m≤(j:ℝ)*Real.log 2 ∧
          (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m) ∧
          ∀ (P : TimeLaw) (z : ℕ → L), Function.Injective z →
          (∀ t, dist (planarEmbedding b e (z t))
            (planarEmbedding b e (z (t+1)))≤D) →
          let S := dyadicPrimeBatch data.primes j
          let μ := FreshEntropy.batchMeanLog S
          (1-(1/2:ℝ)^topIterations-80*topParameter)*
            (bandSize μ topParameter (a*(2:ℝ)^j) topIterations:ℝ)*μ≤
          signedPointEntropy data S
            (P.run z (bandLength topParameter (a*(2:ℝ)^j)) topIterations).law
            (fun t => z t.val) (bandSize μ topParameter (a*(2:ℝ)^j) topIterations) := by
  obtain ⟨U₀,_,hband⟩ := uniform_band_geometric_entropy data b e A hD
    topParameter_pos topParameter_small
  obtain ⟨c,δ,a,hc,hδ,ha,haδ,hselection⟩ :=
    A.uniform_multiscale_top_band_batches K hK U₀
  refine ⟨c,δ,a,hc,hδ,ha,haδ,?_⟩
  filter_upwards [hselection] with m hm
  obtain ⟨J,hJ⟩ := hm
  refine ⟨J,?_⟩
  intro w
  refine ⟨(hJ w).1,(hJ w).2.1,?_⟩
  intro j hj
  obtain ⟨hlo,hhi,_,hready⟩ := (hJ w).2.2 j hj
  refine ⟨hlo,hhi,?_⟩
  intro P z hinj hs
  apply hband (dyadicPrimeBatch data.primes j) ((j:ℝ)*Real.log 2)
    (fun p hp => ((mem_dyadicPrimeBatch _ _ _).mp hp).1)
    hready.nonempty hready.mean_lower hready.mean_upper P z hinj hs
    ((2:ℝ)^j) hready.prime_scale
    (fun p hp => ⟨((mem_dyadicPrimeBatch _ _ _).mp hp).2.1,
      by simpa only [pow_succ,mul_comm] using ((mem_dyadicPrimeBatch _ _ _).mp hp).2.2⟩)
    (a*(2:ℝ)^j) topIterations
    (fun k hk => hready.scale_lower k hk.le)
    (fun k hk => hready.relative k hk.le)
    (fun k hk => hready.capacity k hk.le)

/-- Actual dense batches satisfy accurate-grid mean, margin, and capacity
guards uniformly. The fixed lattice guard constant is absorbed by the actual squared grid. -/
theorem eventually_accurate_actual_batch_guards {A B a δ : ℝ}
    (hA : 0<A) (hB : 0<B) (ha : 0<a) (haA : a<A) (hδ : 0<δ) (U₀ : ℝ) :
    ∀ᶠ m : ℕ in atTop, ∀ (S : Finset ℕ) (T : ℝ), S.Nonempty →
      (∀ p∈S, T≤(p:ℝ) ∧ (p:ℝ)≤2*T) →
      δ*T/Real.log (2*T)≤S.card →
      Real.exp (A*Real.exp m)≤T → Real.log T≤B*Real.exp m →
      5≤T ∧ 1≤FreshEntropy.batchMeanLog S ∧
      FreshEntropy.batchMeanLog S≤2*((B+1)*Real.exp m) ∧
      ∀ k≤accurateIterations m,
        U₀≤(accurateGrid m)^2*bandScale (accurateGrid m) (Real.exp (a*Real.exp m)) k ∧
        1280*((B+1)*Real.exp m)≤(accurateGrid m)^5*
          bandScale (accurateGrid m) (Real.exp (a*Real.exp m)) k ∧
        bandSize (FreshEntropy.batchMeanLog S) (accurateGrid m)
          (Real.exp (a*Real.exp m)) k≤S.card := by
  have hlarge := eventually_mul_le_double_exp (a := a/2) (by positivity) (1280*(B+1))
  have hgap := eventually_const_le_exp_mul (a := A-a) (by linarith only [haA])
    (Real.log (2/δ))
  have hfive := eventually_const_le_exp_mul hA 4
  have hfixed := eventually_const_le_exp_mul (a := a/2) (by positivity) U₀
  filter_upwards [eventually_accurate_scale ha 5,eventually_accurate_scale ha 2,
    hlarge,hgap,hfive,hfixed] with m hm5 hm2 hlarge hgap hfour hfixed
  intro S T hne hp hdense hT hThi
  have he1 : 1≤Real.exp (m:ℝ) := Real.one_le_exp_iff.mpr (Nat.cast_nonneg _)
  have hT0 : 0<T := (Real.exp_pos _).trans_le hT
  have hT5 : 5≤T := by
    have hh := Real.add_one_le_exp (A*Real.exp m)
    linarith only [hh,hfour,hT]
  have hm := actual_batchMeanLog_bounds S hne hT0 hp
  have hmean : 1≤FreshEntropy.batchMeanLog S := by
    have hh := Real.log_le_log (Real.exp_pos _) hT
    rw [Real.log_exp] at hh
    linarith only [hh,hm.1,hfour]
  have hl2 : Real.log 2≤1 := by
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  have hmean' : FreshEntropy.batchMeanLog S≤(B+1)*Real.exp m := by
    rw [Real.log_mul (by norm_num) hT0.ne'] at hm
    nlinarith only [hm.2,hThi,hl2,he1]
  have hsize : 2*Real.exp (a*Real.exp m)≤δ*T := by
    have he : Real.exp (a*Real.exp m+Real.log (2/δ))≤Real.exp (A*Real.exp m) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hgap]
    rw [Real.exp_add,Real.exp_log (div_pos (by norm_num) hδ)] at he
    have hh := mul_le_mul_of_nonneg_left (he.trans hT) hδ.le
    have heq : δ*(Real.exp (a*Real.exp m)*(2/δ))=2*Real.exp (a*Real.exp m) := by field_simp
    rwa [heq] at hh
  have hcap := dense_actual_batch_cap S hne (by linarith only [hT5]) hp hdense hsize
  have hlast (k : ℕ) (hk : k≤accurateIterations m) :
      bandScale (accurateGrid m) (Real.exp (a*Real.exp m)) (accurateIterations m)≤
        bandScale (accurateGrid m) (Real.exp (a*Real.exp m)) k :=
    bandScale_antitone (accurateGrid_pos m).le (accurateGrid_le_one m)
      (Real.exp_pos _).le hk
  refine ⟨hT5,hmean,by nlinarith only [hmean',hB,Real.exp_pos (m:ℝ)],?_⟩
  intro k hk
  refine ⟨?_,?_,?_⟩
  · have he := Real.add_one_le_exp ((a/2)*Real.exp m)
    have hb : U₀≤Real.exp ((a/2)*Real.exp m) := by linarith only [he,hfixed]
    exact hb.trans (hm2.trans (mul_le_mul_of_nonneg_left (hlast k hk)
      (sq_nonneg (accurateGrid m))))
  · have hh := hlarge.trans hm5
    simpa only [mul_assoc] using hh.trans (mul_le_mul_of_nonneg_left (hlast k hk)
      (pow_pos (accurateGrid_pos m) 5).le)
  · exact (bandSize_le_start (by linarith only [hmean]) (accurateGrid_pos m).le
      (accurateGrid_le_one m) (Real.exp_nonneg _) k).trans hcap

/-- The actual finite prime supply for a fixed finite number of windows. -/
noncomputable def dyadicPrimePool (data : SignedResidueData L)
    (J : ℕ → Finset ℕ) (W : ℕ) : Finset ℕ :=
  (allBins W J).biUnion (dyadicPrimeBatch data.primes)

lemma dyadicPrimePool_mem_primes (data : SignedResidueData L)
    (J : ℕ → Finset ℕ) (W : ℕ) :
    ∀ p∈dyadicPrimePool data J W, p∈data.primes := by
  intro p hp
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hp
  exact ((mem_dyadicPrimeBatch _ _ _).mp hj).1

lemma dyadicPrimeBatch_subset_pool (data : SignedResidueData L)
    (J : ℕ → Finset ℕ) {W w j : ℕ} (hw : w<W) (hj : j∈J w) :
    dyadicPrimeBatch data.primes j⊆dyadicPrimePool data J W := by
  intro p hp
  apply Finset.mem_biUnion.mpr
  refine ⟨j,?_,hp⟩
  exact Finset.mem_biUnion.mpr ⟨w,Finset.mem_range.mpr hw,hj⟩

/-- For any finite collection of accurate windows strictly below their prime
log windows, A5 supplies the actual batches and all their accurate-band guards.
The threshold depends on the finite window count, never on a walk or start. -/
theorem ArithmeticInterface.uniform_multiscale_accurate_band_batches
    {data : SignedResidueData L} {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} (A : ArithmeticInterface data b e)
    (K : ℕ) (hK : 0<K) (W : ℕ) (a : ℕ → ℝ)
    (ha : ∀ w<W, 0<a w ∧ a w<(100:ℝ)^w) (U₀ : ℝ) :
    ∃ c δ : ℝ, 0<c ∧ 0<δ ∧ ∀ᶠ m : ℕ in atTop,
      ∃ J : ℕ → Finset ℕ, ∀ w<W,
        c*((100:ℝ)^w*Real.exp m)≤(J w).card ∧
        (∀ i∈J w, ∀ j∈J w, i<j → i+K≤j) ∧
        ∀ j∈J w,
          (100:ℝ)^w*Real.exp m≤(j:ℝ)*Real.log 2 ∧
          (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m) ∧
          let S := dyadicPrimeBatch data.primes j
          5≤(2:ℝ)^j ∧ 1≤FreshEntropy.batchMeanLog S ∧
          FreshEntropy.batchMeanLog S≤2*((21/20*(100:ℝ)^w+1)*Real.exp m) ∧
          ∀ k≤accurateIterations m,
            U₀≤(accurateGrid m)^2*bandScale (accurateGrid m) (Real.exp (a w*Real.exp m)) k ∧
            1280*((21/20*(100:ℝ)^w+1)*Real.exp m)≤(accurateGrid m)^5*
              bandScale (accurateGrid m) (Real.exp (a w*Real.exp m)) k ∧
            bandSize (FreshEntropy.batchMeanLog S) (accurateGrid m)
              (Real.exp (a w*Real.exp m)) k≤S.card := by
  obtain ⟨c,δ,hc,hδ,hbins⟩ := A.uniform_multiscale_dyadic_batches K hK
  have hguards := (Finset.range W).eventually_all.mpr (fun w hw =>
    eventually_accurate_actual_batch_guards (A := (100:ℝ)^w)
      (B := 21/20*(100:ℝ)^w) (by positivity) (by positivity)
      (ha w (Finset.mem_range.mp hw)).1 (ha w (Finset.mem_range.mp hw)).2 hδ U₀)
  refine ⟨c,δ,hc,hδ,?_⟩
  filter_upwards [hbins,hguards] with m hm hg
  obtain ⟨J,hJ⟩ := hm
  refine ⟨J,?_⟩
  intro w hw
  refine ⟨(hJ w).1,(hJ w).2.1,?_⟩
  intro j hj
  obtain ⟨hlo,hhi,hdense⟩ := (hJ w).2.2 j hj
  refine ⟨hlo,hhi,?_⟩
  apply hg w (Finset.mem_range.mpr hw) (dyadicPrimeBatch data.primes j) ((2:ℝ)^j)
    (dyadicPrimeBatch_nonempty_of_dense data.primes j hδ hdense)
    (fun p hp => ⟨((mem_dyadicPrimeBatch _ _ _).mp hp).2.1,
      by simpa only [pow_succ,mul_comm] using ((mem_dyadicPrimeBatch _ _ _).mp hp).2.2⟩)
    (by simpa only [pow_succ,mul_comm] using hdense)
  · have heq : Real.exp ((j:ℝ)*Real.log 2)=(2:ℝ)^j := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
    rw [←heq]
    exact Real.exp_le_exp.mpr hlo
  · simpa only [Real.log_pow,mul_assoc] using hhi

lemma actual_batchMeanLog_nonempty {S : Finset ℕ}
    (hmean : 1≤FreshEntropy.batchMeanLog S) : S.Nonempty := by
  by_contra h
  have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp h
  subst S
  norm_num [FreshEntropy.batchMeanLog,Finset.expect] at hmean

/-- The actual accurate-window endpoint bound, with all density, capacity, and
geometric guards discharged before every time law and walk. The finite prime
pool is the explicit `dyadicPrimePool data J W`. -/
theorem ArithmeticInterface.uniform_multiscale_accurate_band_entropy
    {data : SignedResidueData L} {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} (A : ArithmeticInterface data b e)
    {D : ℝ} (hD : 1≤D) (K : ℕ) (hK : 0<K) (W : ℕ)
    (a : ℕ → ℝ) (ha : ∀ w<W, 0<a w ∧ a w<(100:ℝ)^w) :
    ∃ c δ : ℝ, 0<c ∧ 0<δ ∧ ∀ᶠ m : ℕ in atTop,
      ∃ J : ℕ → Finset ℕ, ∃ Q : Finset ℕ,
        Q=dyadicPrimePool data J W ∧ (∀ p∈Q, p∈data.primes) ∧
        ∀ w<W,
          c*((100:ℝ)^w*Real.exp m)≤(J w).card ∧
          (∀ i∈J w, ∀ j∈J w, i<j → i+K≤j) ∧
          ∀ j∈J w,
            dyadicPrimeBatch data.primes j⊆Q ∧
            (100:ℝ)^w*Real.exp m≤(j:ℝ)*Real.log 2 ∧
            (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m) ∧
            ∀ (P : TimeLaw) (z : ℕ → L), Function.Injective z →
            (∀ t, dist (planarEmbedding b e (z t))
              (planarEmbedding b e (z (t+1)))≤D) →
            let S := dyadicPrimeBatch data.primes j
            let μ := FreshEntropy.batchMeanLog S
            (1-91*accurateGrid m)*
              (bandSize μ (accurateGrid m) (Real.exp (a w*Real.exp m))
                (accurateIterations m):ℝ)*μ≤
            signedPointEntropy data S
              (P.run z (bandLength (accurateGrid m) (Real.exp (a w*Real.exp m)))
                (accurateIterations m)).law
              (fun t => z t.val)
              (bandSize μ (accurateGrid m) (Real.exp (a w*Real.exp m))
                (accurateIterations m)) := by
  obtain ⟨c,δ,hc,hδ,hselection⟩ := A.uniform_multiscale_accurate_band_batches K hK W a ha
    (geometricGuardConstant data b e A D)
  refine ⟨c,δ,hc,hδ,?_⟩
  filter_upwards [hselection,eventually_accurate_small (show (0:ℝ)<1/200 by norm_num)]
    with m hm hsmall
  obtain ⟨J,hJ⟩ := hm
  refine ⟨J,dyadicPrimePool data J W,rfl,dyadicPrimePool_mem_primes data J W,?_⟩
  intro w hw
  refine ⟨(hJ w hw).1,(hJ w hw).2.1,?_⟩
  intro j hj
  obtain ⟨hlo,hhi,hT,hmean,hmeanup,hguards⟩ := (hJ w hw).2.2 j hj
  refine ⟨dyadicPrimeBatch_subset_pool data J hw hj,hlo,hhi,?_⟩
  intro P z hinj hs
  let S := dyadicPrimeBatch data.primes j
  let μ := FreshEntropy.batchMeanLog S
  have hactual := explicit_band_geometric_entropy data b e A hD (accurateGrid_pos m) hsmall
    S ((21/20*(100:ℝ)^w+1)*Real.exp m)
    (fun p hp => ((mem_dyadicPrimeBatch _ _ _).mp hp).1)
    (actual_batchMeanLog_nonempty hmean) hmean hmeanup P z hinj hs ((2:ℝ)^j) hT
    (fun p hp => ⟨((mem_dyadicPrimeBatch _ _ _).mp hp).2.1,
      by simpa only [pow_succ,mul_comm] using ((mem_dyadicPrimeBatch _ _ _).mp hp).2.2⟩)
    (Real.exp (a w*Real.exp m)) (accurateIterations m)
    (fun k hk => (hguards k hk.le).1)
    (fun k hk => (hguards k hk.le).2.1)
    (fun k hk => (hguards k hk.le).2.2)
  dsimp only at hactual
  have hcoef : 1-91*accurateGrid m≤1-(1/2:ℝ)^accurateIterations m-80*accurateGrid m := by
    have hh := accurateIterations_error m
    have hg := accurateGrid_pos m
    linarith only [hh,hg]
  have hmass : 0≤(bandSize μ (accurateGrid m) (Real.exp (a w*Real.exp m))
      (accurateIterations m):ℝ)*μ :=
    mul_nonneg (Nat.cast_nonneg _) (by dsimp only [μ]; linarith only [hmean])
  have hcompare := mul_le_mul_of_nonneg_right hcoef hmass
  simp only [←mul_assoc] at hcompare
  exact hcompare.trans hactual

end Entry002
