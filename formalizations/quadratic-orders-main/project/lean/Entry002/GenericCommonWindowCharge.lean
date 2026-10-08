import Entry002.GenericBackwardBatchCharge
import Entry002.GenericWindowTopEntropy
import Entry002.GenericWindowBandSizes

/-! One literal common-window law for every actual selected dyadic batch.
This module composes the proved geometric endpoint entropy, backward residue
coverage, finite posterior selection and actual word-information transport. The finite selection and coverage calculations are
adapted from OpenAI family028, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0), through the
locally proved GenericBackwardBatchCharge and GenericWindowEntropy modules.
Schedule factorization is an equality of actual forward kernels.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Entry002
open OAI.GaussianMoat
open scoped BigOperators Classical
variable {L : Type*} [AddCommGroup L]

lemma common_window_batch_split (a : ℝ) (m : ℕ) (J : ℕ → Finset ℕ)
    {W w j : ℕ} (hw : w < W) (hj : j ∈ J w) :
    ∃ winprefix suffix : List ℕ,
      commonBlocks a m W J = winprefix ++ topBlock a j ++ suffix ++
        middleBlocks a m w J ++ accurateBlock m (1/20) ∧
      suffix.length ≤ (J w).card*topIterations ∧
      (∀ n ∈ suffix, ∃ i ∈ J w, i < j ∧ n ∈ topBlock a i) := by
  obtain ⟨winpre, hwin⟩ := windowBlocks_split a m J hw
  obtain ⟨toppre, toppost, htop, hlen, hpost⟩ := topBlocks_split (a := a) hj
  refine ⟨winpre ++ toppre, toppost, ?_, hlen, hpost⟩
  simp only [commonBlocks, hwin, htop, middleBlocks, List.append_assoc]

lemma common_window_batch_law (z : ℕ → L) (a : ℝ) (m W w j : ℕ)
    (J : ℕ → Finset ℕ) (winprefix suffix : List ℕ) (N : ℕ)
    (hsplit : commonBlocks a m W J = winprefix ++ topBlock a j ++ suffix ++
      middleBlocks a m w J ++ accurateBlock m (1/20)) :
    ((TimeLaw.at 0).advance (commonSchedule z (winprefix ++ topBlock a j) 0)).advance
      (commonSchedule z ((suffix ++ middleBlocks a m w J) ++ accurateBlock m (1/20)) N) =
      (TimeLaw.at 0).advance (commonSchedule z (commonBlocks a m W J) N) := by
  rw [← TimeLaw.advance_then, ← commonSchedule_append]
  congr 2
  simpa only [List.append_assoc] using hsplit.symm


lemma common_window_factor_split (a : ℝ) (m : ℕ) (J : ℕ → Finset ℕ)
    {W w : ℕ} (hw : w < W) :
    ∃ winprefix : List ℕ, commonBlocks a m W J =
      (winprefix ++ topBlocks a (J w)) ++ middleBlocks a m w J ++ accurateBlock m (1/20) := by
  obtain ⟨winprefix, hp⟩ := windowBlocks_split a m J hw
  refine ⟨winprefix, ?_⟩
  simp only [commonBlocks, hp, middleBlocks, List.append_assoc]

lemma common_window_factor_law (z : ℕ → L) (a : ℝ) (m W w : ℕ)
    (J : ℕ → Finset ℕ) (winprefix : List ℕ) (N : ℕ)
    (hsplit : commonBlocks a m W J =
      (winprefix ++ topBlocks a (J w)) ++ middleBlocks a m w J ++ accurateBlock m (1/20)) :
    ((TimeLaw.at 0).advance (commonSchedule z (winprefix ++ topBlocks a (J w)) 0)).advance
      (commonSchedule z (middleBlocks a m w J ++ accurateBlock m (1/20)) N) =
      (TimeLaw.at 0).advance (commonSchedule z (commonBlocks a m W J) N) := by
  rw [← TimeLaw.advance_then, ← commonSchedule_append]
  congr 2
  simpa only [List.append_assoc] using hsplit.symm


lemma batch_collision_short_of_sq {D γ T p : ℝ} {len : ℕ}
    (hD : 0 ≤ D) (hγ : 0 < γ) (hp : 0 ≤ p) (hTp : T ≤ p)
    (hsq : (D*(len : ℝ))^2 < γ^2*T) :
    D*len < γ*Real.sqrt p := by
  have hsqrt := Real.sq_sqrt hp
  have hnonneg := Real.sqrt_nonneg p
  have hmul := mul_le_mul_of_nonneg_left hTp (sq_nonneg γ)
  have hDn : 0 ≤ D*(len : ℝ) := mul_nonneg hD (Nat.cast_nonneg _)
  apply (sq_lt_sq₀ hDn (mul_nonneg hγ.le hnonneg)).mp
  simpa only [mul_pow, hsqrt] using hsq.trans_le hmul


/-- The actual common-window charge. All three entropy endpoints, backward
coverage, sampling floors, and posterior information are derived. The finite
old-label weight is the remaining numerical growth invariant. -/
theorem eventually_common_window_batch_charge (data : SignedResidueData L)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (A : ArithmeticInterface data b e) {D a δ : ℝ} {K : ℕ}
    (hD : 1 ≤ D) (ha : 0 < a) (ha1 : a ≤ 1) (haδ : 2*a ≤ δ)
    (hgap : a ≤ (2:ℝ)^K*topCoefficient a) (W : ℕ) :
    ∀ᶠ m : ℕ in Filter.atTop, ∀ J : ℕ → Finset ℕ,
      (∀ w < W, ∀ j ∈ J w, (100:ℝ)^w*Real.exp m ≤ (j:ℝ)*Real.log 2 ∧
        (j:ℝ)*Real.log 2 ≤ 21/20*((100:ℝ)^w*Real.exp m) ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1)) ≤ (dyadicPrimeBatch data.primes j).card) →
      (∀ w < W, ∀ i ∈ J w, ∀ j ∈ J w, i < j → i+K ≤ j) →
      ∀ z : ℕ → L, Function.Injective z →
      (∀ t, dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1))) ≤ D) →
      (∀ t, z t ∈ avoiding data (dyadicPrimePool data J W)) →
      ∀ w < W, ∀ j ∈ J w, ∀ F : Finset (ℕ × Bool),
      F ⊆ dyadicPrimePool data J W ×ˢ (Finset.univ : Finset Bool) →
      F.sum (fun i => Real.log i.1) ≤ (topCoefficient a/4)*(2:ℝ)^j/10000 →
      ∃ G : Finset (ℕ × Bool), F ⊆ G ∧
        G ⊆ dyadicPrimePool data J W ×ˢ (Finset.univ : Finset Bool) ∧
        G ⊆ F ∪ (dyadicPrimeBatch data.primes j ×ˢ (Finset.univ : Finset Bool)) ∧
        (G \ F).card ≤ bandSize
          (FreshEntropy.batchMeanLog (dyadicPrimeBatch data.primes j))
          topParameter (a*(2:ℝ)^j) topIterations ∧
        G.sum (fun i => Real.log i.1) ≤ F.sum (fun i => Real.log i.1) +
          2*(dyadicPrimeBatch data.primes j).sum (fun p => Real.log p) ∧
        windowBatchRate (topCoefficient a/4) j ≤
          ((TimeLaw.at 0).advance (commonSchedule z (commonBlocks a m W J)
            (windowSmoothing W m))).info
          (fun t => residueFamilyHom data G (z t)) (incrementWord z (batchWordLength j))
          (fun t => residueFamilyHom data F (z t)) / batchWordLength j := by
  have hδ : 0 < δ := by linarith only [ha, haδ]
  obtain ⟨γ, hγ, hcollision⟩ := A.collision
  have hc : 0 < topCoefficient a/4 := div_pos (topCoefficient_pos ha) (by norm_num)
  have htop := (Finset.range W).eventually_all.mpr (fun w _ =>
    (windowScale_tendsto w).eventually
      (eventually_window_top_entropy data b e A hD ha haδ hgap))
  have hband := (Finset.range W).eventually_all.mpr (fun w hw =>
    eventually_window_band_entropy data b e A hD ha.le ha1 hδ W w
      (Finset.mem_range.mp hw))
  have hsizes := (Finset.range W).eventually_all.mpr (fun w hw =>
    eventually_window_band_sizes data hδ W w (Finset.mem_range.mp hw))
  have htail := (Finset.range W).eventually_all.mpr (fun w hw =>
    eventually_window_tail_bounds b e hD ha.le ha1 W w (Finset.mem_range.mp hw))
  filter_upwards [htop, hband, hsizes, htail,
    eventually_common_window_batch_arithmetic hD hγ hc W,
    eventually_common_window_backward_arithmetic W,
    eventually_common_window_large (100:ℝ)] with m htop hband hsizes htail hsample hback hlarge
  intro J hJ hsep z hz hs havoid w hw j hj F hFpool hbudget
  let X : ℝ := (100:ℝ)^w*Real.exp m
  let S := dyadicPrimeBatch data.primes j
  let μ := FreshEntropy.batchMeanLog S
  let q := bandSize μ topParameter (a*(2:ℝ)^j) topIterations
  let qmid := bandSize μ (accurateGrid m)
    (Real.exp (((100:ℝ)^w/4)*Real.exp m)) (accurateIterations m)
  let qbot := bandSize μ (accurateGrid m)
    (Real.exp ((1/20)*Real.exp m)) (accurateIterations m)
  obtain ⟨winprefix, hsplit⟩ := common_window_factor_split a m J hw
  let P := (TimeLaw.at 0).advance (commonSchedule z (winprefix ++ topBlocks a (J w)) 0)
  have hdata := hJ w hw j hj
  have hne : S.Nonempty := dyadicPrimeBatch_nonempty_of_dense data.primes j hδ hdata.2.2
  have hS : ∀ p ∈ S, p ∈ data.primes := fun p hp => ((mem_dyadicPrimeBatch _ _ _).mp hp).1
  have hSpool : S ⊆ dyadicPrimePool data J W := dyadicPrimeBatch_subset_pool data J hw hj
  have hF : ∀ i ∈ F, i.1 ∈ data.primes := by
    intro i hi
    exact dyadicPrimePool_mem_primes data J W i.1 (Finset.mem_product.mp (hFpool hi)).1
  obtain ⟨_, hqcap, hμ1, hμup, hqsize, hAnchor⟩ :=
    htop w (Finset.mem_range.mpr hw) (J w) winprefix (hsep w hw) (hJ w hw) j hj
  have hμ : 0 < μ := by linarith only [hμ1]
  obtain ⟨hmidpos, hmidcap, hbotpos, hbotcap⟩ :=
    hsizes w (Finset.mem_range.mpr hw) J hJ j hj
  obtain ⟨_, _, _, hpostball, hfullball⟩ :=
    htail w (Finset.mem_range.mpr hw) J (fun i hi k hk => (hJ i hi k hk).2.1)
  have hp (i : BatchSignedIndex S) :
      (2:ℝ)^j ≤ (signedBatchPrime S i.2 : ℝ) ∧
      (signedBatchPrime S i.2 : ℝ) ≤ 2*(2:ℝ)^j := by
    have hi := (mem_dyadicPrimeBatch _ _ _).mp (signedBatchPrime_mem S i.2)
    exact ⟨hi.2.1, by simpa only [pow_succ, mul_comm] using hi.2.2⟩
  have hT : Real.exp X ≤ (2:ℝ)^j := by
    rw [← Real.exp_log (by positivity : (0:ℝ)<2^j), Real.log_pow]
    exact Real.exp_le_exp.mpr hdata.1
  have hThi : (2:ℝ)^j ≤ Real.exp (21/20*X) := by
    rw [← Real.exp_log (by positivity : (0:ℝ)<2^j), Real.log_pow]
    exact Real.exp_le_exp.mpr hdata.2.1
  have hpi (i : BatchSignedIndex S) : 0 < (signedBatchPrime S i.2 : ℝ) :=
    (Real.exp_pos X).trans_le (hT.trans (hp i).1)
  have hback' := fun i : BatchSignedIndex S =>
    hback w hw μ
      (Real.log (wordStepBall b e (D*((accurateBlock m (1/20)).sum+windowSmoothing W m))).card)
      (signedBatchPrime S i.2 : ℝ) hμ hμup hpostball
      (hT.trans (hp i).1)
      ((hp i).2.trans (mul_le_mul_of_nonneg_left hThi (by norm_num)))
  let i₀ : BatchSignedIndex S := (fun _ => true, ⟨0,hne.card_pos⟩)
  obtain ⟨hnSample, hlen, hshortsq, hr, hLN, hsampfloor, hsampmargin⟩ :=
    hsample w hw j hdata.1 hdata.2.1
  have hK : ∀ t, (1-91*accurateGrid m)*(qmid:ℝ)*batchMeanLog S ≤
      signedPointEntropy data S ((commonSchedule z (middleBlocks a m w J) 0).law t)
        (fun u => z (t+u.val)) qmid := by
    intro t
    have hh := (hband w (Finset.mem_range.mpr hw) J hJ j hj z hz hs (TimeLaw.at t)).1
    simpa only [signedPointEntropy_exact_start, qmid, qbot, μ, S,
      FreshEntropy.batchMeanLog, batchMeanLog] using hh
  have hR : ∀ t, (1-91*accurateGrid m)*(qbot:ℝ)*batchMeanLog S ≤
      signedPointEntropy data S ((commonSchedule z (accurateBlock m (1/20)) (windowSmoothing W m)).law t)
        (fun u => z (t+u.val)) qbot := by
    intro t
    have hh := (hband w (Finset.mem_range.mpr hw) J hJ j hj z hz hs (TimeLaw.at t)).2
    simpa only [signedPointEntropy_exact_start, qmid, qbot, μ, S,
      FreshEntropy.batchMeanLog, batchMeanLog] using hh
  have hqsize' : (topCoefficient a/4)*(2:ℝ)^j/Real.log ((2:ℝ)^j) ≤ (q:ℝ) := by
    convert hqsize using 1
    ring
  have hmargin := hsampmargin (q:ℝ) μ
    (Real.log (wordStepBall b e
      (D*((middleBlocks a m w J++accurateBlock m (1/20)).sum+windowSmoothing W m))).card)
    (F.sum (fun i => Real.log i.1)) hμup hqsize' hfullball hbudget
  obtain ⟨G, hFG, hpool, hlocal, _, hcard, hweight, hinfo, _⟩ :=
    exists_positive_dyadic_backward_batch_charge data S hne hS b e z
      (middleBlocks a m w J) (accurateBlock m (1/20)) (windowSmoothing W m) P
      J W hSpool F hF hFpool (by linarith only [hD]) hs hz
      (fun t p hp => havoid t p (hSpool hp)) hcollision
      (coverageRepetitions_pos X) hmidpos hmidcap hbotpos hbotcap hqcap hlen hLN
      (fun i => (Real.exp_le_exp.mpr (hlarge w)).trans (hT.trans (hp i).1))
      hK hR (hback' i₀).2.1 (hback' i₀).2.2.1 (hback' i₀).2.2.2.1
      (fun i => (hback' i).2.2.2.2)
      (fun i => batch_collision_short_of_sq (by linarith only [hD]) hγ
        (hpi i).le (hp i).1 hshortsq)
      (fun i => (hsampfloor _ (hpi i) (hp i).2).1)
      (hAnchor (TimeLaw.at 0) z hz hs) (packageRepetitions j) hnSample
      (by positivity) hr
      (fun i => by simpa only [mul_div_assoc] using (hsampfloor _ (hpi i) (hp i).2).2)
      (by simpa only [commonSchedule_bound, Nat.cast_add, q, μ, S,
        FreshEntropy.batchMeanLog, batchMeanLog] using hmargin)
  refine ⟨G, hFG, hpool, hlocal, hcard, hweight, ?_⟩
  dsimp only [P] at hinfo
  simpa only [common_window_factor_law z a m W w J winprefix (windowSmoothing W m) hsplit] using hinfo

end Entry002
