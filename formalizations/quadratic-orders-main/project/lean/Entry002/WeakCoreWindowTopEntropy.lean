import Entry002.GenericWindowEntropy
import Entry002.ArithmeticCore
import Entry002.GenericWindowTopEntropy
import Entry002.WeakCoreWindowEntropy

/-! Core-only replay of the round-five owned `GenericWindowTopEntropy` source.
All original proof bodies, mathematical objects, and source-license provenance
are retained; the arithmetic premise is exactly A1--A4. This new namespace
does not construct the former natural-density field. -/


/-! Actual top-window anchor entropy. Adapted from family028
WindowParameters.lean lines 276--341, replacing EntropyBand certificates
by proved true-lattice endpoint entropy and true suffix-alphabet costs.
-/
set_option autoImplicit false
namespace Entry002.WeakA5
open Module Filter
open OAI.GaussianMoat
open scoped BigOperators Classical
variable {L : Type*} [AddCommGroup L]

/-- Every selected actual top batch has high entropy after the entire top
window, including all its smaller selected bins. The initial schedule is
arbitrary and the threshold is independent of the walk and starting law. -/
theorem eventually_window_top_entropy (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (A : ArithmeticCore data b e) {D a δ : ℝ} {K : ℕ}
    (hD : 1≤D) (ha : 0<a) (haδ : 2*a≤δ)
    (hgap : a≤(2:ℝ)^K*topCoefficient a) :
    ∀ᶠ X : ℝ in atTop, ∀ (J : Finset ℕ) (initial : List ℕ),
      (∀i∈J,∀j∈J,i<j → i+K≤j) →
      (∀j∈J,X≤(j:ℝ)*Real.log 2 ∧ (j:ℝ)*Real.log 2≤21/20*X ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dyadicPrimeBatch data.primes j).card) →
      ∀j∈J,
      let S := dyadicPrimeBatch data.primes j
      let μ := _root_.Entry002.FreshEntropy.batchMeanLog S
      let q := bandSize μ topParameter (a*(2:ℝ)^j) topIterations
      0<q ∧ q≤S.card ∧ 1≤μ ∧ μ≤2*X ∧
      topCoefficient a*(2:ℝ)^j/(4*Real.log ((2:ℝ)^j))≤(q:ℝ) ∧
      ∀(P : TimeLaw)(z : ℕ → L),Function.Injective z →
      (∀t,dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1)))≤D) →
      (1-1/10000)*(q:ℝ)*μ≤signedPointEntropy data S
        (P.advance (commonSchedule z (initial++topBlocks a J) 0)).law
        (fun t=>z t.val) q := by
  have hδ : 0<δ := by linarith only [ha,haδ]
  have hg := topParameter_pos
  have hC := topCoefficient_pos ha
  let U₀ := geometricGuardConstant data b e A D/topParameter^2
  have hready := eventually_dense_dyadic_top_band_ready data hδ ha haδ U₀
  have hlen := eventually_poly_le_exp (100:ℝ)
    (a := topParameter*topCoefficient a) (mul_pos hg hC) 1
  have hconstant := eventually_poly_le_exp
    (Real.log (_root_.Entry002.displacementPackingConstant b e)+2*Real.log D)
    (a := topParameter*topCoefficient a) (mul_pos hg hC) 0
  obtain ⟨x₀,h₀⟩ := eventually_atTop.mp ((hready.and hlen).and hconstant)
  filter_upwards [eventually_ge_atTop (max x₀ 2)] with X hX
  intro J initial hsep hJ j hj
  have hX2 : 2≤X := (le_max_right _ _).trans hX
  have hX0 : x₀≤X := (le_max_left _ _).trans hX
  let y : ℝ := (j:ℝ)*Real.log 2
  let T : ℝ := (2:ℝ)^j
  let S := dyadicPrimeBatch data.primes j
  let μ := _root_.Entry002.FreshEntropy.batchMeanLog S
  let V := bandScale topParameter (a*T) topIterations
  let H := topParameter*V
  have hXY : X≤y := (hJ j hj).1
  obtain ⟨⟨hready,hlen⟩,hconstant⟩ := h₀ y (hX0.trans hXY)
  have hr := hready j le_rfl (hJ j hj).2.2
  have hT : Real.exp y=T := by
    dsimp only [y,T]
    rw [Real.exp_nat_mul,Real.exp_log (by norm_num)]
  have hV : V=topCoefficient a*T := by unfold V bandScale topCoefficient; ring
  have hmeanpos : 0<μ := by dsimp only [μ]; linarith only [hr.mean_lower]
  have hmeanup : μ≤2*X := by
    have hh := actual_batchMeanLog_bounds S hr.nonempty (by positivity : 0<T)
      (fun p hp => ⟨((mem_dyadicPrimeBatch _ _ _).mp hp).2.1,
        by simpa only [pow_succ,mul_comm] using ((mem_dyadicPrimeBatch _ _ _).mp hp).2.2⟩)
    rw [Real.log_mul (by norm_num) (by positivity),Real.log_pow] at hh
    have hl2 := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    dsimp only [μ,S,T] at ⊢
    linarith only [hh.2,(hJ j hj).2.1,hl2,hX2]
  have hVL : 2*μ≤V := by
    have hh := hr.relative topIterations le_rfl
    have hg5 : topParameter^5≤1 := pow_le_one₀ hg.le (by norm_num [topParameter])
    have hVp : 0<V := bandScale_pos hg (mul_pos ha (by positivity)) _
    have hp := mul_le_mul_of_nonneg_right hg5 hVp.le
    have hmuup : μ≤2*y := hr.mean_upper
    change 1280*y≤topParameter^5*V at hh
    nlinarith only [hh,hmuup,hp,hmeanpos]
  have hmass := bandSize_mul_half hmeanpos hVL
  have hqpos : 0<bandSize μ topParameter (a*T) topIterations := by
    have hVp : 0<V := bandScale_pos hg (mul_pos ha (by positivity)) _
    change V/2≤_ at hmass
    have hq : (0:ℝ)<bandSize μ topParameter (a*T) topIterations := by
      nlinarith only [hmass,hVp,hmeanpos]
    exact_mod_cast hq
  have hqcap := hr.capacity topIterations le_rfl
  have hlog : 0<Real.log T := by
    rw [←hT,Real.log_exp]
    linarith only [hXY,hX2]
  have hμT : μ≤2*Real.log T := by
    rw [←hT,Real.log_exp]
    exact hr.mean_upper
  have hsize := bandSize_lower_of_scale hmeanpos hlog hμT hVL
    (le_of_eq hV.symm)
  refine ⟨hqpos,hqcap,hr.mean_lower,hmeanup,hsize,?_⟩
  intro P z hinj hs
  obtain ⟨pre,post,he,hpl,hpm⟩ := topBlocks_split (a := a) hj
  have hcard := narrow_bins_card hX2 J (fun i hi => (hJ i hi).2.1)
  have hlen' : (post.length+2:ℝ)≤Real.exp H := by
    have hp : (post.length:ℝ)≤(J.card:ℝ)*topIterations := by exact_mod_cast hpl
    simp only [pow_one,hT] at hlen
    have hexp := Real.add_one_le_exp H
    norm_num only [topIterations,Nat.cast_ofNat] at hp
    dsimp only [H] at hexp ⊢
    rw [hV] at hexp ⊢
    nlinarith only [hp,hcard,hlen,hexp,hXY,hX2]
  have hpst : ∀n∈post,(n:ℝ)≤Real.exp H := by
    intro n hn
    obtain ⟨i,hi,hij,hni⟩ := hpm n hn
    dsimp only [H]; rw [hV]
    simpa only [T,mul_assoc] using topBlock_separated ha hgap (hsep i hi j hj hij) n hni
  have hH0 : 0≤H := (mul_pos hg (bandScale_pos hg (mul_pos ha (by positivity)) _)).le
  have hlenlog := Real.log_le_log (by positivity : (0:ℝ)<(post.length:ℝ)+1)
    (by linarith only [hlen'] : (post.length:ℝ)+1≤Real.exp H)
  rw [Real.log_exp] at hlenlog
  have hcost := actual_schedule_zero_cost_le b e hD hH0 post hpst hlenlog
  have hfixed : Real.log (_root_.Entry002.displacementPackingConstant b e)+2*Real.log D≤H := by
    simp only [pow_zero,mul_one,hT] at hconstant
    dsimp only [H]; rw [hV]
    simpa only [mul_assoc] using hconstant
  have hcost' : Real.log (wordStepBall b e (D*(post.sum+0))).card≤
      (10*topParameter)*(bandSize μ topParameter (a*T) topIterations:ℝ)*μ := by
    simp only [add_zero]
    change V/2≤_ at hmass
    dsimp only [H] at hcost hfixed
    nlinarith only [hcost,hfixed,hmass,hg]
  have hband := commonSchedule_subband_geometric_entropy data b e A hD hg
    topParameter_small S y
    (fun p hp => ((mem_dyadicPrimeBatch _ _ _).mp hp).1)
    hr.nonempty hr.mean_lower hr.mean_upper P z hinj hs T hr.prime_scale
    (fun p hp => ⟨((mem_dyadicPrimeBatch _ _ _).mp hp).2.1,
      by simpa only [pow_succ,mul_comm] using ((mem_dyadicPrimeBatch _ _ _).mp hp).2.2⟩)
    (a*T) topIterations (initial++pre) post 0 (10*topParameter)
    (fun k hk => by
      have hh := (div_le_iff₀ (sq_pos_of_pos hg)).mp (hr.scale_lower k hk.le)
      simpa only [U₀,mul_comm] using hh)
    (fun k hk => hr.relative k hk.le)
    (fun k hk => hr.capacity k hk.le)
    (by simpa only [Nat.cast_zero,add_zero] using hcost')
  dsimp only at hband
  have hcoef : 1-1/10000≤1-(1/2:ℝ)^topIterations-80*topParameter-10*topParameter := by
    linarith only [top_deficit]
  have hmass0 : 0≤(bandSize μ topParameter (a*T) topIterations:ℝ)*μ :=
    mul_nonneg (Nat.cast_nonneg _) hmeanpos.le
  have hh := (mul_le_mul_of_nonneg_right hcoef hmass0).trans
    (by simpa only [mul_assoc] using hband)
  have heq : initial++topBlocks a J=(initial++pre)++topBlock a j++post := by
    rw [he]
    simp only [List.append_assoc]
  rw [heq]
  dsimp only [μ,S,T] at hh
  rw [←mul_assoc] at hh
  exact hh

end Entry002.WeakA5
