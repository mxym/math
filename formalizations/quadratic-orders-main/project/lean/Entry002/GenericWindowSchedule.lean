import Entry002.GenericDensityBands

/-! Literal common-window lists and actual metric-ball suffix costs.
Adapted from pinned family028 CommonBlocks.lean lines 10--139 and
Smoothing.lean lines 108--145, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.
The geometric constants below come from the arbitrary actual rank-two lattice.
-/
set_option autoImplicit false
namespace Entry002
open Module Filter
open OAI.GaussianMoat
open scoped BigOperators Classical
variable {L : Type*} [AddCommGroup L]

theorem eventually_suffix_cost_constant {D a b C A : ℝ} (hD : 0<D) (ha : 0<a) (hab : a<b) :
    ∀ᶠ X : ℝ in atTop, ∀ ns : List ℕ, ∀ N : ℕ,
      1≤ns.sum+N → (ns.length+2:ℝ)≤Real.exp X →
      (∀ n∈ns, (n:ℝ)≤Real.exp (Real.exp (a*X))) →
      (N:ℝ)+1≤Real.exp (C*X) →
      A+2*Real.log (D*(ns.sum+N))≤Real.exp (b*X) := by
  have hp := eventually_poly_le_exp_linear
    (|A|+2*|Real.log D|+2*|1+C|) ha 1
  have hres := eventually_mul_exp_le_exp hab 3
  filter_upwards [hp,hres,eventually_ge_atTop (1:ℝ)] with X hp hres hX
  intro ns N hs hl ho hN
  have hlog := schedule_log_bound ns N (Real.exp_nonneg (a*X)) ho
  have hl' : Real.log ((ns.length:ℝ)+1)≤X := by
    have hh := Real.log_le_log (by positivity : 0<(ns.length:ℝ)+1) (by linarith only [hl] : (ns.length:ℝ)+1≤Real.exp X)
    rwa [Real.log_exp] at hh
  have hN' : Real.log ((N:ℝ)+1)≤C*X := by
    have hh := Real.log_le_log (by positivity : 0<(N:ℝ)+1) hN
    rwa [Real.log_exp] at hh
  have hspos : (0:ℝ)<(ns.sum+N:ℕ) := by exact_mod_cast (show 0<ns.sum+N by omega)
  have hs' : Real.log ((ns.sum+N:ℕ):ℝ)≤Real.log ((ns.sum+N:ℕ)+1) :=
    Real.log_le_log hspos (by push_cast; linarith)
  simp only [Nat.cast_add] at hspos hs' hlog
  rw [Real.log_mul hD.ne' hspos.ne']
  have hc : A+2*Real.log D+2*(1+C)*X≤Real.exp (a*X) := by
    simp only [pow_one] at hp
    have h1 := le_abs_self (A)
    have h2 := le_abs_self (Real.log D)
    have h3 := le_abs_self (1+C)
    nlinarith only [hp,hX,h1,h2,h3,abs_nonneg (A),abs_nonneg (Real.log D)]
  nlinarith only [hlog,hl',hN',hs',hc,hres]

/-- The suffix alphabet is the true planar displacement ball. -/
theorem eventually_actual_suffix_cost (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) {D a c C : ℝ}
    (hD : 1≤D) (ha : 0<a) (hac : a<c) :
    ∀ᶠ X : ℝ in atTop, ∀ ns : List ℕ, ∀ N : ℕ,
      1≤ns.sum+N → (ns.length+2:ℝ)≤Real.exp X →
      (∀ n∈ns, (n:ℝ)≤Real.exp (Real.exp (a*X))) →
      (N:ℝ)+1≤Real.exp (C*X) →
      Real.log (wordStepBall b e (D*(ns.sum+N))).card≤Real.exp (c*X) := by
  filter_upwards [eventually_suffix_cost_constant
    (A := Real.log (displacementPackingConstant b e))
    (C := C) (by linarith only [hD] : 0<D) ha hac] with X hX
  intro ns N hpos hlen hops hN
  have hrad : 1≤D*(ns.sum+N:ℕ) :=
    one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast hpos)
  have hh := ((displacementPackingConstant_spec b e).2 _ hrad).trans
    (by simpa only [Nat.cast_add] using hX ns N hpos hlen hops hN)
  simpa only [Nat.cast_add] using hh

noncomputable def commonBlocks (a : ℝ) (m W : ℕ) (J : ℕ → Finset ℕ) : List ℕ :=
  windowBlocks a m J W++accurateBlock m (1/20)

noncomputable def middleBlocks (a : ℝ) (m w : ℕ) (J : ℕ → Finset ℕ) : List ℕ :=
  accurateBlock m ((100:ℝ)^w/4)++windowBlocks a m J w

lemma windowScale_tendsto (w : ℕ) :
    Tendsto (fun m : ℕ => (100:ℝ)^w*Real.exp m) atTop atTop :=
  (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)

lemma commonBlocks_length {a : ℝ} {m W : ℕ} (J : ℕ → Finset ℕ) (hm : 2≤Real.exp m)
    (hJ : ∀ w<W, ∀ j∈J w, (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) :
    ((commonBlocks a m W J).length:ℝ)+2≤
      (W:ℝ)*(60*(100:ℝ)^W*Real.exp m+4*(m:ℝ)^2)+4*(m:ℝ)^2+2 := by
  have hh := windowBlocks_length_bound_of_bins (a := a) J hm hJ
  simp only [commonBlocks,List.length_append,accurateBlock,List.length_ofFn,
    accurateIterations,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
  linarith only [hh]

lemma middleBlocks_length_le {a : ℝ} {m W w : ℕ} (J : ℕ → Finset ℕ) (hw : w<W) :
    (middleBlocks a m w J).length≤(windowBlocks a m J W).length := by
  obtain ⟨pre,he⟩ := windowBlocks_split a m J hw
  simp only [middleBlocks,he,List.length_append]
  omega

theorem eventually_window_tail_bounds (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) {D a : ℝ} (hD : 1≤D) (ha : 0≤a) (ha1 : a≤1)
    (W w : ℕ) (hw : w<W) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ → Finset ℕ,
      (∀ i<W, ∀ j∈J i, (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m)) →
      ((commonBlocks a m W J).length:ℝ)+2≤Real.exp (Real.exp m) ∧
      (windowSmoothing W m:ℝ)≤Real.exp (Real.exp ((1/100)*Real.exp m)) ∧
      ((windowBlocks a m J w).length+2:ℝ)≤Real.exp (Real.exp (((100:ℝ)^w/50)*Real.exp m)) ∧
      Real.log (wordStepBall b e (D*((accurateBlock m (1/20)).sum+windowSmoothing W m))).card≤
        Real.exp (3/50*((100:ℝ)^w*Real.exp m)) ∧
      Real.log (wordStepBall b e (D*((middleBlocks a m w J++accurateBlock m (1/20)).sum+windowSmoothing W m))).card≤
        Real.exp (13/50*((100:ℝ)^w*Real.exp m)) := by
  have hN := eventually_mul_le_double_exp (a := 1/100) (by norm_num) (20*(100:ℝ)^W+2)
  have hlen := eventually_mul_le_double_exp (a := 1/100) (by norm_num) 1
  have ht := windowScale_tendsto w
  have hbot := ht.eventually (eventually_actual_suffix_cost b e (D := D) (a := 1/20) (c := 3/50)
    (C := 20*(100:ℝ)^W+2) hD (by norm_num) (by norm_num))
  have hrest := ht.eventually (eventually_actual_suffix_cost b e (D := D) (a := 1/4) (c := 13/50)
    (C := 20*(100:ℝ)^W+2) hD (by norm_num) (by norm_num))
  have hm2 := (windowScale_tendsto 0).eventually (eventually_ge_atTop (2:ℝ))
  filter_upwards [eventually_window_length W,hN,hlen,hbot,hrest,hm2] with m hm hN hlen hbot hrest hm2
  intro J hJ
  simp only [one_mul] at hlen
  simp only [pow_zero,one_mul] at hm2
  have hl := (commonBlocks_length (a := a) J hm2 hJ).trans hm
  have hpow := window_power_one w
  have hX : Real.exp (m:ℝ)≤(100:ℝ)^w*Real.exp m := by nlinarith only [hpow,Real.exp_pos (m:ℝ)]
  have hNsmall : (windowSmoothing W m:ℝ)≤Real.exp (Real.exp ((1/100)*Real.exp m)) := by
    have hN' := (windowSmoothing_bounds W m).2.trans (Real.exp_le_exp.mpr hN)
    linarith only [hN']
  have hlw : ((windowBlocks a m J w).length+2:ℝ)≤Real.exp (Real.exp (((100:ℝ)^w/50)*Real.exp m)) := by
    have hh : (windowBlocks a m J w).length≤(commonBlocks a m W J).length := by
      obtain ⟨pre,he⟩ := windowBlocks_split a m J hw
      simp only [commonBlocks,he,List.length_append]; omega
    have harg : Real.exp (m:ℝ)≤Real.exp (((100:ℝ)^w/50)*Real.exp m) := by
      apply hlen.trans (Real.exp_le_exp.mpr _)
      nlinarith only [hpow,Real.exp_pos (m:ℝ)]
    exact (add_le_add (by exact_mod_cast hh : ((windowBlocks a m J w).length:ℝ)≤(commonBlocks a m W J).length) (le_refl (2:ℝ))) |>.trans (hl.trans (Real.exp_le_exp.mpr harg))
  have hNs : (windowSmoothing W m:ℝ)+1≤Real.exp ((20*(100:ℝ)^W+2)*((100:ℝ)^w*Real.exp m)) :=
    (windowSmoothing_bounds W m).2.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hX (by positivity)))
  have hbLen : ((accurateBlock m (1/20)).length+2:ℝ)≤Real.exp ((100:ℝ)^w*Real.exp m) := by
    have hh : (accurateBlock m (1/20)).length≤(commonBlocks a m W J).length := by simp [commonBlocks]
    exact (add_le_add (by exact_mod_cast hh : ((accurateBlock m (1/20)).length:ℝ)≤(commonBlocks a m W J).length) (le_refl (2:ℝ))) |>.trans (hl.trans (Real.exp_le_exp.mpr hX))
  have hrLen : ((middleBlocks a m w J++accurateBlock m (1/20)).length+2:ℝ)≤Real.exp ((100:ℝ)^w*Real.exp m) := by
    have hh := middleBlocks_length_le (a := a) (m := m) J hw
    have hh' : (middleBlocks a m w J++accurateBlock m (1/20)).length≤(commonBlocks a m W J).length := by
      simp only [commonBlocks,List.length_append]; omega
    exact (add_le_add (by exact_mod_cast hh' : ((middleBlocks a m w J++accurateBlock m (1/20)).length:ℝ)≤(commonBlocks a m W J).length) (le_refl (2:ℝ))) |>.trans (hl.trans (Real.exp_le_exp.mpr hX))
  have hbOps : ∀ n∈accurateBlock m (1/20), (n:ℝ)≤Real.exp (Real.exp ((1/20)*((100:ℝ)^w*Real.exp m))) := by
    apply accurateBlock_bound (accurateGrid_le_one m)
    exact (mul_le_of_le_one_left (Real.exp_nonneg _) (accurateGrid_le_one m)).trans
      (Real.exp_le_exp.mpr (by linarith only [hX]))
  have hrOps : ∀ n∈middleBlocks a m w J++accurateBlock m (1/20), (n:ℝ)≤Real.exp (Real.exp ((1/4)*((100:ℝ)^w*Real.exp m))) := by
    intro n hn
    rcases List.mem_append.mp hn with hn|hn
    · rcases List.mem_append.mp hn with hn|hn
      · apply accurateBlock_bound (accurateGrid_le_one m) _ n hn
        simpa only [div_mul_eq_mul_div,mul_assoc,one_mul] using
          (mul_le_of_le_one_left (Real.exp_nonneg (((100:ℝ)^w/4)*Real.exp m)) (accurateGrid_le_one m))
      · exact (smaller_window_operations ha ha1 m w J (fun i hi => hJ i (hi.trans hw)) n hn).trans
          (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith only [show 0≤(100:ℝ)^w*Real.exp m by positivity] : ((100:ℝ)^w/50)*Real.exp m≤(1/4)*((100:ℝ)^w*Real.exp m))))
    · exact (hbOps n hn).trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith only [show 0≤(100:ℝ)^w*Real.exp m by positivity] : (1/20)*((100:ℝ)^w*Real.exp m)≤(1/4)*((100:ℝ)^w*Real.exp m))))
  exact ⟨hl,hNsmall,hlw,
    hbot _ _ (by have := windowSmoothing_pos W m; omega) hbLen hbOps hNs,
    hrest _ _ (by have := windowSmoothing_pos W m; omega) hrLen hrOps hNs⟩


/-- Monotonicity for the actual nonempty metric-ball alphabet. -/
lemma wordStepBall_log_card_mono (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) {R R' : ℝ} (hR : 0≤R) (h : R≤R') :
    Real.log (wordStepBall b e R).card≤Real.log (wordStepBall b e R').card := by
  have hpos : (0:ℝ)<(wordStepBall b e R).card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0,by simpa only
      [mem_wordStepBall,planarEmbedding_zero,norm_zero] using hR⟩
  apply Real.log_le_log hpos
  exact_mod_cast Finset.card_le_card (fun x hx =>
    (mem_wordStepBall b e R' x).mpr (((mem_wordStepBall b e R x).mp hx).trans h))

/-- Derived cost for a suffix whose operations, list length, and smoothing
length have logarithms bounded by H. This includes empty suffixes. -/
theorem actual_schedule_cost_le (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) {D H : ℝ} (hD : 1≤D) (hH : 0≤H)
    (ns : List ℕ) (N : ℕ) (hops : ∀n∈ns,(n:ℝ)≤Real.exp H)
    (hlen : Real.log ((ns.length:ℝ)+1)≤H)
    (hN : Real.log ((N:ℝ)+1)≤H+Real.log 2) :
    Real.log (wordStepBall b e (D*(ns.sum+N))).card≤
      Real.log (displacementPackingConstant b e)+2*Real.log D+2*Real.log 2+6*H := by
  have hD0 : 0<D := by linarith only [hD]
  have hrad : 1≤D*((ns.sum+N:ℕ)+1) :=
    one_le_mul_of_one_le_of_one_le hD (by exact_mod_cast Nat.succ_pos (ns.sum+N))
  have hc := (displacementPackingConstant_spec b e).2 _ hrad
  rw [Real.log_mul hD0.ne' (by positivity)] at hc
  have hlog := schedule_log_bound ns N hH hops
  have hm := wordStepBall_log_card_mono b e
    (by positivity : 0≤D*(ns.sum+N))
    (by push_cast; nlinarith only [hD0] : D*(ns.sum+N)≤D*((ns.sum+N:ℕ)+1))
  simp only [Nat.cast_add] at hc hlog hm
  nlinarith only [hm,hc,hlog,hlen,hN]

/-- Accurate suffix costs are derived uniformly over actual prime batches.
There is no entropy estimate among its premises. -/
theorem eventually_accurate_suffix_cost (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) {D a c B : ℝ}
    (hD : 1≤D) (ha : 0<a) (hc : 0<c) (hca : c<a/2) (_hB : 0<B) :
    ∀ᶠ m : ℕ in atTop, ∀ (S : Finset ℕ) (ns : List ℕ) (N : ℕ),
      0<FreshEntropy.batchMeanLog S →
      FreshEntropy.batchMeanLog S≤2*((B+1)*Real.exp m) →
      (∀n∈ns,(n:ℝ)≤Real.exp (Real.exp (c*Real.exp m))) →
      (N:ℝ)≤Real.exp (Real.exp (c*Real.exp m)) →
      (ns.length+2:ℝ)≤Real.exp (Real.exp (c*Real.exp m)) →
      Real.log (wordStepBall b e (D*(ns.sum+N))).card≤
        10*accurateGrid m*
          (bandSize (FreshEntropy.batchMeanLog S) (accurateGrid m)
            (Real.exp (a*Real.exp m)) (accurateIterations m):ℝ)*FreshEntropy.batchMeanLog S := by
  have ht : Tendsto (fun m : ℕ => Real.exp (m:ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  have hfixed := eventually_const_le_exp_mul hc
    (Real.log (displacementPackingConstant b e)+2*Real.log D+2*Real.log 2)
  filter_upwards [eventually_accurate_scale ha 1,
    ht.eventually (eventually_mul_exp_le_exp hca 2),hfixed,
    eventually_mul_le_double_exp (a := a/2) (by positivity) (4*(B+1))]
    with m hscale hgap hfixed hmeanbound
  intro S ns N hmean hmeanup hops hN hlen
  let H := Real.exp (c*Real.exp m)
  let V := bandScale (accurateGrid m) (Real.exp (a*Real.exp m)) (accurateIterations m)
  have he : 1≤Real.exp H := Real.one_le_exp_iff.mpr (Real.exp_nonneg _)
  have hN' : (N:ℝ)+1≤2*Real.exp H := by dsimp only [H]; linarith only [hN,he]
  have hNlog := Real.log_le_log (by positivity : (0:ℝ)<(N:ℝ)+1) hN'
  rw [Real.log_mul (by norm_num) (Real.exp_ne_zero _),Real.log_exp] at hNlog
  have hlenlog := Real.log_le_log (by positivity : (0:ℝ)<(ns.length:ℝ)+1)
    (by dsimp only [H]; linarith only [hlen] : (ns.length:ℝ)+1≤Real.exp H)
  rw [Real.log_exp] at hlenlog
  have hcost := actual_schedule_cost_le b e hD (Real.exp_nonneg _) ns N hops hlenlog
    (by linarith only [hNlog])
  have hC : Real.log (displacementPackingConstant b e)+2*Real.log D+2*Real.log 2≤4*H := by
    have hh := Real.add_one_le_exp (c*Real.exp (m:ℝ))
    dsimp only [H]
    linarith only [hh,hfixed,Real.exp_nonneg (c*Real.exp (m:ℝ))]
  have h2 : 2*H≤accurateGrid m*V := by
    dsimp only [H,V]
    simpa only [pow_one] using hgap.trans hscale
  have hVL : 2*FreshEntropy.batchMeanLog S≤V := by
    have hsc0 : Real.exp ((a/2)*Real.exp m)≤accurateGrid m*V := by
      simpa only [pow_one,V] using hscale
    have hsc : Real.exp ((a/2)*Real.exp m)≤V :=
      hsc0.trans
        (mul_le_of_le_one_left (bandScale_pos (accurateGrid_pos m) (Real.exp_pos _) _).le
          (accurateGrid_le_one m))
    nlinarith only [hmeanup,hmeanbound,hsc]
  have hmass := bandSize_mul_half hmean hVL
  change V/2≤_ at hmass
  have hg := accurateGrid_pos m
  nlinarith only [hcost,hC,h2,hmass,hg]

/-- The unsmoothed selected-top suffix has only two logarithmic terms. -/
theorem actual_schedule_zero_cost_le (b : Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) {D H : ℝ} (hD : 1≤D) (hH : 0≤H)
    (ns : List ℕ) (hops : ∀n∈ns,(n:ℝ)≤Real.exp H)
    (hlen : Real.log ((ns.length:ℝ)+1)≤H) :
    Real.log (wordStepBall b e (D*ns.sum)).card≤
      Real.log (displacementPackingConstant b e)+2*Real.log D+4*H := by
  have hD0 : 0<D := by linarith only [hD]
  have hrad : 1≤D*((ns.sum:ℝ)+1) :=
    one_le_mul_of_one_le_of_one_le hD
      (by linarith only [(Nat.cast_nonneg ns.sum : (0:ℝ)≤ns.sum)])
  have hc := (displacementPackingConstant_spec b e).2 _ hrad
  rw [Real.log_mul hD0.ne' (by positivity)] at hc
  have hlog := schedule_log_bound ns 0 hH hops
  simp only [Nat.cast_zero,zero_add,Real.log_one,add_zero] at hlog
  have hm := wordStepBall_log_card_mono b e
    (by positivity : 0≤D*ns.sum)
    (by nlinarith only [hD0] : D*ns.sum≤D*((ns.sum:ℝ)+1))
  nlinarith only [hm,hc,hlog,hlen]

end Entry002
