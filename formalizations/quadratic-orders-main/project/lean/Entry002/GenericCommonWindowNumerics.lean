import Entry002.GenericBandParameters

/-!
# Genuine common-window sampling and coverage budgets

Scalar estimates adapted or replayed from OpenAI family028 GaussianMoat,
commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0.
This module supplies proved numerical fields for the actual package and backward
coverage theorems. It does not assume an information gain or coverage result.
-/
set_option autoImplicit false
namespace Entry002
open Filter
open scoped BigOperators Classical Topology

/- Verbatim WindowBatch.lean lines 9--26. -/
lemma eventually_length_smoothing :
    ∀ᶠ X : ℝ in atTop, ∀ p L N : ℝ,
      0<p → p≤2*Real.exp (21/20*X) → 0≤L → L≤Real.exp (21/50*X) →
      Real.exp (20*X)≤N → L≤N ∧ L/(N+1)≤((1/4)/p)/2 := by
  have hh := eventually_mul_exp_le_exp (a := 147/100) (b := 20) (by norm_num) 16
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with X hh hX
  intro p L N hp hp' hL hL' hN
  have hNpos : 0<N+1 := by linarith only [hN,Real.exp_pos (20*X)]
  have hm := mul_le_mul hp' hL' hL (by positivity : 0≤2*Real.exp (21/20*X))
  rw [mul_assoc,←Real.exp_add,show 21/20*X+21/50*X=147/100*X by ring] at hm
  refine ⟨hL'.trans ((Real.exp_le_exp.mpr (by linarith only [hX])).trans hN),?_⟩
  apply (div_le_iff₀ hNpos).mpr
  have he : ((1/4:ℝ)/p)/2=(1/8)/p := by ring
  rw [he]
  apply (mul_le_mul_iff_left₀ hp).mp
  have heq : (1/8/p)*(N+1)*p=(N+1)/8 := by field_simp
  rw [heq]
  nlinarith only [hm,hh,hN]

/- Adapted CommonBlocks.lean lines 125--135: replace sieve mean by explicit μ. -/
lemma floor_size_lower {μ g U X : ℝ} {l : ℕ}
    (hX : 0<X) (hm : 0<μ) (hm' : μ≤2*X)
    (hscale : Real.exp (X/8)≤bandScale g U l) (hlarge : 4*X≤Real.exp (X/8)) :
    Real.exp (X/8)/(4*X)≤(bandSize μ g U l:ℝ) := by
  have hf := Nat.lt_floor_add_one (bandScale g U l/μ)
  have hh := mul_lt_mul_of_pos_right hf hm
  rw [div_mul_cancel₀ _ hm.ne',add_mul,one_mul] at hh
  have hb := mul_le_mul_of_nonneg_left hm' (Nat.cast_nonneg (bandSize μ g U l))
  change (bandScale g U l)<((bandSize μ g U l:ℝ)*μ)+μ at hh
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hf,hh,hb,hscale,hlarge,hm']

/-- The literal one-step numerical parameters discharge every fixed base and
backward coverage budget. The inputs are scalar entropy deficits and the actual
continuation-data cost; no coverage assertion is an input. -/
theorem one_step_coverage_scalar_guards {μ εK εR n H b p : ℝ}
    (hprime : Real.exp 100≤p)
    (hbase : εR*μ≤Real.exp (-100)/(512*640000))
    (hmid : εK*μ≤1/1024) (hcost : n*H/b≤1/1024) :
    0<Real.exp (-100)/512 ∧
    8*(Real.exp (-100)/512)*p=Real.exp (-100)*p/64 ∧
    εR*μ/(Real.exp (-100)/512)+1/640000≤(1/100)*(1/64)/2 ∧
    2*(1-Real.log ((1/100)*(1/64)/2))≤100 ∧
    εK*μ+n*H/b<(1/100)*(1/64)*100/4 ∧
    1≤Real.exp (-100)*p ∧
    100≤Real.log p-Real.log (Real.exp (-100)*p) ∧
    (Real.exp (-100)*p/64)/(1/64)=Real.exp (-100)*p := by
  have hp : 0<p := (Real.exp_pos 100).trans_le hprime
  have hc : 0<Real.exp (-100)/512 := by positivity
  have hsmall : εR*μ/(Real.exp (-100)/512)≤1/640000 := by
    apply (div_le_iff₀ hc).mpr
    convert hbase using 1; ring
  have hl2 : Real.log 2≤1 := by
    simpa only [show (2:ℝ)-1=1 by norm_num] using
      Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  have hl : Real.log (12800:ℝ)≤14 := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<12800)
      (by norm_num : (12800:ℝ)≤2^14)
    rw [Real.log_pow] at hh
    norm_num at hh
    linarith only [hh,hl2]
  have hscale : 2*(1-Real.log ((1/100)*(1/64)/2))≤100 := by
    norm_num only [mul_one,one_mul,div_div]
    rw [show (1:ℝ)/12800=(12800:ℝ)⁻¹ by rw [one_div],Real.log_inv]
    linarith only [hl]
  have hC := mul_le_mul_of_nonneg_left hprime (Real.exp_nonneg (-100))
  rw [←Real.exp_add] at hC
  norm_num at hC
  refine ⟨hc,by ring,by norm_num at hsmall ⊢; linarith only [hsmall],hscale,
    by norm_num; linarith only [hmid,hcost],hC,?_,by ring⟩
  rw [Real.log_mul (Real.exp_ne_zero _) hp.ne',Real.log_exp]
  linarith

/-- Actual lattice collision constants are absorbed into the same integer
sampling lengths. Every count and rate bound remains the proved literal one. -/
theorem eventually_collision_integer_batch_bounds {D γ : ℝ}
    (hD : 1≤D) (hγ : 0<γ) :
    ∀ᶠ X : ℝ in atTop, ∀ j : ℕ,
      X≤j*Real.log 2 → j*Real.log 2≤21/20*X →
      0<packageRepetitions j ∧
      (D*(batchWordLength j:ℝ))^2<γ^2*(2:ℝ)^j ∧
      256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)≤
        (packageRepetitions j:ℝ)*batchWordLength j ∧
      (packageRepetitions j:ℝ)*batchWordLength j≤1024*(2:ℝ)^j*Real.log ((2:ℝ)^j) ∧
      (packageRepetitions j:ℝ)≤Real.exp (7/10*X) ∧
      (batchWordLength j:ℝ)≤Real.exp (21/50*X) := by
  let D' := max 1 (D/γ)
  filter_upwards [eventually_integer_batch_bounds (D := D') (le_max_left _ _)] with X hX
  intro j hlo hhi
  obtain ⟨hn,hshort,hprod,hprod',hnmax,hLmax⟩ := hX j hlo hhi
  have hD' : D≤γ*D' := by
    have hh := (div_le_iff₀ hγ).mp (le_max_right 1 (D/γ))
    simpa only [mul_comm] using hh
  have hL : 0≤(batchWordLength j:ℝ) := Nat.cast_nonneg _
  have hDL := mul_le_mul_of_nonneg_right hD' hL
  have hsquare := pow_le_pow_left₀ (by nlinarith only [hD,hL]) hDL 2
  have hscaled := mul_lt_mul_of_pos_left hshort (sq_pos_of_pos hγ)
  have hh : (D*(batchWordLength j:ℝ))^2<γ^2*(2:ℝ)^j := by
    nlinarith only [hsquare,hscaled]
  exact ⟨hn,hh,hprod,hprod',hnmax,hLmax⟩

/-- One common threshold controls all middle/bottom entropy-deficit budgets in
any fixed finite number of windows. The supplied mean is its actual scalar value. -/
theorem eventually_common_window_errors (W : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ w<W, ∀ μ : ℝ, μ≤2*((100:ℝ)^w*Real.exp m) →
      (91*accurateGrid m)*μ≤Real.exp (-100)/(512*640000) ∧
      (91*accurateGrid m)*μ≤1/1024 := by
  have hε : 0<min (1/1024:ℝ) (Real.exp (-100)/(512*640000)) := by positivity
  filter_upwards [eventually_accurate_error (2*(100:ℝ)^W) hε] with m hm
  intro w hw μ hμ
  have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤100) hw.le
  have hμ' : μ≤(2*(100:ℝ)^W)*Real.exp m := by
    have hh := mul_le_mul_of_nonneg_right hpow (Real.exp_nonneg (m:ℝ))
    nlinarith only [hμ,hh]
  have hbudget := (mul_le_mul_of_nonneg_left hμ'
    (by have := accurateGrid_pos m; positivity : 0≤91*accurateGrid m)).trans hm
  exact ⟨hbudget.trans (min_le_right _ _),hbudget.trans (min_le_left _ _)⟩

/-- Floor rounding at the actual middle accurate scale leaves enough samples
for the derived continuation-data budget. -/
theorem eventually_common_middle_size (w : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ μ : ℝ, 0<μ → μ≤2*((100:ℝ)^w*Real.exp m) →
      Real.exp (((100:ℝ)^w*Real.exp m)/8)/(4*((100:ℝ)^w*Real.exp m))≤
        (bandSize μ (accurateGrid m) (Real.exp (((100:ℝ)^w/4)*Real.exp m))
          (accurateIterations m):ℝ) := by
  have hscale := eventually_accurate_scale (a := (100:ℝ)^w/4) (by positivity) 0
  have hlarge := eventually_mul_le_double_exp (a := (100:ℝ)^w/8) (by positivity) (4*(100:ℝ)^w)
  filter_upwards [hscale,hlarge] with m hscale hlarge
  intro μ hμ hμup
  apply floor_size_lower (by positivity) hμ hμup
  · simpa only [pow_zero,one_mul,div_div,show (4:ℝ)*2=8 by norm_num,div_mul_eq_mul_div] using hscale
  · simpa only [mul_assoc,div_mul_eq_mul_div] using hlarge

noncomputable def windowBatchRate (c : ℝ) (j : ℕ) : ℝ :=
  c/(10000000*Real.log ((2:ℝ)^j))

/-- Sampling and posterior-list arithmetic for the literal integer package
parameters, including the proved positive information rate margin. -/
theorem eventually_window_batch_arithmetic {D γ c : ℝ}
    (hD : 1≤D) (hγ : 0<γ) (hc : 0<c) :
    ∀ᶠ X : ℝ in atTop, ∀ j : ℕ,
      X≤j*Real.log 2 → j*Real.log 2≤21/20*X →
      0<packageRepetitions j ∧ 0<batchWordLength j ∧
      (D*(batchWordLength j:ℝ))^2<γ^2*(2:ℝ)^j ∧
      0<windowBatchRate c j ∧
      (∀ (N : ℕ), Real.exp (20*X)≤(N:ℝ) →
        batchWordLength j≤N ∧ ∀ p : ℝ, 0<p → p≤2*(2:ℝ)^j →
          (batchWordLength j:ℝ)/(N+1)≤((1/4)/p)/2 ∧
          Real.log (4*(p*Real.exp (-X/200))+p*Real.exp
            (-(packageRepetitions j:ℝ)*
              ((batchWordLength j:ℝ)*((1/4)/p)/2)/4))≤Real.log p-X/400) ∧
      (∀ b μ H E : ℝ, μ≤2*X →
        c*(2:ℝ)^j/Real.log ((2:ℝ)^j)≤b →
        H≤Real.exp (13/50*X) → E≤c*(2:ℝ)^j/10000 →
        (packageRepetitions j:ℝ)*((batchWordLength j:ℝ)*windowBatchRate c j+2*H)≤
          b*((X/400)*(1-2*(1/100))-(1/10000)*μ)-E) := by
  filter_upwards [eventually_collision_integer_batch_bounds hD hγ,
    eventually_package_displacement hc,eventually_length_smoothing,
    eventually_ge_atTop (1600:ℝ)] with X hint hdisp hsmooth hX
  intro j hlo hhi
  obtain ⟨hn,hshort,hprod,hprod',hnmax,hLmax⟩ := hint j hlo hhi
  have hTpos : (0:ℝ)<(2:ℝ)^j := by positivity
  have hT : Real.exp X≤(2:ℝ)^j := by
    rw [←Real.exp_log hTpos,Real.log_pow]
    exact Real.exp_le_exp.mpr hlo
  have hThi : (2:ℝ)^j≤Real.exp (21/20*X) := by
    rw [←Real.exp_log hTpos,Real.log_pow]
    exact Real.exp_le_exp.mpr hhi
  have hlogpos : 0<Real.log ((2:ℝ)^j) := by
    rw [Real.log_pow]
    linarith only [hlo,hX]
  refine ⟨hn,batchWordLength_pos j,hshort,by unfold windowBatchRate; positivity,?_,?_⟩
  · intro N hN
    have hlen := hsmooth ((2:ℝ)^j) (batchWordLength j) N hTpos
      (by linarith only [hThi,Real.exp_nonneg (21/20*X)]) (Nat.cast_nonneg _) hLmax hN
    refine ⟨by exact_mod_cast hlen.1,?_⟩
    intro p hp hphi
    refine ⟨(hsmooth p (batchWordLength j) N hp
      (hphi.trans (mul_le_mul_of_nonneg_left hThi (by norm_num)))
      (Nat.cast_nonneg _) hLmax hN).2,?_⟩
    exact package_list_arithmetic hX hT hp hphi hprod
  · intro b μ H E hμ hb hH hE
    exact package_rate_arithmetic (by linarith only [hX]) hTpos hc
      (by simpa only [Real.log_pow] using hlo)
      (by simpa only [Real.log_pow] using hhi) hμ hb hprod'
      (hdisp _ _ _ (Nat.cast_nonneg _) hnmax hH hT) hE

/-- A common smoothing size and a single threshold work for every batch in
all finitely many actual log windows. No walk or start enters the threshold. -/
theorem eventually_common_window_batch_arithmetic {D γ c : ℝ}
    (hD : 1≤D) (hγ : 0<γ) (hc : 0<c) (W : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ w<W, ∀ j : ℕ,
      (100:ℝ)^w*Real.exp m≤j*Real.log 2 →
      j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m) →
      let X := (100:ℝ)^w*Real.exp m
      0<packageRepetitions j ∧ 0<batchWordLength j ∧
      (D*(batchWordLength j:ℝ))^2<γ^2*(2:ℝ)^j ∧
      0<windowBatchRate c j ∧ batchWordLength j≤windowSmoothing W m ∧
      (∀ p : ℝ, 0<p → p≤2*(2:ℝ)^j →
        (batchWordLength j:ℝ)/(windowSmoothing W m+1)≤((1/4)/p)/2 ∧
        Real.log (4*(p*Real.exp (-X/200))+p*Real.exp
          (-(packageRepetitions j:ℝ)*
            ((batchWordLength j:ℝ)*((1/4)/p)/2)/4))≤Real.log p-X/400) ∧
      (∀ b μ H E : ℝ, μ≤2*X → c*(2:ℝ)^j/Real.log ((2:ℝ)^j)≤b →
        H≤Real.exp (13/50*X) → E≤c*(2:ℝ)^j/10000 →
        (packageRepetitions j:ℝ)*((batchWordLength j:ℝ)*windowBatchRate c j+2*H)≤
          b*((X/400)*(1-2*(1/100))-(1/10000)*μ)-E) := by
  have ht : Tendsto (fun m : ℕ => Real.exp (m:ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp (eventually_window_batch_arithmetic hD hγ hc)
  filter_upwards [ht.eventually (eventually_ge_atTop X₀)] with m hm
  intro w hw j hlo hhi
  let X : ℝ := (100:ℝ)^w*Real.exp m
  have hXm : Real.exp m≤X := by
    nlinarith only [window_power_one w,Real.exp_nonneg (m:ℝ)]
  obtain ⟨hn,hL,hshort,hr,hsmooth,hrate⟩ := hX₀ X (hm.trans hXm) j hlo hhi
  have hN : Real.exp (20*X)≤(windowSmoothing W m:ℝ) := by
    apply le_trans _ (windowSmoothing_bounds W m).1
    apply Real.exp_le_exp.mpr
    have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤100) hw.le) (Real.exp_nonneg (m:ℝ))
    dsimp only [X]
    nlinarith only [hp]
  exact ⟨hn,hL,hshort,hr,(hsmooth _ hN).1,(hsmooth _ hN).2,hrate⟩

/-- The numerical middle-size and actual continuation-ball upper bound imply
the small data cost required for the genuine backward amplification theorem. -/
theorem eventually_common_window_backward_arithmetic (W : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ w<W, ∀ μ H p : ℝ,
      0<μ → μ≤2*((100:ℝ)^w*Real.exp m) →
      H≤Real.exp (3/50*((100:ℝ)^w*Real.exp m)) →
      Real.exp ((100:ℝ)^w*Real.exp m)≤p →
      p≤2*Real.exp (21/20*((100:ℝ)^w*Real.exp m)) →
      let X := (100:ℝ)^w*Real.exp m
      let b := bandSize μ (accurateGrid m) (Real.exp (((100:ℝ)^w/4)*Real.exp m))
        (accurateIterations m)
      0<b ∧ (91*accurateGrid m)*μ≤Real.exp (-100)/(512*640000) ∧
      (91*accurateGrid m)*μ≤1/1024 ∧
      (coverageRepetitions X:ℝ)*H/b≤1/1024 ∧
      p*Real.exp (-(coverageRepetitions X:ℝ)*(1/64)^2*
        (p*Real.exp (-X/200))/(2*p))≤1/640000 := by
  have hsize := (Finset.range W).eventually_all.mpr
    (fun w _ => eventually_common_middle_size w)
  have ht : Tendsto (fun m : ℕ => Real.exp (m:ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp
    (eventually_coverage_data_cost.and eventually_coverage_hazard)
  filter_upwards [hsize,eventually_common_window_errors W,ht.eventually (eventually_ge_atTop X₀)]
    with m hsize herr hm
  intro w hw μ H p hμ hμup hH hp hpup
  let X : ℝ := (100:ℝ)^w*Real.exp m
  have hXpos : 0<X := by positivity
  have hXm : Real.exp m≤X := by
    nlinarith only [window_power_one w,Real.exp_nonneg (m:ℝ)]
  have hscalar := hX₀ X (hm.trans hXm)
  have hb := hsize w (Finset.mem_range.mpr hw) μ hμ hμup
  have hbpos : 0<bandSize μ (accurateGrid m) (Real.exp (((100:ℝ)^w/4)*Real.exp m))
      (accurateIterations m) := by
    exact_mod_cast (div_pos (Real.exp_pos _) (by positivity : 0<4*X)).trans_le hb
  exact ⟨hbpos,(herr w hw μ hμup).1,(herr w hw μ hμup).2,
    hscalar.1 _ _ hH hb,hscalar.2 _ ((Real.exp_pos X).trans_le hp) hpup⟩

lemma eventually_common_window_large (C : ℝ) :
    ∀ᶠ m : ℕ in atTop, ∀ w : ℕ, C≤(100:ℝ)^w*Real.exp m := by
  have ht : Tendsto (fun m : ℕ => Real.exp (m:ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [ht.eventually (eventually_ge_atTop C)] with m hm
  intro w
  exact hm.trans (by nlinarith only [window_power_one w,Real.exp_nonneg (m:ℝ)])

/-- A genuinely chosen finite separation gap makes every preceding-prime cost
small relative to the actual top-band batch size scale. -/
theorem exists_window_gap_parameters {δ : ℝ} (hδ : 0<δ) :
    ∃ a : ℝ, ∃ K : ℕ, 0<a ∧ a≤1 ∧ 2*a≤δ ∧ 0<K ∧
      a≤(2:ℝ)^K*topCoefficient a ∧
      4*Real.log 4/((2:ℝ)^K-1)≤(topCoefficient a/4)/10000 := by
  let a := min (δ/4) 1
  have ha : 0<a := lt_min (by positivity) (by norm_num)
  have ha1 : a≤1 := min_le_right _ _
  have haδ : 2*a≤δ := by
    have := min_le_left (δ/4) 1
    dsimp only [a]
    linarith only [this,hδ]
  have hv : 0<topCoefficient a := topCoefficient_pos ha
  have powtop := tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2)
  have hn := powtop.eventually (eventually_ge_atTop
    (max (a/topCoefficient a) (1+160000*Real.log 4/topCoefficient a)))
  obtain ⟨K,hK,hpow⟩ := (eventually_gt_atTop 0 |>.and hn).exists
  have hlo := (le_max_left _ _).trans hpow
  have hhi := (le_max_right _ _).trans hpow
  have hgap : a≤(2:ℝ)^K*topCoefficient a := (div_le_iff₀ hv).mp hlo
  have hden : 0<(2:ℝ)^K-1 := by
    have := one_lt_pow₀ (by norm_num : (1:ℝ)<2) (by omega : K≠0)
    linarith only [this]
  have hcost : 4*Real.log 4/((2:ℝ)^K-1)≤(topCoefficient a/4)/10000 := by
    have hh : 160000*Real.log 4≤((2:ℝ)^K-1)*topCoefficient a := by
      apply (div_le_iff₀ hv).mp
      linarith only [hhi]
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hh]
  exact ⟨a,K,ha,ha1,haδ,hK,hgap,hcost⟩

lemma bandSize_pos_of_relative {μ g U X : ℝ} {l : ℕ}
    (hμ : 0<μ) (hμup : μ≤2*X) (hg : 0≤g) (hg1 : g≤1)
    (hrelative : 1280*X≤g^5*bandScale g U l) :
    0<bandSize μ g U l := by
  have hX : 0<X := by linarith only [hμ,hμup]
  have hV : 0<bandScale g U l := by
    nlinarith only [hrelative,hX,pow_nonneg hg 5]
  have hpow : g^5≤1 := pow_le_one₀ hg hg1
  have hmul := mul_le_mul_of_nonneg_right hpow hV.le
  have hμV : μ≤bandScale g U l := by
    linarith only [hμup,hrelative,hmul,hX]
  exact Nat.floor_pos.mpr ((le_div_iff₀ hμ).mpr (by simpa only [one_mul] using hμV))

end Entry002
