import Entry002.GenericDyadicDensity
import Entry002.FiniteProbability
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Generic numerical multiscale schedules

Exact generic numerical proof bodies from OpenAI family028 GaussianMoat,
commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, https://github.com/openai/math.
Apache-2.0; see ../../upstream-028/LICENSE. Only imports and namespace adapted;
selected spans and hashes are recorded in logs/generic-numerical-schedule-provenance.json.
No Gaussian geometry, sieve, coverage derivation, or engine assertion is imported.
The smoothing guard bounds a displayed scalar error; application to a lattice
still requires actual geometric translation estimates and actual batch data.
-/
set_option autoImplicit false
namespace Entry002
open Filter
open scoped BigOperators Classical Topology

/- Source: AccurateScales.lean lines 78--88, unchanged body. -/
theorem eventually_poly_le_exp (C : ℝ) {a : ℝ} (ha : 0<a) (d : ℕ) :
    ∀ᶠ y : ℝ in atTop, C*y^d≤a*Real.exp y := by
  by_cases hC : 0<C
  · have hh := (Real.isLittleO_pow_exp_atTop (n := d)).bound (div_pos ha hC)
    filter_upwards [hh,eventually_ge_atTop (0:ℝ)] with y hy hy0
    rw [Real.norm_of_nonneg (pow_nonneg hy0 _),Real.norm_of_nonneg (Real.exp_nonneg _)] at hy
    have hm := mul_le_mul_of_nonneg_left hy hC.le
    rwa [←mul_assoc,mul_div_cancel₀ _ hC.ne'] at hm
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with y hy
    exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hC) (pow_nonneg hy _)).trans
      (mul_nonneg ha.le (Real.exp_nonneg _))

/- Source: BatchParameters.lean lines 68--277, unchanged body. -/
lemma package_list_arithmetic {X T p L n : ℝ} (hX : 1600≤X)
    (hT : Real.exp X≤T) (hp0 : 0<p) (hp : p≤2*T)
    (hn : 256*T*Real.log (2*T)≤n*L) :
    Real.log (4*(p*Real.exp (-X/200))+p*Real.exp (-(n:ℝ)*(L*((1/4)/p)/2)/4))≤
      Real.log p-X/400 := by
  have hX0 : 0≤X := by linarith only [hX]
  have hT0 : 0<T := (Real.exp_pos X).trans_le hT
  have hlog : X≤Real.log T := by
    exact (Real.log_exp X).symm ▸ Real.log_le_log (Real.exp_pos X) hT
  have hlog2 : X≤Real.log (2*T) := hlog.trans (Real.log_le_log hT0 (by linarith only [hT0]))
  have hl8 : Real.log 8≤3 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    rw [show (8:ℝ)=2^3 by norm_num,Real.log_pow]
    norm_num at hh ⊢
    linarith only [hh]
  have hhalf : 4*Real.exp (-X/200)≤Real.exp (-X/400)/2 := by
    have he : -X/200≤-X/400-Real.log 8 := by linarith only [hX,hl8]
    have hh := Real.exp_le_exp.mpr he
    rw [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<8)] at hh
    linarith only [hh]
  have hlarge : 4*Real.log (2*T)≤n*L/(32*p) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hp' := mul_le_mul_of_nonneg_right hp (show 0≤128*Real.log (2*T) by linarith only [hlog2,hX0])
    nlinarith only [hn,hp']
  have hsmall : Real.exp (-n*(L*((1/4)/p)/2)/4)≤Real.exp (-X/400)/2 := by
    have hl2 : Real.log 2≤1 := by
      have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
      linarith only [hh]
    have he : -n*(L*((1/4)/p)/2)/4≤-X/400-Real.log 2 := by
      have heq : -n*(L*((1/4)/p)/2)/4= -(n*L/(32*p)) := by ring
      rw [heq]
      linarith only [hlarge,hlog2,hX,hl2]
    have hh := Real.exp_le_exp.mpr he
    rwa [Real.exp_sub,Real.exp_log (by norm_num : (0:ℝ)<2)] at hh
  have harg : 4*(p*Real.exp (-X/200))+p*Real.exp (-n*(L*((1/4)/p)/2)/4)≤
      p*Real.exp (-X/400) := by
    have h1 := mul_le_mul_of_nonneg_left hhalf hp0.le
    have h2 := mul_le_mul_of_nonneg_left hsmall hp0.le
    nlinarith only [h1,h2]
  have hh := Real.log_le_log (by positivity : 0<4*(p*Real.exp (-X/200))+p*Real.exp (-n*(L*((1/4)/p)/2)/4)) harg
  rw [Real.log_mul hp0.ne' (Real.exp_ne_zero _),Real.log_exp] at hh
  linarith only [hh]

lemma package_rate_arithmetic {X T L n b H E c mean : ℝ}
    (hX : 1≤X) (hT : 0<T) (hc : 0<c)
    (hlog : X≤Real.log T) (hlog' : Real.log T≤21/20*X)
    (hmean : mean≤2*X) (hb : c*T/Real.log T≤b)
    (hn : n*L≤1024*T*Real.log T)
    (hshift : 2*n*H≤c*T/5000) (hE : E≤c*T/10000) :
    n*(L*(c/(10000000*Real.log T))+2*H)≤
      b*((X/400)*(1-2*(1/100))-(1/10000)*mean)-E := by
  have hlog0 : 0<Real.log T := by linarith only [hX,hlog]
  have hb0 : 0<b := (div_pos (mul_pos hc hT) hlog0).trans_le hb
  have hbg : c*T≤b*Real.log T := (div_le_iff₀ hlog0).mp hb
  have hbg' : c*T≤b*(21/20*X) := hbg.trans (mul_le_mul_of_nonneg_left hlog' hb0.le)
  have hgain : X/500≤(X/400)*(1-2*(1/100))-(1/10000)*mean := by
    nlinarith only [hmean,hX]
  have hrev := mul_le_mul_of_nonneg_left hgain hb0.le
  have hcost := mul_le_mul_of_nonneg_right hn (show 0≤c/(10000000*Real.log T) by positivity)
  have heq : (1024*T*Real.log T)*(c/(10000000*Real.log T))=1024*c*T/10000000 := by
    field_simp
  rw [heq] at hcost
  nlinarith only [hbg',hrev,hcost,hshift,hE,mul_pos hc hT]

open scoped BigOperators Classical
open Filter

lemma eventually_poly_le_exp_linear (C : ℝ) {a : ℝ} (ha : 0<a) (d : ℕ) :
    ∀ᶠ X : ℝ in atTop, C*X^d≤Real.exp (a*X) := by
  have h := eventually_poly_le_exp (C/a^d) (a := 1) (by norm_num) d
  have ht : Tendsto (fun x : ℝ => a*x) atTop atTop := tendsto_id.const_mul_atTop ha
  filter_upwards [ht.eventually h] with X hX
  simp only [one_mul,mul_pow] at hX
  convert hX using 1; field_simp

lemma eventually_mul_exp_le_exp {a b : ℝ} (hab : a<b) (C : ℝ) :
    ∀ᶠ X : ℝ in atTop, C*Real.exp (a*X)≤Real.exp (b*X) := by
  have h := eventually_poly_le_exp_linear C (sub_pos.mpr hab) 0
  filter_upwards [h] with X hX
  simp only [pow_zero,mul_one] at hX
  have hh := mul_le_mul_of_nonneg_right hX (Real.exp_nonneg (a*X))
  rw [←Real.exp_add] at hh
  convert hh using 1
  congr 1
  ring_nf

noncomputable def batchWordLength (j : ℕ) : ℕ := 2^(2*j/5)
noncomputable def packageRepetitions (j : ℕ) : ℕ :=
  ⌈256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)/batchWordLength j⌉₊

lemma batchWordLength_pos (j : ℕ) : 0<batchWordLength j := by
  unfold batchWordLength; positivity

lemma batchWordLength_dvd {i j : ℕ} (hij : i≤j) : batchWordLength i∣batchWordLength j := by
  exact pow_dvd_pow 2 (Nat.div_le_div_right (Nat.mul_le_mul_left 2 hij))

lemma batchWordLength_log (j : ℕ) :
    (2/5:ℝ)*(j*Real.log 2)-Real.log 2≤Real.log (batchWordLength j:ℝ) ∧
    Real.log (batchWordLength j:ℝ)≤(2/5:ℝ)*(j*Real.log 2) := by
  have hp : 0<Real.log (2:ℝ) := Real.log_pos (by norm_num)
  have h1 : 5*(2*j/5)≤2*j := Nat.mul_div_le _ _
  have h2 : 2*j<5*(2*j/5+1) := Nat.lt_mul_div_succ _ (by norm_num)
  have h1' : 5*(2*j/5:ℕ)≤(2:ℝ)*j := by exact_mod_cast h1
  have h2' : (2:ℝ)*j<5*((2*j/5:ℕ)+1) := by exact_mod_cast h2
  have hh1 := mul_le_mul_of_nonneg_right h1' hp.le
  have hh2 := mul_lt_mul_of_pos_right h2' hp
  simp only [batchWordLength,Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  constructor <;> nlinarith only [hh1,hh2]

lemma batchWordLength_le_scale (j : ℕ) : (batchWordLength j:ℝ)≤(2:ℝ)^j := by
  unfold batchWordLength
  push_cast
  apply pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2)
  omega

theorem eventually_integer_batch_bounds {D : ℝ} (hD : 1≤D) :
    ∀ᶠ X : ℝ in atTop, ∀ j : ℕ,
      X≤j*Real.log 2 → j*Real.log 2≤21/20*X →
      0<packageRepetitions j ∧
      (D*(batchWordLength j:ℝ))^2<(2:ℝ)^j ∧
      256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)≤
        (packageRepetitions j:ℝ)*batchWordLength j ∧
      (packageRepetitions j:ℝ)*batchWordLength j≤1024*(2:ℝ)^j*Real.log ((2:ℝ)^j) ∧
      (packageRepetitions j:ℝ)≤Real.exp (7/10*X) ∧
      (batchWordLength j:ℝ)≤Real.exp (21/50*X) := by
  have hpoly := eventually_poly_le_exp_linear (1024:ℝ) (a := 1/100) (by norm_num) 1
  have hshort' := eventually_mul_exp_le_exp (a := 0) (b := 4/25) (by norm_num) (2*D^2)
  filter_upwards [hpoly,hshort',eventually_ge_atTop (100:ℝ)] with X hpoly hshort' hX
  intro j hlo hhi
  have hl2 : Real.log (2:ℝ)≤1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [hh]
  have hT : Real.log ((2:ℝ)^j)=(j:ℝ)*Real.log 2 := Real.log_pow _ _
  have hTpos : 0<(2:ℝ)^j := by positivity
  have hLpos : 0<(batchWordLength j:ℝ) := by exact_mod_cast batchWordLength_pos j
  have hLlog := batchWordLength_log j
  have hLlo : Real.exp (39/100*X)≤(batchWordLength j:ℝ) := by
    rw [←Real.exp_log hLpos]
    apply Real.exp_le_exp.mpr
    nlinarith only [hLlog.1,hlo,hl2,hX]
  have hLhi : (batchWordLength j:ℝ)≤Real.exp (21/50*X) := by
    rw [←Real.exp_log hLpos]
    apply Real.exp_le_exp.mpr
    nlinarith only [hLlog.2,hhi]
  have hThe : (2:ℝ)^j≤Real.exp (21/20*X) := by
    rw [←Real.exp_log hTpos,hT]
    exact Real.exp_le_exp.mpr hhi
  have hTel : Real.exp X≤(2:ℝ)^j := by
    rw [←Real.exp_log hTpos,hT]
    exact Real.exp_le_exp.mpr hlo
  have hlogT : 1≤Real.log ((2:ℝ)^j) := by rw [hT]; linarith only [hlo,hX]
  have hlog2T : Real.log (2*(2:ℝ)^j)=Real.log 2+Real.log ((2:ℝ)^j) :=
    Real.log_mul (by norm_num) hTpos.ne'
  have hnum : 0<256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j) := by
    rw [hlog2T]; positivity
  have hnlo : 256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)≤
      (packageRepetitions j:ℝ)*batchWordLength j := by
    exact (div_le_iff₀ hLpos).mp (Nat.le_ceil _)
  have hnhi : (packageRepetitions j:ℝ)*batchWordLength j≤
      256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)+(batchWordLength j:ℝ) := by
    have hh := (Nat.ceil_lt_add_one (show 0≤256*(2:ℝ)^j*Real.log (2*(2:ℝ)^j)/batchWordLength j by positivity)).le
    have hm := mul_le_mul_of_nonneg_right hh hLpos.le
    rw [add_mul,one_mul,div_mul_cancel₀ _ hLpos.ne'] at hm
    exact hm
  have hprod : (packageRepetitions j:ℝ)*batchWordLength j≤1024*(2:ℝ)^j*Real.log ((2:ℝ)^j) := by
    have hL := batchWordLength_le_scale j
    rw [hlog2T] at hnhi
    have hh := mul_le_mul_of_nonneg_left hl2 (show 0≤256*(2:ℝ)^j by positivity)
    have hh' := mul_le_mul_of_nonneg_left hlogT (show 0≤(2:ℝ)^j by positivity)
    nlinarith only [hnhi,hL,hh,hh',hTpos]
  have hnbound : (packageRepetitions j:ℝ)≤Real.exp (7/10*X) := by
    have hrough : (packageRepetitions j:ℝ)*(batchWordLength j:ℝ)≤
        1024*Real.exp (21/20*X)*(21/20*X) := by
      apply hprod.trans
      gcongr
      rw [hT]; exact hhi
    have hn' := mul_le_mul_of_nonneg_left hLlo (Nat.cast_nonneg (packageRepetitions j))
    have hc : 1024*(21/20*X)≤Real.exp (4/100*X) := by
      have he := Real.add_one_le_exp (3/100*X)
      have he' : (21/20:ℝ)≤Real.exp (3/100*X) := by linarith only [he,hX]
      have hm := mul_le_mul hpoly he' (by norm_num) (Real.exp_nonneg _)
      simp only [pow_one] at hm
      rw [←Real.exp_add] at hm
      rw [show 1/100*X+3/100*X=4/100*X by ring] at hm
      linarith only [hm]
    have hh := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg (21/20*X))
    rw [←Real.exp_add] at hh
    have hlast : (packageRepetitions j:ℝ)*Real.exp (39/100*X)≤
        Real.exp (7/10*X)*Real.exp (39/100*X) := by
      apply hn'.trans (hrough.trans _)
      rw [←Real.exp_add]
      rw [show 4/100*X+21/20*X=7/10*X+39/100*X by ring] at hh
      nlinarith only [hh]
    nlinarith only [hlast,Real.exp_pos (39/100*X)]
  refine ⟨?_,?_,hnlo,hprod,hnbound,hLhi⟩
  · exact Nat.ceil_pos.mpr (div_pos hnum hLpos)
  · have hsquare := mul_le_mul hLhi hLhi hLpos.le (Real.exp_nonneg _)
    rw [←Real.exp_add] at hsquare
    have hh := mul_le_mul_of_nonneg_left hsquare (sq_nonneg D)
    have hstrict : D^2<Real.exp (4/25*X) := by
      simp only [zero_mul,Real.exp_zero,mul_one] at hshort'
      have hDpos : 0<D^2 := sq_pos_of_pos (by linarith only [hD])
      linarith only [hshort',hDpos]
    have hs := mul_lt_mul_of_pos_right hstrict (Real.exp_pos (21/50*X+21/50*X))
    rw [←Real.exp_add] at hs
    have he : 4/25*X+(21/50*X+21/50*X)=X := by ring
    rw [he] at hs
    have hsq : (D*(batchWordLength j:ℝ))^2≤D^2*Real.exp (21/50*X+21/50*X) := by
      nlinarith only [hh]
    exact (hsq.trans_lt hs).trans_le hTel

/- Source: BatchCertificate.lean lines 247--267, unchanged body. -/
theorem schedule_log_bound (ns : List ℕ) (N : ℕ) {H : ℝ} (hH : 0≤H)
    (hns : ∀ n∈ns, (n:ℝ)≤Real.exp H) :
    Real.log ((ns.sum+N:ℕ)+1)≤Real.log ((ns.length:ℝ)+1)+H+Real.log ((N:ℝ)+1) := by
  have hs : (ns.sum:ℝ)≤(ns.length:ℝ)*Real.exp H := by
    induction ns with
    | nil => simp
    | cons n ns ih =>
      have hn := hns n (List.mem_cons_self ..)
      have hi := ih (fun m hm => hns m (List.mem_cons_of_mem n hm))
      simp only [List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
      nlinarith only [hn,hi]
  have he : 1≤Real.exp H := Real.one_le_exp_iff.mpr hH
  have hc : 0≤(ns.length:ℝ)*Real.exp H := mul_nonneg (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hN : 1≤(N:ℝ)+1 := by linarith only [(Nat.cast_nonneg N : (0:ℝ)≤N)]
  have hle : ((ns.sum+N:ℕ)+1:ℝ)≤((ns.length:ℝ)+1)*Real.exp H*((N:ℝ)+1) := by
    simp only [Nat.cast_add]
    nlinarith only [hs,he,hc,hN,(Nat.cast_nonneg N : (0:ℝ)≤N)]
  have hh := Real.log_le_log (show (0:ℝ)<((ns.sum+N:ℕ)+1) by positivity) hle
  rw [Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (Real.exp_ne_zero _),
    Real.log_exp] at hh
  exact hh

/- Source: Smoothing.lean lines 9--16, unchanged body. -/
lemma window_power_step {i w : ℕ} (hi : i<w) :
    (100:ℝ)^i≤(100:ℝ)^w/100 := by
  have hh : (100:ℝ)^(i+1)≤(100:ℝ)^w := pow_le_pow_right₀ (by norm_num) hi
  rw [pow_succ] at hh
  linarith only [hh]

lemma window_power_nonneg (w : ℕ) : (0:ℝ)≤100^w := by positivity
lemma window_power_one (w : ℕ) : (1:ℝ)≤100^w := one_le_pow₀ (by norm_num)

/- Source: Smoothing.lean lines 86--225, unchanged body. -/
noncomputable def windowSmoothing (W m : ℕ) : ℕ :=
  ⌈Real.exp (20*(100:ℝ)^W*Real.exp m)⌉₊

lemma windowSmoothing_pos (W m : ℕ) : 0<windowSmoothing W m :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

lemma windowSmoothing_bounds (W m : ℕ) :
    Real.exp (20*(100:ℝ)^W*Real.exp m)≤(windowSmoothing W m:ℝ) ∧
    (windowSmoothing W m:ℝ)+1≤Real.exp ((20*(100:ℝ)^W+2)*Real.exp m) := by
  refine ⟨Nat.le_ceil _,?_⟩
  have hh := (Nat.ceil_lt_add_one (Real.exp_nonneg (20*(100:ℝ)^W*Real.exp m))).le
  have he : 1≤Real.exp (m:ℝ) := Real.one_le_exp_iff.mpr (Nat.cast_nonneg _)
  have he' : 3≤Real.exp (2*Real.exp (m:ℝ)) := by
    have hh := Real.add_one_le_exp (2*Real.exp (m:ℝ))
    linarith only [hh,he]
  have hbase : 1≤Real.exp (20*(100:ℝ)^W*Real.exp m) := Real.one_le_exp_iff.mpr (by positivity)
  have hmul := mul_le_mul_of_nonneg_left he' (Real.exp_nonneg (20*(100:ℝ)^W*Real.exp m))
  rw [←Real.exp_add] at hmul
  change (⌈Real.exp (20*(100:ℝ)^W*Real.exp m)⌉₊:ℝ)+1≤_
  rw [show (20*(100:ℝ)^W+2)*Real.exp m=20*(100:ℝ)^W*Real.exp m+2*Real.exp m by ring]
  linarith only [hh,hbase,hmul]

theorem eventually_suffix_cost {D a b C : ℝ} (hD : 0<D) (ha : 0<a) (hab : a<b) :
    ∀ᶠ X : ℝ in atTop, ∀ ns : List ℕ, ∀ N : ℕ,
      1≤ns.sum+N → (ns.length+2:ℝ)≤Real.exp X →
      (∀ n∈ns, (n:ℝ)≤Real.exp (Real.exp (a*X))) →
      (N:ℝ)+1≤Real.exp (C*X) →
      Real.log 36+2*Real.log (D*(ns.sum+N))≤Real.exp (b*X) := by
  have hp := eventually_poly_le_exp_linear
    (|Real.log 36|+2*|Real.log D|+2*|1+C|) ha 1
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
  have hc : Real.log 36+2*Real.log D+2*(1+C)*X≤Real.exp (a*X) := by
    simp only [pow_one] at hp
    have h1 := le_abs_self (Real.log (36:ℝ))
    have h2 := le_abs_self (Real.log D)
    have h3 := le_abs_self (1+C)
    nlinarith only [hp,hX,h1,h2,h3,abs_nonneg (Real.log (36:ℝ)),abs_nonneg (Real.log D)]
  nlinarith only [hlog,hl',hN',hs',hc,hres]

noncomputable def coverageRepetitions (X : ℝ) : ℕ := ⌈Real.exp (X/100)⌉₊

lemma coverageRepetitions_pos (X : ℝ) : 0<coverageRepetitions X :=
  Nat.ceil_pos.mpr (Real.exp_pos _)

lemma coverageRepetitions_bounds {X : ℝ} (hX : 0≤X) :
    Real.exp (X/100)≤(coverageRepetitions X:ℝ) ∧
    (coverageRepetitions X:ℝ)≤2*Real.exp (X/100) := by
  refine ⟨Nat.le_ceil _,?_⟩
  have hh := (Nat.ceil_lt_add_one (Real.exp_nonneg (X/100))).le
  have he : 1≤Real.exp (X/100) := Real.one_le_exp_iff.mpr (by positivity)
  change (⌈Real.exp (X/100)⌉₊:ℝ)≤2*Real.exp (X/100)
  linarith only [hh,he]

lemma eventually_coverage_hazard :
    ∀ᶠ X : ℝ in atTop, ∀ p : ℝ, 0<p → p≤2*Real.exp (21/20*X) →
      p*Real.exp (-(coverageRepetitions X:ℝ)*(1/64)^2*
        (p*Real.exp (-X/200))/(2*p))≤1/640000 := by
  have hp := eventually_poly_le_exp_linear (8192*(21/20+Real.log (1280000:ℝ)))
    (a := 1/200) (by norm_num) 1
  filter_upwards [hp,eventually_ge_atTop (1:ℝ)] with X hpoly hX
  intro p hp0 hp
  have hlog : 0≤Real.log (1280000:ℝ) := Real.log_nonneg (by norm_num)
  have hmargin : 8192*(21/20*X+Real.log (1280000:ℝ))≤Real.exp (X/200) := by
    simp only [pow_one,show (1:ℝ)/200*X=X/200 by ring] at hpoly
    nlinarith only [hpoly,hX,hlog]
  have hn := (coverageRepetitions_bounds (by linarith only [hX])).1
  have hn' := mul_le_mul_of_nonneg_right hn (Real.exp_nonneg (-X/200))
  rw [←Real.exp_add] at hn'
  have he : X/100+-X/200=X/200 := by ring
  rw [he] at hn'
  have harg : -(coverageRepetitions X:ℝ)*(1/64)^2*(p*Real.exp (-X/200))/(2*p)≤
      -(21/20*X)-Real.log (1280000:ℝ) := by
    have hEq : -(coverageRepetitions X:ℝ)*(1/64)^2*(p*Real.exp (-X/200))/(2*p)=
        -(coverageRepetitions X:ℝ)*Real.exp (-X/200)/8192 := by field_simp; ring
    rw [hEq]
    linarith only [hmargin,hn']
  have hh := mul_le_mul hp (Real.exp_le_exp.mpr harg) (Real.exp_nonneg _) (by positivity : 0≤2*Real.exp (21/20*X))
  simp only [mul_assoc,←Real.exp_add] at hh
  have he' : 21/20*X+(-(21/20*X)-Real.log (1280000:ℝ))=-Real.log (1280000:ℝ) := by ring
  rw [he',Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<1280000)] at hh
  norm_num at hh ⊢
  simpa only [mul_assoc] using hh

lemma eventually_coverage_data_cost :
    ∀ᶠ X : ℝ in atTop, ∀ H b : ℝ,
      H≤Real.exp (3/50*X) → Real.exp (X/8)/(4*X)≤b →
      (coverageRepetitions X:ℝ)*H/b≤1/1024 := by
  have hp := eventually_poly_le_exp_linear (8192:ℝ) (a := 11/200) (by norm_num) 1
  filter_upwards [hp,eventually_ge_atTop (1:ℝ)] with X hpoly hX
  intro H b hH hb
  have hXp : 0<X := by linarith only [hX]
  have hbp : 0<b := (div_pos (Real.exp_pos _) (by positivity)).trans_le hb
  have hn := (coverageRepetitions_bounds hXp.le).2
  have hmul := (mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg (coverageRepetitions X))).trans
    (mul_le_mul_of_nonneg_right hn (Real.exp_nonneg (3/50*X)))
  simp only [mul_assoc,←Real.exp_add] at hmul
  have hEq : X/100+3/50*X=7/100*X := by ring
  rw [hEq] at hmul
  have hb' := (div_le_iff₀ (show 0<4*X by positivity)).mp hb
  simp only [pow_one] at hpoly
  have hh := mul_le_mul_of_nonneg_right hpoly (Real.exp_nonneg (7/100*X))
  rw [←Real.exp_add] at hh
  have he : 11/200*X+7/100*X=X/8 := by ring
  rw [he] at hh
  have hnH : (coverageRepetitions X:ℝ)*H*(4096*X)≤b*(4*X) := by
    have hh' := mul_le_mul_of_nonneg_right hmul (show 0≤4096*X by positivity)
    nlinarith only [hh',hh,hb']
  apply (div_le_iff₀ hbp).mpr
  nlinarith only [hnH,hXp]

lemma eventually_package_displacement {c : ℝ} (hc : 0<c) :
    ∀ᶠ X : ℝ in atTop, ∀ n H T : ℝ,
      0≤n → n≤Real.exp (7/10*X) → H≤Real.exp (13/50*X) → Real.exp X≤T →
      2*n*H≤c*T/5000 := by
  have hh := eventually_mul_exp_le_exp (a := 24/25) (b := 1) (by norm_num) (10000/c)
  filter_upwards [hh] with X hX
  intro n H T hn0 hn hH hT
  have hmul := (mul_le_mul_of_nonneg_left hH hn0).trans
    (mul_le_mul_of_nonneg_right hn (Real.exp_nonneg (13/50*X)))
  rw [←Real.exp_add] at hmul
  have he : 7/10*X+13/50*X=24/25*X := by ring
  rw [he] at hmul
  simp only [one_mul] at hX
  have hh' := mul_le_mul_of_nonneg_left (hX.trans hT) hc.le
  rw [←mul_assoc,mul_div_cancel₀ _ hc.ne'] at hh'
  nlinarith only [hmul,hh']

/- Source: Smoothing.lean lines 249--324, unchanged body. -/
lemma binEntropy_small_exp {t Y : ℝ} (ht : 0≤t) (hY : 1≤Y)
    (htY : t≤Real.exp (-Y)) :
    Real.binEntropy t≤(Y+1)*Real.exp (-Y) := by
  have heY : 2≤Real.exp Y := by linarith only [Real.add_one_le_exp Y,hY]
  have hu : Real.exp (-Y)≤(1/2:ℝ) := by
    rw [Real.exp_neg]
    exact inv_le_of_inv_le₀ (by norm_num) (by simpa using heY)
  have hm := Real.binEntropy_strictMonoOn.monotoneOn
    (show t∈Set.Icc 0 (2:ℝ)⁻¹ by norm_num; exact ⟨ht,htY.trans hu⟩)
    (show Real.exp (-Y)∈Set.Icc 0 (2:ℝ)⁻¹ by norm_num; exact ⟨(Real.exp_pos _).le,hu⟩) htY
  have hn := Real.negMulLog_le_one_sub_self (show 0≤1-Real.exp (-Y) by linarith only [hu])
  simp only [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,
    Real.negMulLog,Real.log_exp] at hm ⊢
  have hh : -(1-Real.exp (-Y))*Real.log (1-Real.exp (-Y))≤Real.exp (-Y) := by
    simpa only [Real.negMulLog,sub_sub_cancel] using hn
  nlinarith only [hm,hh]

lemma exp_ratio_bound {a N X A : ℝ} (ha : a≤Real.exp (A*X))
    (hN : Real.exp (10*A*X)≤N) :
    a/(N+1)≤Real.exp (-9*A*X) := by
  have hNp : 0<N+1 := by linarith only [hN,Real.exp_pos (10*A*X)]
  apply (div_le_iff₀ hNp).mpr
  have hh := mul_le_mul_of_nonneg_left hN (Real.exp_nonneg (-9*A*X))
  rw [←Real.exp_add] at hh
  rw [show -9*A*X+10*A*X=A*X by ring] at hh
  nlinarith only [ha,hh,Real.exp_nonneg (-9*A*X)]

theorem eventually_smoothing_guard {A H : ℝ} (hA : 1≤A) :
    ∀ᶠ X : ℝ in atTop, ∀ a L E N : ℝ,
      0≤a → a≤Real.exp (A*X) → 0≤L → L≤Real.exp (A*X) →
      E≤Real.exp (A*X) → Real.exp (10*A*X)≤N →
      2*Real.binEntropy (a/(N+1))+(a/(N+1))*(L*H+2*E)≤Real.exp (-X) := by
  have hpoly := eventually_poly_le_exp_linear (4*(9*A+1))
    (a := 9*A-1) (by linarith only [hA]) 1
  have hcost := eventually_poly_le_exp_linear (2*(max H 0+2))
    (a := 8*A-1) (by linarith only [hA]) 0
  filter_upwards [hpoly,hcost,eventually_ge_atTop (1:ℝ)] with X hpoly hcost hX
  intro a L E N ha0 ha hL0 hL hE hN
  have hNpos : 0<N+1 := by linarith only [hN,Real.exp_pos (10*A*X)]
  have ht0 : 0≤a/(N+1) := div_nonneg ha0 hNpos.le
  have ht := exp_ratio_bound ha hN
  have hAX : 1≤A*X := by nlinarith only [hA,hX]
  have hbin := binEntropy_small_exp ht0 (by nlinarith only [hAX] : 1≤9*A*X)
    (by simpa only [neg_mul] using ht)
  have hbin' : 2*Real.binEntropy (a/(N+1))≤Real.exp (-X)/2 := by
    simp only [pow_one] at hpoly
    have hc : 4*(9*A*X+1)≤Real.exp ((9*A-1)*X) := by nlinarith only [hpoly,hX]
    have hh := mul_le_mul_of_nonneg_right hc (Real.exp_nonneg (-(9*A*X)))
    rw [←Real.exp_add,show (9*A-1)*X+-(9*A*X)= -X by ring] at hh
    linarith only [hh,hbin]
  have hK : L*H+2*E≤(max H 0+2)*Real.exp (A*X) := by
    have hh := mul_le_mul_of_nonneg_left (le_max_left H 0) hL0
    have hh' := mul_le_mul_of_nonneg_right hL (le_max_right H 0)
    nlinarith only [hh,hh',hE]
  have hKt := (mul_le_mul_of_nonneg_left hK ht0).trans
    (mul_le_mul_of_nonneg_right ht (show 0≤(max H 0+2)*Real.exp (A*X) by positivity))
  have hprod : Real.exp (-9*A*X)*((max H 0+2)*Real.exp (A*X))=
      (max H 0+2)*Real.exp (-8*A*X) := by
    rw [mul_left_comm,←Real.exp_add]
    congr 1
    ring_nf
  rw [hprod] at hKt
  have hlast : (max H 0+2)*Real.exp (-8*A*X)≤Real.exp (-X)/2 := by
    simp only [pow_zero,mul_one] at hcost
    have hh := mul_le_mul_of_nonneg_right hcost (Real.exp_nonneg (-8*A*X))
    rw [←Real.exp_add,show (8*A-1)*X+-8*A*X= -X by ring] at hh
    linarith only [hh]
  linarith only [hbin',hKt,hlast]

lemma eventually_smoothing_total (C : ℝ) :
    ∀ᶠ X : ℝ in atTop, C*X*Real.exp (-X)≤1 := by
  have hh := eventually_poly_le_exp C (a := 1) (by norm_num) 1
  filter_upwards [hh] with X hX
  simp only [pow_one,one_mul] at hX
  have hm := mul_le_mul_of_nonneg_right hX (Real.exp_nonneg (-X))
  simpa only [←Real.exp_add,add_neg_cancel,Real.exp_zero] using hm

/- Source: WindowParameters.lean lines 182--205, unchanged body. -/
theorem separated_power_sum (J : Finset ℕ) {K j : ℕ} (hK : 0<K)
    (hsep : ∀ a∈J, ∀ b∈J, a<b → a+K≤b)
    (hcap : ∀ a∈J, a+K≤j) :
    (∑ a∈J, (2:ℝ)^a)≤(2:ℝ)^j/((2:ℝ)^K-1) := by
  have hden : 0<(2:ℝ)^K-1 := by
    have hh := one_lt_pow₀ (by norm_num : (1:ℝ)<2) (by omega : K≠0)
    linarith only [hh]
  induction J using Finset.induction_on_max generalizing j with
  | empty => simp only [Finset.sum_empty]; positivity
  | @insert a J hmax ih =>
    have ha : a∉J := fun h => (lt_irrefl a) (hmax a h)
    have hci : ∀ b∈J, b+K≤a := by
      intro b hb
      exact hsep b (Finset.mem_insert_of_mem hb) a (Finset.mem_insert_self ..)
        (hmax b hb)
    have hi := ih (fun b hb c hc hbc => hsep b (Finset.mem_insert_of_mem hb)
      c (Finset.mem_insert_of_mem hc) hbc) hci
    rw [Finset.sum_insert ha]
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (hcap a (Finset.mem_insert_self ..))
    have hd := (div_le_div_iff_of_pos_right hden).mpr hp
    rw [pow_add] at hd
    have he : (2:ℝ)^a+(2:ℝ)^a/((2:ℝ)^K-1)=(2:ℝ)^a*2^K/(2^K-1) := by
      field_simp; ring
    exact (add_le_add (le_refl ((2:ℝ)^a)) hi).trans (he ▸ hd)

/- Source: WindowParameters.lean lines 239--258, unchanged body. -/
lemma log_two_lower : (1/2:ℝ)≤Real.log 2 := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
  norm_num at hh
  exact hh

lemma narrow_bins_card {X : ℝ} (hX : 2≤X) (J : Finset ℕ)
    (hJ : ∀ j∈J, (j:ℝ)*Real.log 2≤21/20*X) :
    (J.card:ℝ)≤3*X := by
  have hj : ∀ j∈J, (j:ℝ)≤21/10*X := by
    intro j hj
    have hh := mul_le_mul_of_nonneg_left log_two_lower (Nat.cast_nonneg j)
    linarith only [hh,hJ j hj]
  have hs : J⊆Finset.range (⌊21/10*X⌋₊+1) := by
    intro j hj'
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le ((Nat.le_floor_iff (by positivity)).mpr (hj j hj'))
  have hc : (J.card:ℝ)≤(⌊21/10*X⌋₊:ℝ)+1 := by
    exact_mod_cast (Finset.card_le_card hs).trans_eq (Finset.card_range _)
  have hf := Nat.floor_le (show 0≤21/10*X by linarith only [hX])
  linarith only [hc,hf,hX]

/- Source: SeparatedParameters.lean lines 10--45, unchanged body. -/
noncomputable def binEnum (J : Finset ℕ) (n : ℕ) : ℕ :=
  if h : n<J.card then J.orderEmbOfFin rfl ⟨n,h⟩ else 0

lemma binEnum_eq (J : Finset ℕ) {n : ℕ} (hn : n<J.card) :
    binEnum J n=J.orderEmbOfFin rfl ⟨n,hn⟩ := by simp only [binEnum,dite_eq_left hn]

lemma binEnum_mem (J : Finset ℕ) {n : ℕ} (hn : n<J.card) : binEnum J n∈J := by
  rw [binEnum_eq J hn]
  exact J.orderEmbOfFin_mem rfl _

lemma binEnum_strictMono (J : Finset ℕ) {n k : ℕ} (hnk : n<k) (hk : k<J.card) :
    binEnum J n<binEnum J k := by
  rw [binEnum_eq J (hnk.trans hk),binEnum_eq J hk]
  exact (J.orderEmbOfFin rfl).strictMono hnk

lemma binEnum_surj (J : Finset ℕ) {j : ℕ} (hj : j∈J) :
    ∃ n<J.card, binEnum J n=j := by
  have hh : j∈Set.range (J.orderEmbOfFin rfl) := by rw [J.range_orderEmbOfFin rfl]; exact hj
  obtain ⟨i,hi⟩ := hh
  exact ⟨i.val,i.isLt,(binEnum_eq J i.isLt).trans hi⟩

lemma binEnum_sum (J : Finset ℕ) (f : ℕ → ℝ) :
    (∑ n∈Finset.range J.card, f (binEnum J n))=∑ j∈J, f j := by
  apply Finset.sum_bij (fun n _ => binEnum J n)
  · intro n hn; exact binEnum_mem J (Finset.mem_range.mp hn)
  · intro n hn k hk he
    have hn' := Finset.mem_range.mp hn
    have hk' := Finset.mem_range.mp hk
    rcases lt_trichotomy n k with h|h|h
    · exact (ne_of_lt (binEnum_strictMono J h hk') he).elim
    · exact h
    · exact (ne_of_lt (binEnum_strictMono J h hn') he.symm).elim
  · intro j hj
    obtain ⟨n,hn,he⟩ := binEnum_surj J hj
    exact ⟨n,Finset.mem_range.mpr hn,he⟩
  · intro n hn; rfl

/- Source: SeparatedParameters.lean lines 83--176, unchanged body. -/
noncomputable def allBins (W : ℕ) (J : ℕ → Finset ℕ) : Finset ℕ :=
  (Finset.range W).biUnion J

lemma bin_window_gap {X : ℝ} {K u v i j : ℕ} (hX : 0<X)
    (hK : K*Real.log 2≤X) (huv : u<v)
    (hi : i*Real.log 2≤21/20*((100:ℝ)^u*X))
    (hj : (100:ℝ)^v*X≤j*Real.log 2) : i+K≤j := by
  have hp := mul_le_mul_of_nonneg_right (window_power_step huv) hX.le
  have ho := window_power_one u
  have hu : X≤(100:ℝ)^u*X := by nlinarith only [ho,hX]
  have hh : ((i+K:ℕ):ℝ)*Real.log 2≤(j:ℝ)*Real.log 2 := by
    push_cast
    nlinarith only [hp,hu,hK,hi,hj,hX]
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hn : (i+K:ℕ)≤(j:ℝ) := (mul_le_mul_iff_left₀ hl).mp hh
  exact_mod_cast hn

lemma allBins_separated {X : ℝ} {K W : ℕ} (J : ℕ → Finset ℕ) (hX : 0<X)
    (hK : K*Real.log 2≤X)
    (hb : ∀ w<W, ∀ j∈J w, (100:ℝ)^w*X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*((100:ℝ)^w*X))
    (hsep : ∀ w<W, ∀ i∈J w, ∀ j∈J w, i<j → i+K≤j) :
    ∀ i∈allBins W J, ∀ j∈allBins W J, i<j → i+K≤j := by
  intro i hi j hj hij
  obtain ⟨u,hu,hi⟩ := Finset.mem_biUnion.mp hi
  obtain ⟨v,hv,hj⟩ := Finset.mem_biUnion.mp hj
  have hu' := Finset.mem_range.mp hu
  have hv' := Finset.mem_range.mp hv
  rcases lt_trichotomy u v with huv|rfl|hvu
  · exact bin_window_gap hX hK huv (hb u hu' i hi).2 (hb v hv' j hj).1
  · exact hsep u hu' i hi j hj hij
  · have hh := bin_window_gap hX hK hvu (hb v hv' j hj).2 (hb u hu' i hi).1
    omega

lemma bins_disjoint {X : ℝ} {W : ℕ} (J : ℕ → Finset ℕ) (hX : 0<X)
    (hb : ∀ w<W, ∀ j∈J w, (100:ℝ)^w*X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*((100:ℝ)^w*X)) :
    (↑(Finset.range W) : Set ℕ).PairwiseDisjoint J := by
  intro u hu v hv hne
  apply Finset.disjoint_left.mpr
  intro j hju hjv
  have hp (i k : ℕ) (hik : i<k) (hji : j∈J i) (hjk : j∈J k) (hi : i<W) (hk : k<W) : False := by
    have hh := mul_le_mul_of_nonneg_right (window_power_step hik) hX.le
    have hlo := (hb k hk j hjk).1
    have hhi := (hb i hi j hji).2
    have hz : 0<(100:ℝ)^k*X := by positivity
    nlinarith only [hh,hlo,hhi,hz]
  rcases lt_or_gt_of_ne hne with h|h
  · exact hp u v h hju hjv (Finset.mem_range.mp hu) (Finset.mem_range.mp hv)
  · exact hp v u h hjv hju (Finset.mem_range.mp hv) (Finset.mem_range.mp hu)

lemma allBins_card_upper {m W : ℕ} (J : ℕ → Finset ℕ) (hm : 2≤Real.exp m)
    (hb : ∀ w<W, ∀ j∈J w, j*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) :
    ((allBins W J).card:ℝ)≤3*(W:ℝ)*(100:ℝ)^W*Real.exp m := by
  have hh := Finset.card_biUnion_le (s := Finset.range W) (t := J)
  have hs : (∑ w∈Finset.range W, ((J w).card:ℝ))≤(W:ℝ)*(3*(100:ℝ)^W*Real.exp m) := by
    calc
      _ ≤ ∑ w∈Finset.range W, 3*(100:ℝ)^W*Real.exp m := by
        apply Finset.sum_le_sum
        intro w hw
        have hw' := Finset.mem_range.mp hw
        have hp := window_power_one w
        have he : 2≤(100:ℝ)^w*Real.exp m := by nlinarith only [hp,hm]
        have hc := narrow_bins_card he (J w) (hb w hw')
        have hp' := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤100) hw'.le) (Real.exp_nonneg (m:ℝ))
        nlinarith only [hc,hp']
      _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hh' : ((allBins W J).card:ℝ)≤∑ w∈Finset.range W, ((J w).card:ℝ) := by exact_mod_cast hh
  nlinarith only [hh',hs]

lemma allBins_rate {X c t : ℝ} {W : ℕ} (J : ℕ → Finset ℕ) (hX : 0<X) (hc : 0<c)
    (hb : ∀ w<W, ∀ j∈J w, (100:ℝ)^w*X≤j*Real.log 2 ∧ j*Real.log 2≤21/20*((100:ℝ)^w*X))
    (hdense : ∀ w<W, t*((100:ℝ)^w*X)≤(J w).card) :
    (W:ℝ)*(c*t/10500000)≤∑ j∈allBins W J, c/(10000000*Real.log ((2:ℝ)^j)) := by
  rw [allBins,Finset.sum_biUnion (bins_disjoint J hX hb)]
  have hs : ∀ w<W, c*t/10500000≤∑ j∈J w, c/(10000000*Real.log ((2:ℝ)^j)) := by
    intro w hw
    have hwX : 0<(100:ℝ)^w*X := by positivity
    have hl : ∀ j∈J w, 0<Real.log ((2:ℝ)^j) := by
      intro j hj; rw [Real.log_pow]; exact hwX.trans_le (hb w hw j hj).1
    have ht' := hdense w hw
    have hh : (J w).card*(c/(10500000*((100:ℝ)^w*X)))≤∑ j∈J w, c/(10000000*Real.log ((2:ℝ)^j)) := by
      calc
        _ = ∑ _j∈J w, c/(10500000*((100:ℝ)^w*X)) := by simp only [Finset.sum_const,nsmul_eq_mul]
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro j hj
          apply div_le_div_of_nonneg_left hc.le (by have := hl j hj; positivity : 0<10000000*Real.log ((2:ℝ)^j))
          rw [Real.log_pow]
          nlinarith only [(hb w hw j hj).2]
    have hm := mul_le_mul_of_nonneg_right ht' (show 0≤c/(10500000*((100:ℝ)^w*X)) by positivity)
    have he : t*((100:ℝ)^w*X)*(c/(10500000*((100:ℝ)^w*X)))=c*t/10500000 := by field_simp
    rw [he] at hm
    exact hm.trans hh
  have hh := Finset.sum_le_sum (s := Finset.range W) (fun w hw => hs w (Finset.mem_range.mp hw))
  simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] using hh


/-- A single actual natural smoothing size handles any finite family of displayed
scalar errors, and can exceed any prescribed length bound. No geometric or
entropy-rate assertion is assumed here. -/
theorem exists_common_smoothing_size {ι : Type*} (I : Finset ι)
    (a len weight : ι → ℝ) (H : ℝ) (B : ℕ) {ε : ℝ} (hε : 0 < ε)
    (ha : ∀ i ∈ I, 0 ≤ a i) (hlen : ∀ i ∈ I, 0 ≤ len i) :
    ∃ N : ℕ, B ≤ N ∧ ∀ i ∈ I,
      2 * Real.binEntropy (a i / ((N : ℝ) + 1)) +
        (a i / ((N : ℝ) + 1)) * (len i * H + 2 * weight i) ≤ ε := by
  have hbounded : ∀ᶠ X : ℝ in atTop, ∀ i ∈ I,
      a i ≤ Real.exp X ∧ len i ≤ Real.exp X ∧ weight i ≤ Real.exp X := by
    apply I.eventually_all.mpr
    intro i _
    filter_upwards [eventually_ge_atTop (max (a i) (max (len i) (weight i)))] with X hX
    have he : X ≤ Real.exp X := by linarith only [Real.add_one_le_exp X]
    exact ⟨(le_max_left _ _).trans (hX.trans he),
      ((le_max_left _ _).trans (le_max_right _ _)).trans (hX.trans he),
      ((le_max_right _ _).trans (le_max_right _ _)).trans (hX.trans he)⟩
  have hguard := eventually_smoothing_guard (A := 1) (H := H) (by norm_num)
  have hexists : ∀ᶠ X : ℝ in atTop, ∃ N : ℕ, B ≤ N ∧ ∀ i ∈ I,
      2 * Real.binEntropy (a i / ((N : ℝ) + 1)) +
        (a i / ((N : ℝ) + 1)) * (len i * H + 2 * weight i) ≤ ε := by
    filter_upwards [hbounded, hguard, eventually_ge_atTop (B : ℝ),
      eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (-Real.log ε)]
      with X hb hg hB hX hεX
    let N : ℕ := ⌈Real.exp (10 * X)⌉₊
    have hN : Real.exp (10 * X) ≤ (N : ℝ) := Nat.le_ceil _
    have hBN : (B : ℝ) ≤ (N : ℝ) := by
      have he := Real.add_one_le_exp (10 * X)
      exact hB.trans (by linarith only [hN, he, hX])
    have heε : Real.exp (-X) ≤ ε := by
      calc
        _ ≤ Real.exp (Real.log ε) := Real.exp_le_exp.mpr (by linarith only [hεX])
        _ = ε := Real.exp_log hε
    refine ⟨N, by exact_mod_cast hBN, ?_⟩
    intro i hi
    have hh := hg (a i) (len i) (weight i) (N : ℝ) (ha i hi)
      (by simpa using (hb i hi).1) (hlen i hi)
      (by simpa using (hb i hi).2.1) (by simpa using (hb i hi).2.2)
      (by simpa using hN)
    exact hh.trans heε
  obtain ⟨X, hX⟩ := hexists.exists
  exact hX


/-- A single smoothing size simultaneously bounds every offset error appearing
in a finite block telescope. The block lengths and residue log weights are
actual supplied finite numbers, with no error certificate hypothesis. -/
theorem exists_common_block_smoothing_size (len : ℕ → ℕ) (n : ℕ)
    (weight : ℕ → ℝ) (H : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, (∀ j < n, len (j + 1) ≤ N) ∧ ∀ j < n, ∀ a < len (j + 1),
      2 * Real.binEntropy ((a : ℝ) / ((N : ℝ) + 1)) +
        ((a : ℝ) / ((N : ℝ) + 1)) * ((len j : ℝ) * H + 2 * weight (j + 1)) ≤ ε := by
  let I : Finset (Σ _ : ℕ, ℕ) := (Finset.range n).sigma (fun j => Finset.range (len (j + 1)))
  let B : ℕ := (Finset.range n).sup (fun j => len (j + 1))
  obtain ⟨N, hBN, herr⟩ := exists_common_smoothing_size I
    (fun i => (i.2 : ℝ)) (fun i => (len i.1 : ℝ))
    (fun i => weight (i.1 + 1)) H B hε
    (fun _ _ => Nat.cast_nonneg _) (fun _ _ => Nat.cast_nonneg _)
  refine ⟨N, ?_, ?_⟩
  · intro j hj
    exact (Finset.le_sup (f := fun j => len (j + 1)) (Finset.mem_range.mpr hj)).trans hBN
  · intro j hj a ha
    exact herr ⟨j, a⟩ (by simpa only [I, Finset.mem_sigma, Finset.mem_range] using And.intro hj ha)


/-- A5 supplies one walk-independent dense separated selection at every
multiscale window simultaneously; the base threshold is independent of the
number of windows. All batches are the actual finite prime sets. -/
theorem ArithmeticInterface.uniform_multiscale_dyadic_batches
    {L : Type*} [AddCommGroup L] {data : SignedResidueData L}
    {b : Module.Basis (Fin 2) ℤ L} {e : CoeffSpace ≃ₗ[ℝ] Plane}
    (A : ArithmeticInterface data b e) (K : ℕ) (hK : 0 < K) :
    ∃ c δ : ℝ, 0 < c ∧ 0 < δ ∧ ∀ᶠ m : ℕ in atTop,
      ∃ J : ℕ → Finset ℕ, ∀ w : ℕ,
        c * ((100 : ℝ)^w * Real.exp m) ≤ (J w).card ∧
        (∀ i ∈ J w, ∀ j ∈ J w, i < j → i + K ≤ j) ∧
        ∀ j ∈ J w,
          (100 : ℝ)^w * Real.exp m ≤ (j : ℝ) * Real.log 2 ∧
          (j : ℝ) * Real.log 2 ≤ 21/20 * ((100 : ℝ)^w * Real.exp m) ∧
          δ * (2 : ℝ)^j / Real.log ((2 : ℝ)^(j + 1)) ≤
            (dyadicPrimeBatch data.primes j).card := by
  obtain ⟨c, δ, hc, hδ, hselection⟩ := A.separated_dyadic_batches K hK
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp hselection
  have ht : Tendsto (fun m : ℕ => Real.exp (m : ℝ)) atTop atTop :=
    Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨c, δ, hc, hδ, ?_⟩
  filter_upwards [ht.eventually (eventually_ge_atTop X0)] with m hm
  have hsel (w : ℕ) := hX0 ((100 : ℝ)^w * Real.exp m)
    (hm.trans (by nlinarith only [window_power_one w, Real.exp_nonneg (m : ℝ)]))
  choose J hJ using hsel
  exact ⟨J, hJ⟩

end Entry002
