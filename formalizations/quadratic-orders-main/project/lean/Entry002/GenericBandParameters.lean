import Entry002.GenericNumericalSchedule

/-!
# Pure numerical geometric-band and window scaffold

Generic proof bodies replayed from OpenAI family028 GaussianMoat, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (https://github.com/openai/math),
Apache-2.0; see ../../upstream-028/LICENSE. All selected scalar/list proof
bodies are verbatim, except `bandSize` takes a real mean `μ` instead of a
Gaussian sieve. No EntropyBand, enrichment-margin or engine assertion is
imported. The accompanying source map distinguishes verbatim and adapted code.
-/
set_option autoImplicit false
namespace Entry002
open Filter
open scoped BigOperators Classical Topology

/- Source: MultiscaleSchedule.lean lines 215--231. -/
lemma log_floor_exp {x : ℝ} (hx : 2 ≤ x) :
    1 ≤ ⌊Real.exp x⌋₊ ∧ x-1 ≤ Real.log (⌊Real.exp x⌋₊:ℝ) ∧
      Real.log (⌊Real.exp x⌋₊:ℝ) ≤ x := by
  have he : 2 ≤ Real.exp x := by linarith only [Real.add_one_le_exp x,hx]
  have hn : 1 ≤ ⌊Real.exp x⌋₊ := Nat.floor_pos.mpr (by linarith only [he])
  have hnp : (0:ℝ)<⌊Real.exp x⌋₊ := by exact_mod_cast hn
  have hlow : Real.exp x/2 ≤ (⌊Real.exp x⌋₊:ℝ) := by
    have h := Nat.lt_floor_add_one (Real.exp x)
    linarith only [he,h]
  have hlo := Real.log_le_log (div_pos (Real.exp_pos x) (by norm_num : (0:ℝ)<2)) hlow
  rw [Real.log_div (Real.exp_ne_zero x) (by norm_num : (2:ℝ)≠0),Real.log_exp] at hlo
  have hl2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
    linarith only [h]
  have hhi := Real.log_le_log hnp (Nat.floor_le (Real.exp_nonneg x))
  rw [Real.log_exp] at hhi
  exact ⟨hn,by linarith only [hlo,hl2],hhi⟩

/- Source: MultiscaleSchedule.lean lines 323--340. -/
noncomputable def bandScale (g U : ℝ) (j : ℕ) : ℝ := (g^2)^j*U
noncomputable def bandLength (g U : ℝ) (j : ℕ) : ℕ := ⌊Real.exp (g*bandScale g U j)⌋₊
noncomputable def bandSize (μ g U : ℝ) (j : ℕ) : ℕ := ⌊bandScale g U j/μ⌋₊

lemma bandScale_pos {g U : ℝ} (hg : 0<g) (hU : 0<U) (j : ℕ) :
    0<bandScale g U j := mul_pos (pow_pos (sq_pos_of_pos hg) _) hU

lemma bandScale_antitone {g U : ℝ} (hg : 0≤g) (hg1 : g≤1) (hU : 0≤U) :
    Antitone (bandScale g U) := by
  intro i j hij
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (sq_nonneg g) (pow_le_one₀ hg hg1) hij) hU

lemma bandScale_succ (g U : ℝ) (j : ℕ) :
    bandScale g U (j+1)=g^2*bandScale g U j := by
  unfold bandScale
  rw [pow_succ]
  ring

/- Source: SieveCertificate.lean lines 102--113. -/
lemma bandLength_le_exp_start {g U : ℝ} (hg : 0≤g) (hg1 : g≤1) (hU : 0≤U) (j : ℕ) :
    (bandLength g U j:ℝ)≤Real.exp (g*U) := by
  apply (Nat.floor_le (Real.exp_nonneg _)).trans
  apply Real.exp_le_exp.mpr
  have hh := bandScale_antitone hg hg1 hU (Nat.zero_le j)
  simpa only [bandScale,pow_zero,one_mul] using mul_le_mul_of_nonneg_left hh hg

lemma bandLength_le_exp_at {g U : ℝ} (hg : 0≤g) (hg1 : g≤1) (hU : 0≤U)
    {i j : ℕ} (hij : i≤j) :
    (bandLength g U j:ℝ)≤Real.exp (g*bandScale g U i) := by
  exact (Nat.floor_le (Real.exp_nonneg _)).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (bandScale_antitone hg hg1 hU hij) hg))

/- Source: BatchCertificate.lean lines 204--245. -/
lemma bandScale_add (g U : ℝ) (j k : ℕ) :
    bandScale g U (j+k)=bandScale g (bandScale g U j) k := by
  unfold bandScale
  rw [pow_add]
  ring

lemma bandLength_add (g U : ℝ) (j k : ℕ) :
    bandLength g U (j+k)=bandLength g (bandScale g U j) k := by
  unfold bandLength
  rw [bandScale_add]

lemma bandList_split (g U : ℝ) (j l r : ℕ) :
    List.ofFn (fun i : Fin (j+l+r) => bandLength g U i.val)=
      List.ofFn (fun i : Fin j => bandLength g U i.val)++
      List.ofFn (fun i : Fin l => bandLength g (bandScale g U j) i.val)++
      List.ofFn (fun i : Fin r => bandLength g (bandScale g U (j+l)) i.val) := by
  rw [List.ofFn_add,List.ofFn_add]
  simp only [Fin.val_castLE,Fin.val_natAdd,bandLength_add]

theorem band_first_crossing {g U V : ℝ} {m : ℕ} (hg : 0<g) (hg1 : g<1)
    (hV : 0<V) (hstart : V≤U) (hend : bandScale g U m≤V) :
    ∃ k, k ≤ m ∧ g^2*V<bandScale g U k ∧ bandScale g U k≤V := by
  have hex : ∃ k, bandScale g U k≤V := ⟨m,hend⟩
  let k := Nat.find hex
  have hk : bandScale g U k≤V := Nat.find_spec hex
  have hkm : k ≤ m := Nat.find_min' hex hend
  refine ⟨k,hkm,?_,hk⟩
  by_cases hk0 : k=0
  · simp only [hk0,bandScale,pow_zero,one_mul]
    have hg2 : g^2<1 := pow_lt_one₀ hg.le hg1 (by omega : 2≠0)
    exact (mul_lt_of_lt_one_left hV hg2).trans_le hstart
  · have hkpos : 0<k := Nat.pos_of_ne_zero hk0
    have hprev : V<bandScale g U (k-1) := lt_of_not_ge (Nat.find_min hex (by omega))
    have he : k=k-1+1 := by omega
    rw [he,bandScale_succ]
    exact mul_lt_mul_of_pos_left hprev (sq_pos_of_pos hg)

lemma bandScale_log {g U : ℝ} (hg : 0<g) (hU : 0<U) (k : ℕ) :
    Real.log (bandScale g U k)=(k:ℝ)*(2*Real.log g)+Real.log U := by
  unfold bandScale
  rw [Real.log_mul (ne_of_gt (pow_pos (sq_pos_of_pos hg) _)) hU.ne',Real.log_pow,Real.log_pow]
  norm_num

/- Source: AccurateScales.lean lines 90--165. -/
theorem eventually_linear_le_square (A B : ℝ) :
    ∀ᶠ y : ℝ in atTop, A*y+B≤y^2 := by
  filter_upwards [eventually_ge_atTop (max (|A|+|B|+1) 1)] with y hy
  have h1 : 1≤y := (le_max_right _ _).trans hy
  have h2 : |A|+|B|+1≤y := (le_max_left _ _).trans hy
  have h3 : A≤|A| := le_abs_self _
  have h4 : B≤|B| := le_abs_self _
  nlinarith only [h1,h2,h3,h4,abs_nonneg A,abs_nonneg B]

noncomputable def accurateGrid (m : ℕ) : ℝ := Real.exp (-((m:ℝ)^2))
def accurateIterations (m : ℕ) : ℕ := 4*m^2

lemma accurateGrid_pos (m : ℕ) : 0<accurateGrid m := Real.exp_pos _

lemma accurateGrid_le_one (m : ℕ) : accurateGrid m≤1 := by
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))

lemma accurateIterations_error (m : ℕ) :
    (1/2:ℝ)^(accurateIterations m)+90*accurateGrid m≤91*accurateGrid m := by
  have hl : (1/2:ℝ)≤Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
    norm_num at hh
    exact hh
  have he : (1/2:ℝ)^(accurateIterations m)≤accurateGrid m := by
    rw [show (1/2:ℝ)=Real.exp (-Real.log 2) by rw [Real.exp_neg,Real.exp_log (by norm_num)]; norm_num]
    rw [←Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    simp only [accurateIterations,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    nlinarith only [sq_nonneg (m:ℝ),hl]
  linarith only [he]

lemma accurateGrid_scale (m : ℕ) (a : ℝ) :
    bandScale (accurateGrid m) (Real.exp (a*Real.exp m)) (accurateIterations m)=
      Real.exp (a*Real.exp m-8*(m:ℝ)^4) := by
  unfold bandScale accurateGrid accurateIterations
  rw [←Real.exp_nat_mul,←Real.exp_nat_mul,←Real.exp_add]
  congr 1
  push_cast
  ring

theorem eventually_accurate_scale {a : ℝ} (ha : 0<a) (k : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      Real.exp ((a/2)*Real.exp m)≤(accurateGrid m)^k *
        bandScale (accurateGrid m) (Real.exp (a*Real.exp m)) (accurateIterations m) := by
  have h4 := eventually_poly_le_exp 8 (a := a/4) (by positivity) 4
  have h2 := eventually_poly_le_exp (k:ℝ) (a := a/4) (by positivity) 2
  have hh := (h4.and h2).filter_mono (show Filter.map ((↑) : ℕ → ℝ) atTop≤atTop from tendsto_natCast_atTop_atTop)
  change ∀ᶠ m : ℕ in atTop, _ at hh
  filter_upwards [hh] with m hm
  rw [accurateGrid_scale]
  unfold accurateGrid
  rw [←Real.exp_nat_mul,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith only [hm.1,hm.2]

theorem eventually_accurate_error (C : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ m : ℕ in atTop, 91*accurateGrid m*(C*Real.exp m)≤ε := by
  by_cases hC : 0<C
  · have hh := eventually_linear_le_square 1 (Real.log (91*C/ε))
    have hh' := hh.filter_mono (show Filter.map ((↑) : ℕ → ℝ) atTop≤atTop from tendsto_natCast_atTop_atTop)
    filter_upwards [hh'] with m hm
    change 1*(m:ℝ)+Real.log (91*C/ε)≤(m:ℝ)^2 at hm
    have he : Real.exp ((m:ℝ)-(m:ℝ)^2)≤ε/(91*C) := by
      rw [←Real.exp_log (show 0<ε/(91*C) by positivity)]
      apply Real.exp_le_exp.mpr
      rw [Real.log_div (by positivity) (by positivity)]
      rw [Real.log_div (by positivity) hε.ne'] at hm
      linarith only [hm]
    have hmul := (le_div_iff₀ (show 0<91*C by positivity)).mp he
    unfold accurateGrid
    rw [show 91*Real.exp (-((m:ℝ)^2))*(C*Real.exp m)=
      Real.exp ((m:ℝ)-(m:ℝ)^2)*(91*C) by rw [Real.exp_sub,Real.exp_neg]; ring]
    exact hmul
  · filter_upwards [] with m
    have : C*Real.exp (m:ℝ)≤0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hC) (Real.exp_nonneg _)
    exact (mul_nonpos_of_nonneg_of_nonpos (by exact mul_nonneg (by norm_num) (accurateGrid_pos m).le : 0≤91*accurateGrid m) this).trans hε.le

/- Source: AccurateScales.lean lines 173--196. -/
lemma eventually_const_le_exp_mul {a : ℝ} (ha : 0<a) (C : ℝ) :
    ∀ᶠ m : ℕ in atTop, C≤a*Real.exp m := by
  have hh : Tendsto (fun m : ℕ => Real.exp (m:ℝ)*a) atTop atTop :=
    (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop).atTop_mul_const ha
  simpa only [mul_comm] using hh.eventually (eventually_ge_atTop C)

lemma eventually_mul_le_double_exp {a : ℝ} (ha : 0<a) (C : ℝ) :
    ∀ᶠ m : ℕ in atTop, C*Real.exp m≤Real.exp (a*Real.exp m) := by
  have hh := eventually_poly_le_exp (C/a) (a := 1) (by norm_num) 1
  have ht : Tendsto (fun m : ℕ => a*Real.exp m) atTop atTop := by
    simpa only [Function.comp_apply] using Filter.Tendsto.const_mul_atTop ha
      (Real.tendsto_exp_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  filter_upwards [ht.eventually hh] with m hm
  simpa only [pow_one,one_mul,←mul_assoc,div_mul_cancel₀ _ ha.ne'] using hm

lemma eventually_accurate_small {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ m : ℕ in atTop, accurateGrid m≤ε := by
  have hh := eventually_linear_le_square 0 (-Real.log ε)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hh] with m hm
  change 0*(m:ℝ)-Real.log ε≤(m:ℝ)^2 at hm
  unfold accurateGrid
  rw [←Real.exp_log hε]
  apply Real.exp_le_exp.mpr
  linarith only [hm]

/- Source: WindowParameters.lean lines 13--22. -/
noncomputable def topParameter : ℝ := 1/1000000
def topIterations : ℕ := 20
noncomputable def topCoefficient (a : ℝ) : ℝ := (topParameter^2)^topIterations*a

lemma topParameter_pos : 0<topParameter := by norm_num [topParameter]
lemma topParameter_small : topParameter≤1/200 := by norm_num [topParameter]
lemma topCoefficient_pos {a : ℝ} (ha : 0<a) : 0<topCoefficient a := by
  unfold topCoefficient; exact mul_pos (pow_pos (sq_pos_of_pos topParameter_pos) _) ha
lemma top_deficit : (1/2:ℝ)^topIterations+90*topParameter≤1/10000 := by
  norm_num [topParameter,topIterations]

/- Source: WindowParameters.lean lines 88--180. -/
noncomputable def topBlock (a : ℝ) (j : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin topIterations => bandLength topParameter (a*(2:ℝ)^j) i.val)

noncomputable def topBlocks (a : ℝ) (J : Finset ℕ) : List ℕ :=
  (J.sort (·≥·)).flatMap (topBlock a)

noncomputable def accurateBlock (m : ℕ) (a : ℝ) : List ℕ :=
  List.ofFn (fun i : Fin (accurateIterations m) =>
    bandLength (accurateGrid m) (Real.exp (a*Real.exp m)) i.val)

lemma topBlocks_length (a : ℝ) (J : Finset ℕ) :
    (topBlocks a J).length=J.card*topIterations := by
  unfold topBlocks
  rw [List.length_flatMap]
  simp only [topBlock,List.length_ofFn,List.map_const',List.sum_replicate,Finset.length_sort,
    smul_eq_mul]

lemma topBlock_bound {a H : ℝ} (ha : 0≤a) (j : ℕ)
    (h : topParameter*a*(2:ℝ)^j≤H) :
    ∀ n∈topBlock a j, (n:ℝ)≤Real.exp H := by
  intro n hn
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn
  exact (bandLength_le_exp_start topParameter_pos.le
    (by norm_num [topParameter]) (mul_nonneg ha (by positivity)) i.val).trans
    (Real.exp_le_exp.mpr (by simpa only [mul_assoc] using h))

lemma accurateBlock_bound {a H : ℝ} {m : ℕ} (hg : accurateGrid m≤1)
    (h : accurateGrid m*Real.exp (a*Real.exp m)≤H) :
    ∀ n∈accurateBlock m a, (n:ℝ)≤Real.exp H := by
  intro n hn
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn
  exact (bandLength_le_exp_start (accurateGrid_pos m).le hg (Real.exp_nonneg _) i.val).trans
    (Real.exp_le_exp.mpr h)

lemma sorted_split {J : Finset ℕ} {j : ℕ} (hj : j∈J) :
    ∃ pre post : List ℕ, J.sort (·≥·)=pre++j::post ∧
      (∀ i∈post, i∈J ∧ i < j) ∧ (∀ i∈pre, i∈J ∧ j < i) := by
  have hm : j∈J.sort (·≥·) := (Finset.mem_sort (·≥·)).mpr hj
  obtain ⟨pre,post,he⟩ := List.mem_iff_append.mp hm
  have hp : (J.sort (·≥·)).Pairwise (·>·) := by
    exact (Finset.sortedGT_sort J).pairwise
  rw [he,List.pairwise_append,List.pairwise_cons] at hp
  refine ⟨pre,post,he,?_,?_⟩
  · intro i hi
    refine ⟨(Finset.mem_sort (·≥·)).mp ?_,hp.2.1.1 i hi⟩
    rw [he]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hi)
  · intro i hi
    refine ⟨(Finset.mem_sort (·≥·)).mp ?_,hp.2.2 i hi j (List.mem_cons_self ..)⟩
    rw [he]; exact List.mem_append_left _ hi

lemma topBlocks_split {a : ℝ} {J : Finset ℕ} {j : ℕ} (hj : j∈J) :
    ∃ pre post : List ℕ, topBlocks a J=pre++topBlock a j++post ∧
      post.length≤J.card*topIterations ∧
      (∀ n∈post, ∃ i∈J, i<j ∧ n∈topBlock a i) := by
  obtain ⟨A,B,he,hB,_⟩ := sorted_split hj
  refine ⟨A.flatMap (topBlock a),B.flatMap (topBlock a),?_,?_,?_⟩
  · simp only [topBlocks,he,List.flatMap_append,List.flatMap_cons,List.append_assoc]
  · have hh : (B.flatMap (topBlock a)).length≤(topBlocks a J).length := by
      simp only [topBlocks,he,List.flatMap_append,List.flatMap_cons,List.length_append]
      omega
    simpa only [topBlocks_length] using hh
  · intro n hn
    obtain ⟨i,hi,hn⟩ := List.mem_flatMap.mp hn
    exact ⟨i,(hB i hi).1,(hB i hi).2,hn⟩

noncomputable def windowBlocks (a : ℝ) (m : ℕ) (J : ℕ → Finset ℕ) (W : ℕ) : List ℕ :=
  ((List.range W).reverse).flatMap (fun w =>
    topBlocks a (J w)++accurateBlock m ((100:ℝ)^w/4))

lemma windowBlocks_succ (a : ℝ) (m : ℕ) (J : ℕ → Finset ℕ) (W : ℕ) :
    windowBlocks a m J (W+1)=topBlocks a (J W)++accurateBlock m ((100:ℝ)^W/4)++
      windowBlocks a m J W := by
  simp only [windowBlocks,List.range_succ,List.reverse_append,List.reverse_singleton,
    List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc]

lemma windowBlocks_split (a : ℝ) (m : ℕ) (J : ℕ → Finset ℕ) {W w : ℕ} (hw : w<W) :
    ∃ pre, windowBlocks a m J W=pre++topBlocks a (J w)++
      accurateBlock m ((100:ℝ)^w/4)++windowBlocks a m J w := by
  induction W with
  | zero => omega
  | succ W ih =>
    rw [windowBlocks_succ]
    by_cases he : w=W
    · subst w; exact ⟨[],by simp only [List.nil_append]⟩
    · obtain ⟨pre,hp⟩ := ih (by omega)
      rw [hp]
      exact ⟨topBlocks a (J W)++accurateBlock m ((100:ℝ)^W/4)++pre,by simp only [List.append_assoc]⟩

lemma windowBlocks_mem (a : ℝ) (m : ℕ) (J : ℕ → Finset ℕ) {W n : ℕ}
    (hn : n∈windowBlocks a m J W) :
    ∃ w<W, n∈topBlocks a (J w) ∨ n∈accurateBlock m ((100:ℝ)^w/4) := by
  obtain ⟨w,hw,hn⟩ := List.mem_flatMap.mp hn
  exact ⟨w,List.mem_range.mp (List.mem_reverse.mp hw),List.mem_append.mp hn⟩

/- Source: WindowParameters.lean lines 260--269. -/
lemma topBlock_separated {a : ℝ} (ha : 0<a) {i j K : ℕ}
    (hgap : a≤(2:ℝ)^K*topCoefficient a) (hij : i+K≤j) :
    ∀ n∈topBlock a i, (n:ℝ)≤Real.exp (topParameter*topCoefficient a*(2:ℝ)^j) := by
  apply topBlock_bound ha.le
  have hh := mul_le_mul_of_nonneg_left hgap (show 0≤(2:ℝ)^i by positivity)
  rw [←mul_assoc,←pow_add] at hh
  have hp : (2:ℝ)^(i+K)≤(2:ℝ)^j := pow_le_pow_right₀ (by norm_num) hij
  have hp' := mul_le_mul_of_nonneg_right hp (topCoefficient_pos ha).le
  have hg := mul_le_mul_of_nonneg_left (hh.trans hp') topParameter_pos.le
  nlinarith only [hg]

/- Source: Smoothing.lean lines 18--84. -/
lemma smaller_window_operations {a : ℝ} (ha : 0≤a) (ha1 : a≤1)
    (m w : ℕ) (J : ℕ → Finset ℕ)
    (hJ : ∀ i<w, ∀ j∈J i, (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m)) :
    ∀ n∈windowBlocks a m J w,
      (n:ℝ)≤Real.exp (Real.exp (((100:ℝ)^w/50)*Real.exp m)) := by
  intro n hn
  obtain ⟨i,hi,hni⟩ := windowBlocks_mem a m J hn
  have hh := mul_le_mul_of_nonneg_right (window_power_step hi) (Real.exp_nonneg (m:ℝ))
  have hi0 : 0≤(100:ℝ)^i*Real.exp m := by positivity
  rcases hni with hni|hni
  · obtain ⟨j,hj,hnj⟩ := List.mem_flatMap.mp hni
    have hj' : j∈J i := (Finset.mem_sort (·≥·)).mp hj
    have hp : (2:ℝ)^j≤Real.exp (((100:ℝ)^w/50)*Real.exp m) := by
      rw [←Real.exp_log (by positivity : (0:ℝ)<2^j),Real.log_pow]
      apply Real.exp_le_exp.mpr
      nlinarith only [hJ i hi j hj',hh,hi0]
    apply topBlock_bound ha j _ n hnj
    have hc : topParameter*a≤1 := by
      have hg : topParameter≤1 := by norm_num [topParameter]
      exact (mul_le_mul_of_nonneg_left ha1 topParameter_pos.le).trans (by simpa only [mul_one] using hg)
    exact (mul_le_of_le_one_left (by positivity : (0:ℝ)≤2^j) hc).trans hp
  · apply accurateBlock_bound (accurateGrid_le_one m) _ n hni
    have he : Real.exp (((100:ℝ)^i/4)*Real.exp m)≤Real.exp (((100:ℝ)^w/50)*Real.exp m) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hh,hi0]
    exact (mul_le_of_le_one_left (Real.exp_nonneg _) (accurateGrid_le_one m)).trans he

lemma windowBlocks_length_bound {C : ℝ} {a : ℝ} (m W : ℕ)
    (J : ℕ → Finset ℕ) (hJ : ∀ w<W, ((J w).card:ℝ)≤C) :
    ((windowBlocks a m J W).length:ℝ)≤(W:ℝ)*(20*C+4*(m:ℝ)^2) := by
  induction W with
  | zero => simp [windowBlocks]
  | succ W ih =>
    have hi := ih (fun w hw => hJ w (by omega))
    rw [windowBlocks_succ,List.length_append,List.length_append]
    simp only [topBlocks_length,Nat.cast_add,Nat.cast_mul,topIterations,Nat.cast_ofNat,
      accurateBlock,List.length_ofFn,accurateIterations,Nat.cast_pow]
    have hh := hJ W (by omega)
    have hW : (W:ℝ)+1=(W+1:ℕ) := by push_cast; rfl
    push_cast
    nlinarith only [hi,hh]

lemma windowBlocks_length_bound_of_bins {a : ℝ} {m W : ℕ}
    (J : ℕ → Finset ℕ) (hm : 2≤Real.exp m)
    (hJ : ∀ w<W, ∀ j∈J w, (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^w*Real.exp m)) :
    ((windowBlocks a m J W).length:ℝ)≤
      (W:ℝ)*(60*(100:ℝ)^W*Real.exp m+4*(m:ℝ)^2) := by
  have hb : ∀ w<W, ((J w).card:ℝ)≤3*(100:ℝ)^W*Real.exp m := by
    intro w hw
    have hw1 := window_power_one w
    have hs : 2≤(100:ℝ)^w*Real.exp m := by nlinarith only [hw1,hm]
    have hh := narrow_bins_card hs (J w) (hJ w hw)
    have hp : (100:ℝ)^w≤(100:ℝ)^W := pow_le_pow_right₀ (by norm_num) hw.le
    have he := mul_le_mul_of_nonneg_right hp (Real.exp_nonneg (m:ℝ))
    nlinarith only [hh,he]
  have hh := windowBlocks_length_bound (a := a) m W J hb
  nlinarith only [hh]

lemma eventually_window_length (W : ℕ) :
    ∀ᶠ m : ℕ in atTop,
      (W:ℝ)*(60*(100:ℝ)^W*Real.exp m+4*(m:ℝ)^2)+4*(m:ℝ)^2+2≤Real.exp (Real.exp m) := by
  have hp := eventually_poly_le_exp (4*((W:ℝ)+1)) (a := 1) (by norm_num) 2
  have ht := (eventually_mul_le_double_exp (a := 1) (by norm_num) (60*W*(100:ℝ)^W+3))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hp,ht] with m hm ht
  simp only [one_mul] at hm ht
  have he : 1≤Real.exp (m:ℝ) := Real.one_le_exp_iff.mpr (Nat.cast_nonneg _)
  nlinarith only [hm,ht,he]

/- Source: AccurateScales.lean lines 318--332, real mean adaptation. -/
lemma bandSize_lower_of_scale {μ g U C T : ℝ} {l : ℕ}
    (hmean : 0< μ) (hlog : 0<Real.log T)
    (hm : μ≤2*Real.log T)
    (hV : 2*μ≤bandScale g U l)
    (hscale : C*T≤bandScale g U l) :
    C*T/(4*Real.log T)≤(bandSize μ g U l:ℝ) := by
  have hf := Nat.lt_floor_add_one (bandScale g U l/μ)
  have hh := mul_lt_mul_of_pos_right hf hmean
  rw [div_mul_cancel₀ _ hmean.ne',add_mul,one_mul] at hh
  have hlo : bandScale g U l/2≤(bandSize μ g U l:ℝ)*μ := by
    change _≤(⌊bandScale g U l/μ⌋₊:ℝ)*_
    linarith only [hh,hV]
  have hu := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (bandSize μ g U l))
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith only [hlo,hu,hscale]


/- New generic wrappers for the actual floor-based band parameters. -/
lemma bandSize_mul_bounds {μ g U : ℝ} (hμ : 0<μ) {j : ℕ}
    (hV : 0≤bandScale g U j) :
    bandScale g U j-μ≤(bandSize μ g U j:ℝ)*μ ∧
      (bandSize μ g U j:ℝ)*μ≤bandScale g U j := by
  have hlo := mul_lt_mul_of_pos_right
    (Nat.lt_floor_add_one (bandScale g U j/μ)) hμ
  rw [div_mul_cancel₀ _ hμ.ne',add_mul,one_mul] at hlo
  have hhi := mul_le_mul_of_nonneg_right
    (Nat.floor_le (div_nonneg hV hμ.le)) hμ.le
  rw [div_mul_cancel₀ _ hμ.ne'] at hhi
  exact ⟨by change _≤(⌊bandScale g U j/μ⌋₊:ℝ)*_; linarith only [hlo],hhi⟩

lemma bandSize_mul_half {μ g U : ℝ} (hμ : 0<μ) {j : ℕ}
    (hV : 2*μ≤bandScale g U j) :
    bandScale g U j/2≤(bandSize μ g U j:ℝ)*μ := by
  have hb := (bandSize_mul_bounds hμ (by linarith only [hV,hμ])).1
  linarith only [hb,hV]

lemma bandLength_log_bounds {g U : ℝ} {j : ℕ}
    (hV : 2≤g*bandScale g U j) :
    1≤bandLength g U j ∧
      g*bandScale g U j-1≤Real.log (bandLength g U j:ℝ) ∧
      Real.log (bandLength g U j:ℝ)≤g*bandScale g U j :=
  log_floor_exp hV

end Entry002
