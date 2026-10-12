import Entry002.GenericWindowSchedule
import Entry002.ArithmeticCore
import Entry002.GenericWindowEntropy
import Entry002.WeakCoreGeometricBands

/-! Core-only replay of the round-five owned `GenericWindowEntropy` source.
All original proof bodies, mathematical objects, and source-license provenance
are retained; the arithmetic premise is exactly A1--A4. This new namespace
does not construct the former natural-density field. -/


/-! Actual endpoint entropy for literal subbands inside the common window.
The schedule is a concrete list of actual difference kernels. Every later
entropy loss is bounded by the actual planar displacement ball.
-/
set_option autoImplicit false
namespace Entry002.WeakA5
open Module Filter
open OAI.GaussianMoat
open scoped BigOperators Classical
variable {L : Type*} [AddCommGroup L]

/-- A selected band survives arbitrary preceding operations and its true
suffix, with all its geometric margins derived from explicit scalar bounds. -/
theorem commonSchedule_subband_geometric_entropy (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (A : ArithmeticCore data b e) {D g : ℝ}
    (hD : 1≤D) (hg : 0<g) (hg1 : g≤1/200)
    (S : Finset ℕ) (X : ℝ) (hS : ∀ p∈S,p∈data.primes) (hne : S.Nonempty)
    (hmean : 1≤_root_.Entry002.FreshEntropy.batchMeanLog S)
    (hmeanup : _root_.Entry002.FreshEntropy.batchMeanLog S≤2*X)
    (P : TimeLaw) (z : ℕ → L) (hinj : Function.Injective z)
    (hs : ∀t,dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1)))≤D)
    (T : ℝ) (hT : 5≤T) (hpT : ∀p∈S,T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (U : ℝ) (l : ℕ) (pre post : List ℕ) (N : ℕ) (err : ℝ)
    (hguard : ∀j<l,geometricGuardConstant data b e A D≤g^2*bandScale g U j)
    (hrelative : ∀j<l,1280*X≤g^5*bandScale g U j)
    (hcap : ∀j<l,bandSize (_root_.Entry002.FreshEntropy.batchMeanLog S) g U j≤S.card)
    (hsuffix : Real.log (wordStepBall b e (D*(post.sum+N))).card≤
      err*(bandSize (_root_.Entry002.FreshEntropy.batchMeanLog S) g U l:ℝ)*_root_.Entry002.FreshEntropy.batchMeanLog S) :
    let μ := _root_.Entry002.FreshEntropy.batchMeanLog S
    (1-(1/2:ℝ)^l-80*g-err)*(bandSize μ g U l:ℝ)*μ≤
      signedPointEntropy data S (P.advance (commonSchedule z
        (pre++List.ofFn (fun i : Fin l => bandLength g U i.val)++post) N)).law
        (fun t=>z t.val) (bandSize μ g U l) := by
  let Q := P.advance (commonSchedule z pre 0)
  have hbase := explicit_band_geometric_entropy data b e A hD hg hg1
    S X hS hne hmean hmeanup Q z hinj hs T hT hpT U l hguard hrelative hcap
  dsimp only at hbase
  have hloss := (Q.run z (bandLength g U) l).advance_entropy (commonSchedule z post N)
    data S hS b e z (by linarith only [hD]) hs
    (bandSize (_root_.Entry002.FreshEntropy.batchMeanLog S) g U l)
  rw [commonSchedule_bound] at hloss
  simp only [Nat.cast_add] at hloss
  have he : P.advance (commonSchedule z
      (pre++List.ofFn (fun i : Fin l => bandLength g U i.val)++post) N)=
      (Q.run z (bandLength g U) l).advance (commonSchedule z post N) := by
    rw [List.append_assoc,commonSchedule_append,TimeLaw.advance_then,
      TimeLaw.advance_common_append,TimeLaw.foldl_ofFn]
  rw [he]
  nlinarith only [hbase,hloss,hsuffix]

/-- Exact-start form used by actual backward coverage and future kernels. -/
theorem commonSchedule_subband_geometric_entropy_at (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (A : ArithmeticCore data b e) {D g : ℝ}
    (hD : 1≤D) (hg : 0<g) (hg1 : g≤1/200)
    (S : Finset ℕ) (X : ℝ) (hS : ∀p∈S,p∈data.primes) (hne : S.Nonempty)
    (hmean : 1≤_root_.Entry002.FreshEntropy.batchMeanLog S)
    (hmeanup : _root_.Entry002.FreshEntropy.batchMeanLog S≤2*X)
    (z : ℕ → L) (hinj : Function.Injective z)
    (hs : ∀t,dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1)))≤D)
    (T : ℝ) (hT : 5≤T) (hpT : ∀p∈S,T≤(p:ℝ) ∧ (p:ℝ)≤2*T)
    (U : ℝ) (l : ℕ) (pre post : List ℕ) (N : ℕ) (err : ℝ)
    (hguard : ∀j<l,geometricGuardConstant data b e A D≤g^2*bandScale g U j)
    (hrelative : ∀j<l,1280*X≤g^5*bandScale g U j)
    (hcap : ∀j<l,bandSize (_root_.Entry002.FreshEntropy.batchMeanLog S) g U j≤S.card)
    (hsuffix : Real.log (wordStepBall b e (D*(post.sum+N))).card≤
      err*(bandSize (_root_.Entry002.FreshEntropy.batchMeanLog S) g U l:ℝ)*_root_.Entry002.FreshEntropy.batchMeanLog S)
    (a : ℕ) :
    let μ := _root_.Entry002.FreshEntropy.batchMeanLog S
    (1-(1/2:ℝ)^l-80*g-err)*(bandSize μ g U l:ℝ)*μ≤
      signedPointEntropy data S ((commonSchedule z
        (pre++List.ofFn (fun i : Fin l => bandLength g U i.val)++post) N).law a)
        (fun t=>z (a+t.val)) (bandSize μ g U l) := by
  have h := commonSchedule_subband_geometric_entropy data b e A hD hg hg1 S X
    hS hne hmean hmeanup (TimeLaw.at a) z hinj hs T hT hpT U l pre post N err
    hguard hrelative hcap hsuffix
  simpa only [signedPointEntropy_exact_start] using h

/-- Dense actual batches give endpoint entropy for an accurate band in any
literal schedule with numerically bounded suffix operations. The suffix cost
and every geometric guard are derived before any time law or walk is chosen. -/
theorem eventually_accurate_common_subband_entropy (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (A : ArithmeticCore data b e) {D α B a c δ : ℝ}
    (hD : 1≤D) (hα : 0<α) (hB : 0<B) (ha : 0<a) (haα : a<α)
    (hc : 0<c) (hca : c<a/2) (hδ : 0<δ) :
    ∀ᶠ m : ℕ in atTop, ∀ (S : Finset ℕ) (T : ℝ) (pre post : List ℕ) (N : ℕ),
      (∀p∈S,p∈data.primes) → S.Nonempty →
      (∀p∈S,T≤(p:ℝ) ∧ (p:ℝ)≤2*T) →
      δ*T/Real.log (2*T)≤S.card → Real.exp (α*Real.exp m)≤T →
      Real.log T≤B*Real.exp m →
      (∀n∈post,(n:ℝ)≤Real.exp (Real.exp (c*Real.exp m))) →
      (N:ℝ)≤Real.exp (Real.exp (c*Real.exp m)) →
      (post.length+2:ℝ)≤Real.exp (Real.exp (c*Real.exp m)) →
      ∀ (P : TimeLaw) (z : ℕ → L), Function.Injective z →
      (∀t,dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1)))≤D) →
      let μ := _root_.Entry002.FreshEntropy.batchMeanLog S
      let q := bandSize μ (accurateGrid m) (Real.exp (a*Real.exp m)) (accurateIterations m)
      (1-91*accurateGrid m)*(q:ℝ)*μ≤signedPointEntropy data S
        (P.advance (commonSchedule z (pre++accurateBlock m a++post) N)).law
        (fun t=>z t.val) q := by
  filter_upwards [eventually_accurate_actual_batch_guards hα hB ha haα hδ
    (geometricGuardConstant data b e A D),
    eventually_accurate_suffix_cost b e hD ha hc hca hB,
    eventually_accurate_small (show (0:ℝ)<1/200 by norm_num)] with m hguards hcost hsmall
  intro S T pre post N hS hne hp hdense hT hThi hops hN hlen P z hinj hs
  obtain ⟨hT5,hmean,hmeanup,hready⟩ := hguards S T hne hp hdense hT hThi
  have hmeanpos : 0<_root_.Entry002.FreshEntropy.batchMeanLog S := by linarith only [hmean]
  have hcst := hcost S post N hmeanpos hmeanup hops hN hlen
  have hbase := commonSchedule_subband_geometric_entropy data b e A hD
    (accurateGrid_pos m) hsmall S ((B+1)*Real.exp m) hS hne hmean hmeanup
    P z hinj hs T hT5 hp (Real.exp (a*Real.exp m)) (accurateIterations m)
    pre post N (10*accurateGrid m)
    (fun k hk => (hready k hk.le).1)
    (fun k hk => (hready k hk.le).2.1)
    (fun k hk => (hready k hk.le).2.2) hcst
  dsimp only at hbase
  have hcoef : 1-91*accurateGrid m≤
      1-(1/2:ℝ)^accurateIterations m-80*accurateGrid m-10*accurateGrid m := by
    linarith only [accurateIterations_error m]
  have hmass : 0≤(bandSize (_root_.Entry002.FreshEntropy.batchMeanLog S) (accurateGrid m)
      (Real.exp (a*Real.exp m)) (accurateIterations m):ℝ)*_root_.Entry002.FreshEntropy.batchMeanLog S :=
    mul_nonneg (Nat.cast_nonneg _) hmeanpos.le
  have hh := mul_le_mul_of_nonneg_right hcoef hmass
  simp only [←mul_assoc] at hh
  dsimp only
  unfold accurateBlock
  exact hh.trans hbase

/-- Both actual future endpoints in a selected window. No endpoint entropy,
margin, or suffix-cost conclusion is assumed. -/
theorem eventually_window_band_entropy (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (A : ArithmeticCore data b e) {D a δ : ℝ}
    (hD : 1≤D) (ha : 0≤a) (ha1 : a≤1) (hδ : 0<δ)
    (W w : ℕ) (hw : w<W) :
    ∀ᶠ m : ℕ in atTop, ∀ J : ℕ → Finset ℕ,
      (∀i<W,∀j∈J i,(100:ℝ)^i*Real.exp m≤(j:ℝ)*Real.log 2 ∧
        (j:ℝ)*Real.log 2≤21/20*((100:ℝ)^i*Real.exp m) ∧
        δ*(2:ℝ)^j/Real.log ((2:ℝ)^(j+1))≤(dyadicPrimeBatch data.primes j).card) →
      ∀j∈J w,∀(z : ℕ → L),Function.Injective z →
      (∀t,dist (planarEmbedding b e (z t)) (planarEmbedding b e (z (t+1)))≤D) →
      ∀P : TimeLaw,
      let S := dyadicPrimeBatch data.primes j
      let μ := _root_.Entry002.FreshEntropy.batchMeanLog S
      let qmid := bandSize μ (accurateGrid m)
        (Real.exp (((100:ℝ)^w/4)*Real.exp m)) (accurateIterations m)
      let qbot := bandSize μ (accurateGrid m)
        (Real.exp ((1/20)*Real.exp m)) (accurateIterations m)
      (1-91*accurateGrid m)*(qmid:ℝ)*μ≤signedPointEntropy data S
        (P.advance (commonSchedule z (middleBlocks a m w J) 0)).law
        (fun t=>z t.val) qmid ∧
      (1-91*accurateGrid m)*(qbot:ℝ)*μ≤signedPointEntropy data S
        (P.advance (commonSchedule z (accurateBlock m (1/20)) (windowSmoothing W m))).law
        (fun t=>z t.val) qbot := by
  have hwp := window_power_one w
  have hp : (0:ℝ)<100^w := by positivity
  have hmid := eventually_accurate_common_subband_entropy data b e A
    (α := (100:ℝ)^w) (B := 2*(100:ℝ)^w)
    (a := (100:ℝ)^w/4) (c := (100:ℝ)^w/50)
    hD hp (by positivity) (by positivity) (by linarith only [hp])
    (by positivity) (by linarith only [hp]) hδ
  have hbot := eventually_accurate_common_subband_entropy data b e A
    (α := 1) (B := 2*(100:ℝ)^w) (a := 1/20) (c := 1/100)
    hD (by norm_num) (by positivity) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hδ
  filter_upwards [hmid,hbot,eventually_window_tail_bounds b e hD ha ha1 W w hw]
    with m hmid hbot htail
  intro J hJ j hj z hinj hs P
  have hdata := hJ w hw j hj
  let S := dyadicPrimeBatch data.primes j
  have hne : S.Nonempty := dyadicPrimeBatch_nonempty_of_dense data.primes j hδ hdata.2.2
  have hS : ∀p∈S,p∈data.primes := fun p hp => ((mem_dyadicPrimeBatch _ _ _).mp hp).1
  have hpT : ∀p∈S,(2:ℝ)^j≤(p:ℝ) ∧ (p:ℝ)≤2*(2:ℝ)^j := by
    intro p hp
    exact ⟨((mem_dyadicPrimeBatch _ _ _).mp hp).2.1,
      by simpa only [pow_succ,mul_comm] using ((mem_dyadicPrimeBatch _ _ _).mp hp).2.2⟩
  have hdense : δ*(2:ℝ)^j/Real.log (2*(2:ℝ)^j)≤S.card := by
    simpa only [pow_succ,mul_comm] using hdata.2.2
  have hT : Real.exp ((100:ℝ)^w*Real.exp m)≤(2:ℝ)^j := by
    rw [←Real.exp_log (by positivity : (0:ℝ)<2^j),Real.log_pow]
    exact Real.exp_le_exp.mpr hdata.1
  have hThi : Real.log ((2:ℝ)^j)≤(2*(100:ℝ)^w)*Real.exp m := by
    rw [Real.log_pow]
    nlinarith only [hdata.2.1,show 0≤(100:ℝ)^w*Real.exp m by positivity]
  obtain ⟨_,hN,hlen,_,_⟩ := htail J (fun i hi k hk => (hJ i hi k hk).2.1)
  have hmid' := hmid S ((2:ℝ)^j) [] (windowBlocks a m J w) 0 hS hne hpT hdense hT hThi
    (smaller_window_operations ha ha1 m w J (fun i hi k hk => (hJ i (hi.trans hw) k hk).2.1))
    (by simp only [Nat.cast_zero]; positivity) hlen P z hinj hs
  have hTwo : (2:ℝ)≤Real.exp (Real.exp ((1/100)*Real.exp m)) := by
    have he : 1≤Real.exp ((1/100)*Real.exp (m:ℝ)) := Real.one_le_exp_iff.mpr (by positivity)
    linarith only [Real.add_one_le_exp (Real.exp ((1/100)*Real.exp (m:ℝ))),he]
  have hbot' := hbot S ((2:ℝ)^j) [] [] (windowSmoothing W m) hS hne hpT hdense
    ((Real.exp_le_exp.mpr (by nlinarith only [hwp,Real.exp_pos (m:ℝ)] :
      1*Real.exp m≤(100:ℝ)^w*Real.exp m)).trans hT)
    hThi (by simp only [List.not_mem_nil,IsEmpty.forall_iff,implies_true]) hN
    (by simpa only [List.length_nil,Nat.cast_zero,zero_add] using hTwo) P z hinj hs
  dsimp only at hmid' hbot'
  rw [List.nil_append] at hmid'
  rw [List.nil_append,List.append_nil] at hbot'
  exact ⟨hmid',hbot'⟩

end Entry002.WeakA5
