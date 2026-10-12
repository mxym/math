import Entry002.GenericSignSeparation
import Entry002.GenericResidues
import Entry002.GenericFreshCoverage
import Entry002.ArithmeticCore
import Entry002.GenericFreshEntropy
import Entry002.WeakCoreSignSeparation

/-! Core-only replay of the round-five owned `GenericFreshEntropy` source.
All original proof bodies, mathematical objects, and source-license provenance
are retained; the arithmetic premise is exactly A1--A4. This new namespace
does not construct the former natural-density field. -/


/-! Actual finite-law displacement entropy from genuine signed-kernel rectangle
probability. Generic finite-law proofs adapted from OpenAI family 028,
FreshEntropy.lean, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a. -/

namespace Entry002.WeakA5.FreshEntropy
universe uKappa uBeta uIota uOmega uXi uAlpha
open Module
open OAI.GaussianMoat
open Entry002.WeakA5.SignSeparation
open scoped BigOperators Classical
variable {L : Type*} [AddCommGroup L]

theorem expect_restrict {κ : Type uKappa} {β : Type uBeta} [Fintype κ] [Fintype β] [Nonempty β]
    (s : Finset κ) (F : (s → β) → ℝ) :
    (𝔼 σ : κ → β, F (fun p => σ p)) = 𝔼 τ : s → β, F τ := by
  classical
  let e := Equiv.piEquivPiSubtypeProd (fun x => x ∈ s) (fun _ => β)
  calc
    _ = 𝔼 pair : (s → β) × ({x : κ // x ∉ s} → β), F pair.1 := by
      exact Fintype.expect_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      rw [← Finset.univ_product_univ,Finset.expect_product]
      simp only [Fintype.expect_const]

theorem expect_precomp_injective {ι : Type uIota} {κ : Type uKappa} {β : Type uBeta} [Fintype ι] [Fintype κ]
    [Fintype β] [Nonempty β] (e : ι → κ) (he : Function.Injective e)
    (F : (ι → β) → ℝ) :
    (𝔼 σ : κ → β, F (σ ∘ e)) = 𝔼 τ : ι → β, F τ := by
  classical
  let s := Finset.univ.image e
  let ee : ι ≃ s := Equiv.ofBijective (fun i => ⟨e i, Finset.mem_image.mpr
    ⟨i,Finset.mem_univ _,rfl⟩⟩) ⟨fun i j h => he (congrArg Subtype.val h),by
      rintro ⟨y,hy⟩
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hy
      exact ⟨i,Subtype.ext hi⟩⟩
  calc
    _ = 𝔼 τ : s → β, F (fun i => τ (ee i)) := expect_restrict s _
    _ = _ := by
      exact Fintype.expect_equiv (Equiv.arrowCongr ee.symm (Equiv.refl β)) _ _ (fun _ => rfl)

lemma signMeasure_real_eq_expect {ι : Type uIota} [Fintype ι] (S : Set (ι → Bool)) :
    (signMeasure ι).real S = 𝔼 σ : ι → Bool, if σ ∈ S then (1 : ℝ) else 0 := by
  rw [signMeasure_real_set]
  simp [Finset.expect,NNRat.smul_def,div_eq_inv_mul]

lemma expect_sign_restriction {ι : Type uIota} {κ : Type uKappa} [Fintype ι] [Fintype κ]
    (e : ι → κ) (he : Function.Injective e) (S : Set (ι → Bool)) :
    (𝔼 σ : κ → Bool, if σ ∘ e ∈ S then (1 : ℝ) else 0) =
      (signMeasure ι).real S := by
  exact (expect_precomp_injective e he (fun τ => if τ ∈ S then (1 : ℝ) else 0)).trans
    (signMeasure_real_eq_expect S).symm

lemma uniform_entropy_event_bound {Ω : Type uOmega} {Ξ : Type uXi} {α : Type uAlpha} [Fintype Ω] [Nonempty Ω]
    [Fintype Ξ] [Nonempty Ξ] (X : Ξ → Ω → α) (bad : Ξ → Prop)
    (hg : ∀ σ, ¬bad σ → Function.Injective (X σ)) :
    (1-(𝔼 σ, if bad σ then (1 : ℝ) else 0))*Real.log (Fintype.card Ω) ≤
      𝔼 σ, (FinLaw.uniform Ω).Hf (X σ) := by
  have hp (σ : Ξ) : (1-(if bad σ then (1 : ℝ) else 0))*Real.log (Fintype.card Ω) ≤
      (FinLaw.uniform Ω).Hf (X σ) := by
    by_cases hb : bad σ
    · simpa [hb] using (FinLaw.uniform Ω).Hf_nonneg (X σ)
    · simp only [hb,ite_false,sub_zero,one_mul]
      rw [FinLaw.uniform_Hf_injective _ (hg σ hb)]
  have h := Finset.expect_le_expect (s := Finset.univ) (fun σ _ => hp σ)
  simpa only [← Finset.expect_mul,Finset.expect_sub_distrib,Fintype.expect_const] using h

noncomputable def prefixIndices (k r : ℕ) : Finset (Fin k) :=
  Finset.univ.filter (fun i => i.val < r)

lemma mem_prefixIndices {k r : ℕ} (i : Fin k) : i ∈ prefixIndices k r ↔ i.val < r := by
  simp [prefixIndices]

lemma prefixIndices_card {k r : ℕ} (hr : r ≤ k) : (prefixIndices k r).card = r := by
  have he : prefixIndices k r = (Finset.univ : Finset (Fin r)).image
      (fun i => (⟨i.val,by omega⟩ : Fin k)) := by
    ext i
    simp only [mem_prefixIndices,Finset.mem_image,Finset.mem_univ,true_and]
    exact ⟨fun hi => ⟨⟨i.val,hi⟩,rfl⟩,fun ⟨j,hj⟩ => by cases hj; exact j.isLt⟩
  have hinj : Function.Injective (fun i : Fin r => (⟨i.val,by omega⟩ : Fin k)) :=
    fun i j h => Fin.ext (congrArg (fun j : Fin k => j.val) h)
  rw [he,Finset.card_image_of_injective _ hinj]
  exact Finset.card_fin r


noncomputable def batchPrefixSet (S : Finset ℕ)
    (π : Equiv.Perm (Fin S.card)) (r : ℕ) : Finset ℕ :=
  (prefixIndices S.card r).image (fun i => signedBatchPrime S (π i))

theorem batchPrefixSet_subset (S : Finset ℕ)
    (π : Equiv.Perm (Fin S.card)) (r : ℕ) : batchPrefixSet S π r ⊆ S := by
  intro p hp
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  exact signedBatchPrime_mem S _

theorem signedBatchPrime_injective (S : Finset ℕ) :
    Function.Injective (signedBatchPrime S) :=
  Subtype.val_injective.comp S.equivFin.symm.injective

theorem batchPrefixSet_card (S : Finset ℕ)
    (π : Equiv.Perm (Fin S.card)) {r : ℕ} (hr : r ≤ S.card) :
    (batchPrefixSet S π r).card = r := by
  have hinj : Function.Injective (fun i => signedBatchPrime S (π i)) :=
    (signedBatchPrime_injective S).comp π.injective
  rw [batchPrefixSet, Finset.card_image_of_injective _ hinj]
  exact prefixIndices_card hr

noncomputable def batchPrefixIndex (S : Finset ℕ)
    (π : Equiv.Perm (Fin S.card)) (r : ℕ) (p : batchPrefixSet S π r) : Fin S.card :=
  S.equivFin ⟨p.val, batchPrefixSet_subset S π r p.property⟩

theorem batchPrefixIndex_injective (S : Finset ℕ)
    (π : Equiv.Perm (Fin S.card)) (r : ℕ) : Function.Injective (batchPrefixIndex S π r) := by
  intro p q hpq
  apply Subtype.ext
  exact congrArg (fun y : S => y.val) (S.equivFin.injective hpq)

/-- Any collision of actual signed prime observations creates a genuine
nonzero common-kernel displacement in the prescribed difference region. -/
theorem prefix_injective_of_no_bad (data : SignedResidueData L) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) (π : Equiv.Perm (Fin S.card)) (r : ℕ)
    (σ : Fin S.card → Bool) (E : Finset L) (Q : Set L)
    (hE : ∀ x ∈ E, ∀ y ∈ E, x-y ∈ Q)
    (hb : ¬badSign data (batchPrefixSet S π r) Q (σ ∘ batchPrefixIndex S π r)) :
    Function.Injective (fun x : E =>
      FinLaw.prefixVar (fun x : E => signedResidueVector data S σ x) π r x) := by
  intro x y hxy
  apply Subtype.ext
  by_contra hne
  apply hb
  refine ⟨(x : L)-(y : L), hE x x.property y y.property, sub_ne_zero.mpr hne, ?_⟩
  intro p
  obtain ⟨i, hi, hp'⟩ := Finset.mem_image.mp p.property
  have hres := congrFun hxy i
  have hiv := (mem_prefixIndices i).mp hi
  simp only [FinLaw.prefixVar, hiv, ite_eq_left, Option.some.injEq] at hres
  have hidx : batchPrefixIndex S π r p = π i := by
    apply S.equivFin.symm.injective
    apply Subtype.ext
    simpa only [batchPrefixIndex, Equiv.symm_apply_apply, signedBatchPrime,
      signedBatchIndex] using hp'.symm
  have hprime : signedBatchPrime S (π i) = p.val := hp'
  let _ : NeZero p.val :=
    ⟨(data.prime_mem _ (hS _ (batchPrefixSet_subset S π r p.property))).ne_zero⟩
  have hfield : data.phi p.val (σ (π i)) (x : L) =
      data.phi p.val (σ (π i)) (y : L) := by
    simp only [signedResidueVector] at hres
    rw [hprime] at hres
    exact ZMod.val_injective p.val hres
  change data.phi p.val (σ (batchPrefixIndex S π r p)) ((x : L)-(y : L)) = 0
  rw [hidx, map_sub, hfield, sub_self]

/-- The proved rectangle kernel probability supplies a true prefix-observation
entropy lower bound for uniform actual lattice displacements. -/
theorem prefix_entropy_rectangle (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticCore data b e) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) (π : Equiv.Perm (Fin S.card))
    {r : ℕ} (hr : r ≤ S.card) (E : Finset L) (hEne : E.Nonempty)
    (o : Plane ≃ₗᵢ[ℝ] Plane) {T R W d : ℝ} (hT : 5 ≤ T)
    (hpT : ∀ p ∈ S, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1/4)
    (harea : max (2 / |planarCellDet e|)
      (Real.sqrt 2 * Real.sqrt (separationConstant data hArith)) * R * W ≤
      (∏ p ∈ batchPrefixSet S π r, (p : ℝ)) ^ (1-d))
    (hlarge : 1000 ≤ d^3*r)
    (hE : ∀ x ∈ E, ∀ y ∈ E, x-y ∈ latticeRectangle b e o R W) :
    let := hEne.to_subtype
    (1-Real.exp (-(d^3*r/5120)))*Real.log E.card ≤
      𝔼 σ : Fin S.card → Bool,
        (FinLaw.uniform E).Hf
          (FinLaw.prefixVar (fun x : E => signedResidueVector data S σ x) π r) := by
  let := hEne.to_subtype
  let t := batchPrefixSet S π r
  let Q := latticeRectangle b e o R W
  have htS : ∀ p ∈ t, p ∈ data.primes :=
    fun p hp => hS p (batchPrefixSet_subset S π r hp)
  have hc : t.card=r := batchPrefixSet_card S π hr
  have hprob : (𝔼 σ : Fin S.card → Bool,
      if badSign data t Q (σ ∘ batchPrefixIndex S π r) then (1 : ℝ) else 0) ≤
      Real.exp (-(d^3*r/5120)) := by
    calc
      _ = (signMeasure t).real {τ | badSign data t Q τ} := by
        convert expect_sign_restriction (batchPrefixIndex S π r)
          (batchPrefixIndex_injective S π r) {τ | badSign data t Q τ} using 1
        congr 1
        ext σ
        simp
      _ ≤ _ := by
        have ht := signed_rectangle data b e hArith t htS o hT
          (fun p hp => hpT p (batchPrefixSet_subset S π r hp))
          hW hWR hd hd1 harea (by rwa [hc])
        simpa only [hc] using ht
  have hg := uniform_entropy_event_bound
    (fun σ => FinLaw.prefixVar (fun x : E => signedResidueVector data S σ x) π r)
    (fun σ => badSign data t Q (σ ∘ batchPrefixIndex S π r))
    (fun σ hb => prefix_injective_of_no_bad data S hS π r σ E Q hE hb)
  simp only [Fintype.card_coe] at hg
  have hl : 0 ≤ Real.log (E.card : ℝ) := Real.log_nonneg (by exact_mod_cast hEne.card_pos)
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left hprob 1) hl).trans hg


lemma prefix_log_period (data : SignedResidueData L) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes)
    (π : Equiv.Perm (Fin S.card)) (r : ℕ) :
    Real.log (∏ p ∈ batchPrefixSet S π r, (p : ℝ)) =
      ∑ i ∈ prefixIndices S.card r, Real.log (signedBatchPrime S (π i) : ℕ) := by
  rw [log_period data (batchPrefixSet S π r)
    (fun p hp => hS p (batchPrefixSet_subset S π r hp))]
  rw [Finset.sum_coe_sort (batchPrefixSet S π r) (fun p : ℕ => Real.log (p : ℝ))]
  change (∑ p ∈ batchPrefixSet S π r, Real.log (p : ℝ)) = _
  unfold batchPrefixSet
  exact Finset.sum_image ((signedBatchPrime_injective S).comp π.injective).injOn

lemma prefix_product_tail (data : SignedResidueData L) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) (hk : 0 < S.card)
    {r : ℕ} (hr : r ≤ S.card) {T δ : ℝ} (hT : 0 < T) (hδ : 0 < δ)
    (hpT : ∀ p ∈ S, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T) :
    (𝔼 π : Equiv.Perm (Fin S.card),
      if Real.log (∏ p ∈ batchPrefixSet S π r, (p : ℝ)) < r*_root_.Entry002.FreshEntropy.batchMeanLog S-δ then (1 : ℝ) else 0) ≤
      r*(Real.log 2)^2/δ^2 := by
  let : Nonempty (Fin S.card) := ⟨⟨0,hk⟩⟩
  have hb (i : Fin S.card) : Real.log T ≤ Real.log (signedBatchPrime S i : ℕ) ∧
      Real.log (signedBatchPrime S i : ℕ) ≤ Real.log T+Real.log 2 := by
    have hh := hpT (signedBatchPrime S i) (signedBatchPrime_mem S i)
    constructor
    · exact Real.log_le_log hT hh.1
    · have h := Real.log_le_log (hT.trans_le hh.1) hh.2
      rwa [Real.log_mul (by norm_num : (2 : ℝ)≠0) hT.ne',add_comm] at h
  have h := perm_sample_interval_tail (fun i => Real.log (signedBatchPrime S i : ℕ))
    (prefixIndices S.card r) hδ hb
  convert h using 1 <;>
    simp only [prefixIndices_card hr,_root_.Entry002.FreshEntropy.batchMeanLog,← prefix_log_period data S hS]
  congr 1

theorem signed_prefix_entropy (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticCore data b e) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes)
    {r : ℕ} (hr : r ≤ S.card) (Δ : Finset L) (hΔne : Δ.Nonempty)
    {T R W d δ : ℝ} (o : Plane ≃ₗᵢ[ℝ] Plane) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ S, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1/4)
    (hδ : 0 < δ) (hgap : Real.log ((max (2 / |planarCellDet e|) (Real.sqrt 2 * Real.sqrt (separationConstant data hArith)))*R*W) ≤ (1-d)*(r*_root_.Entry002.FreshEntropy.batchMeanLog S-δ))
    (hlarge : 1000 ≤ d^3*r)
    (hΔ : ∀ x ∈ Δ, ∀ y ∈ Δ, x-y ∈ latticeRectangle b e o R W) :
    let := hΔne.to_subtype
    (1-r*(Real.log 2)^2/δ^2-Real.exp (-(d^3*r/5120)))*Real.log Δ.card ≤
      (FinLaw.uniform Δ).signedEntropy (fun σ x => signedResidueVector data S σ x) r := by
  let := hΔne.to_subtype
  have hk : 0 < S.card := by
    by_contra hn
    have hz : r=0 := by omega
    simp only [hz,Nat.cast_zero,mul_zero] at hlarge
    norm_num at hlarge
  have hscale : 0 < max (2 / |planarCellDet e|) (Real.sqrt 2 * Real.sqrt (separationConstant data hArith)) :=
    (div_pos (by norm_num) (abs_pos.mpr (planarCellDet_ne_zero e))).trans_le (le_max_left _ _)
  have hRW : 0 < (max (2 / |planarCellDet e|) (Real.sqrt 2 * Real.sqrt (separationConstant data hArith)))*R*W := by
    exact mul_pos (mul_pos hscale (by linarith)) (by linarith)
  have hlog : 0 ≤ Real.log (Δ.card : ℝ) := Real.log_nonneg (by exact_mod_cast hΔne.card_pos)
  let ε := Real.exp (-(d^3*r/5120))
  let bad (π : Equiv.Perm (Fin S.card)) :=
    Real.log (∏ p ∈ batchPrefixSet S π r, (p : ℝ)) < r*_root_.Entry002.FreshEntropy.batchMeanLog S-δ
  have hp (π : Equiv.Perm (Fin S.card)) :
      (1-(if bad π then (1 : ℝ) else 0)-ε)*Real.log Δ.card ≤
      𝔼 σ : Fin S.card → Bool,
        (FinLaw.uniform Δ).Hf (FinLaw.prefixVar (fun x : Δ => signedResidueVector data S σ x) π r) := by
    by_cases hb : bad π
    · have hn : 0 ≤ (𝔼 σ : Fin S.card → Bool,
          (FinLaw.uniform Δ).Hf (FinLaw.prefixVar (fun x : Δ => signedResidueVector data S σ x) π r)) :=
        Finset.expect_nonneg (fun _ _ => (FinLaw.uniform Δ).Hf_nonneg _)
      simp only [hb,ite_eq_left,sub_self,zero_sub]
      exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.exp_pos _).le) hlog).trans hn
    · simp only [hb,ite_false,sub_zero]
      apply prefix_entropy_rectangle data b e hArith S hS π hr Δ hΔne o hT hpT hW hWR hd hd1 ?_ hlarge hΔ
      have hP : 0 < (∏ p ∈ batchPrefixSet S π r, (p : ℝ)) := by
        exact Finset.prod_pos (fun p hp => by
          exact_mod_cast (data.prime_mem p (hS p (batchPrefixSet_subset S π r hp))).pos)
      apply (Real.log_le_log_iff hRW (Real.rpow_pos_of_pos hP _)).mp
      rw [Real.log_rpow hP]
      exact hgap.trans (mul_le_mul_of_nonneg_left (le_of_not_gt hb) (by linarith))
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun π _ => hp π)
  simp only [← Finset.expect_mul,Finset.expect_sub_distrib,Fintype.expect_const] at hav
  have hb := prefix_product_tail data S hS hk hr (by linarith : (0 : ℝ)<T) hδ hpT
  have hlow := mul_le_mul_of_nonneg_right (sub_le_sub_right (sub_le_sub_left hb 1) ε) hlog
  apply hlow.trans
  convert hav using 1
  unfold FinLaw.signedEntropy FinLaw.orderedEntropy
  exact Finset.expect_comm _ _ _


lemma residue_prefix_entropy_le {Ω : Type uOmega} [Fintype Ω]
    (data : SignedResidueData L) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) (P : FinLaw Ω) (Z : Ω → L)
    (σ : Fin S.card → Bool) {m : ℕ} (hb : m ≤ S.card)
    {U : ℝ} (hU : ∀ p ∈ S, Real.log (p : ℝ) ≤ U) :
    P.orderedEntropy (fun ω => signedResidueVector data S σ (Z ω)) m ≤ m*U := by
  have h (π : Equiv.Perm (Fin S.card)) := P.Hf_prefix_le_sum
    (fun ω => signedResidueVector data S σ (Z ω)) (fun _ => U)
    (fun i => (signedResidueVector_coordinate_entropy_le data S hS σ P Z i).trans
      (hU _ (signedBatchPrime_mem S i))) π hb
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun π _ => h π)
  simpa only [FinLaw.orderedEntropy,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
      Fintype.expect_const] using hh

theorem actual_fresh_entropy (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticCore data b e) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes)
    {m r : ℕ} (hbr : m < r) (hr : r ≤ S.card)
    (Δ : Finset L) (hΔne : Δ.Nonempty)
    (X Y : Δ → L) (hXY : ∀ ω, X ω-Y ω=ω)
    {T R W d δ : ℝ} (o : Plane ≃ₗᵢ[ℝ] Plane) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ S, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1/4)
    (hδ : 0 < δ) (hgap : Real.log ((max (2 / |planarCellDet e|) (Real.sqrt 2 * Real.sqrt (separationConstant data hArith)))*R*W) ≤ (1-d)*(r*_root_.Entry002.FreshEntropy.batchMeanLog S-δ))
    (hlarge : 1000 ≤ d^3*r)
    (hΔ : ∀ x ∈ Δ, ∀ y ∈ Δ, x-y ∈ latticeRectangle b e o R W) :
    let := hΔne.to_subtype
    (1-r*(Real.log 2)^2/δ^2-Real.exp (-(d^3*r/5120)))*Real.log Δ.card-
        2*m*Real.log (2*T) ≤
      (r-m : ℕ)*(𝔼 σ : Fin S.card → Bool,
        𝔼 π : Equiv.Perm (Fin S.card),
          (FinLaw.uniform Δ).cHf (fun ω => signedResidueVector data S σ ω (π ⟨m,by omega⟩))
            (fun ω => (FinLaw.prefixVar (fun x => signedResidueVector data S σ (X x)) π m ω,
              FinLaw.prefixVar (fun x => signedResidueVector data S σ (Y x)) π m ω))) := by
  let := hΔne.to_subtype
  let P := FinLaw.uniform Δ
  have hU (p : ℕ) (hp : p ∈ S) : Real.log (p : ℝ) ≤ Real.log (2*T) :=
    Real.log_le_log (by have := (hpT p hp).1; linarith) (hpT p hp).2
  have hp (σ : Fin S.card → Bool) := P.fresh_entropy_from_prefix
    (fun ω => signedResidueVector data S σ (X ω)) (fun ω => signedResidueVector data S σ (Y ω))
    (fun ω => signedResidueVector data S σ ω) hbr hr (by
      intro i ω ν hx hy
      let _ : NeZero (signedBatchPrime S i) :=
        ⟨(data.prime_mem _ (hS _ (signedBatchPrime_mem S i))).ne_zero⟩
      have hx' := ZMod.val_injective (signedBatchPrime S i) hx
      have hy' := ZMod.val_injective (signedBatchPrime S i) hy
      change (data.phi (signedBatchPrime S i) (σ i) (ω : L)).val =
        (data.phi (signedBatchPrime S i) (σ i) (ν : L)).val
      rw [← hXY ω, ← hXY ν, map_sub, map_sub, hx', hy'])
  have hX σ := residue_prefix_entropy_le data S hS P X σ (by omega : m ≤ S.card) hU
  have hY σ := residue_prefix_entropy_le data S hS P Y σ (by omega : m ≤ S.card) hU
  have hl (σ : Fin S.card → Bool) :
      P.orderedEntropy (fun ω => signedResidueVector data S σ ω) r-2*m*Real.log (2*T) ≤
      (r-m : ℕ)*(𝔼 π : Equiv.Perm (Fin S.card),
        P.cHf (fun ω => signedResidueVector data S σ ω (π ⟨m,by omega⟩))
          (fun ω => (FinLaw.prefixVar (fun x => signedResidueVector data S σ (X x)) π m ω,
            FinLaw.prefixVar (fun x => signedResidueVector data S σ (Y x)) π m ω))) := by
    linarith [hp σ,hX σ,hY σ]
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun σ _ => hl σ)
  simp only [Finset.expect_sub_distrib,Fintype.expect_const,← Finset.mul_expect] at hh
  have hg := signed_prefix_entropy data b e hArith S hS hr Δ hΔne o hT hpT hW hWR hd hd1 hδ hgap hlarge hΔ
  exact (sub_le_sub_right hg _).trans hh


/-- The complete lower bound feeds the shared actual fresh-coordinate API,
with no assumed signed-rectangle or fresh-entropy conclusion. -/
theorem actual_fresh_coordinate_entropy (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (hArith : ArithmeticCore data b e) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes)
    {m r : ℕ} (hbr : m < r) (hr : r ≤ S.card)
    (Δ : Finset L) (hΔne : Δ.Nonempty)
    (X Y : Δ → L) (hXY : ∀ ω, X ω-Y ω=ω)
    {T R W d δ : ℝ} (o : Plane ≃ₗᵢ[ℝ] Plane) (hT : 5 ≤ T)
    (hpT : ∀ p ∈ S, T ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2*T)
    (hW : 1 ≤ W) (hWR : W ≤ R) (hd : 0 < d) (hd1 : d < 1/4)
    (hδ : 0 < δ) (hgap : Real.log ((max (2 / |planarCellDet e|) (Real.sqrt 2 * Real.sqrt (separationConstant data hArith)))*R*W) ≤ (1-d)*(r*_root_.Entry002.FreshEntropy.batchMeanLog S-δ))
    (hlarge : 1000 ≤ d^3*r)
    (hΔ : ∀ x ∈ Δ, ∀ y ∈ Δ, x-y ∈ latticeRectangle b e o R W) :
    let := hΔne.to_subtype
    (1-r*(Real.log 2)^2/δ^2-Real.exp (-(d^3*r/5120)))*Real.log Δ.card-
        2*m*Real.log (2*T) ≤
      (r-m : ℕ) * signedFreshCoordinate data S (FinLaw.uniform Δ) X Y m (by omega) := by
  let := hΔne.to_subtype
  simpa only [signedFreshCoordinate, hXY] using
    actual_fresh_entropy data b e hArith S hS hbr hr Δ hΔne X Y hXY o hT hpT
      hW hWR hd hd1 hδ hgap hlarge hΔ

end Entry002.WeakA5.FreshEntropy
