import Entry002.GenericBackwardKernelCoverage
import Entry002.GenericDensityBands
import Entry002.GenericCommonWindowNumerics

/-!
# Actual backward schedule coverage and pooled batch charge

The finite selection and package transport below replay the proved construction
in GenericBatchSelection (adapted from OpenAI family028 InformationTelescope,
commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0), retaining its
actual selected-label witness. Backward coverage is derived from the entropy of
the two actual schedule factors, rather than supplied as an information premise.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Entry002
open OAI.GaussianMoat
open scoped BigOperators Classical
variable {L Ω Γ : Type*} [AddCommGroup L] [Fintype Ω] [Fintype Γ]

lemma selectedBatchLabels_subset (S : Finset ℕ) {b : ℕ} (hb : b ≤ S.card)
    (σ : Fin S.card → Bool) (π : Equiv.Perm (Fin S.card)) :
    selectedBatchLabels S hb σ π ⊆ S ×ˢ (Finset.univ : Finset Bool) := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  exact Finset.mem_product.mpr ⟨signedBatchPrime_mem S _, Finset.mem_univ _⟩

theorem exists_pooled_residueFamily_batch_extension (data : SignedResidueData L)
    (S : Finset ℕ) (hne : S.Nonempty) (hS : ∀ q ∈ S, q ∈ data.primes) (p : FinLaw Ω)
    (F : Finset (ℕ × Bool)) (hF : ∀ i ∈ F, i.1 ∈ data.primes) (X : Ω → L) (q : Ω → FinLaw Γ) {b : ℕ} (hb : b ≤ S.card)
    (hit : (i : BatchSignedIndex S) → Γ → ZMod (signedBatchPrime S i.2) → Prop)
    (Good : BatchSignedIndex S → Ω → Prop)
    (exception : (i : BatchSignedIndex S) → Ω → Finset (ZMod (signedBatchPrime S i.2)))
    (e c : BatchSignedIndex S → ℝ) {A η δ : ℝ} (n : ℕ)
    (hA : 0 ≤ A) (he : ∀ i, 0 ≤ e i) (hc : ∀ i, 0 ≤ c i)
    (htrue : ∀ ω, p ω ≠ 0 → ∀ v, q ω v ≠ 0 → ∀ i,
      ¬hit i v (data.phi (signedBatchPrime S i.2) (i.1 i.2) (X ω)))
    (hE : ∀ i ω, Good i ω → ((exception i ω).card : ℝ) ≤ e i)
    (hhit : ∀ i ω, Good i ω → ∀ x ∉ exception i ω,
      c i ≤ (q ω).prob (fun v => hit i v x))
    (hnum : ∀ i, Real.log (4 * e i + (signedBatchPrime S i.2 : ℝ) *
      Real.exp (-(n : ℝ) * (c i / 4))) ≤ Real.log (signedBatchPrime S i.2) - A)
    (hH : (1-δ) * (b : ℝ) * batchMeanLog S ≤ signedPointEntropy data S p X b)
    (hBad : (𝔼 i : BatchSignedIndex S, p.prob (fun ω => ¬Good i ω)) ≤ η)
    {len : ℕ} (hlen : 0 < len) (hn : 0 < n) {r : ℝ}
    (hrate : (n : ℝ) * (len : ℝ) * r ≤
      (b : ℝ) * (A * (1-2*η)-δ * batchMeanLog S)-F.sum (fun i => Real.log i.1)) :
    ∃ G : Finset (ℕ × Bool), F ⊆ G ∧ G ⊆ F ∪ (S ×ˢ (Finset.univ : Finset Bool)) ∧
      (∀ i ∈ G, i.1 ∈ data.primes) ∧ (G \ F).card ≤ b ∧
      G.sum (fun i => Real.log i.1) ≤ F.sum (fun i => Real.log i.1) +
        2 * S.sum (fun q => Real.log q) ∧
      r ≤ (p.joint q).cIf (fun v => residueFamilyHom data G (X v.1))
        Prod.snd (fun v => residueFamilyHom data F (X v.1)) / len := by
  let _ := residueFamilyFintype data F hF
  obtain ⟨σ, π, hinfo⟩ := exists_signed_batch_information data S hne hS p
    (fun ω => residueFamilyHom data F (X ω)) X q hb hit Good exception e c n
    hA he hc htrue hE hhit hnum hH (residueFamily_entropy_le data F hF p X)
    hBad hlen hn hrate
  let B := selectedBatchLabels S hb σ π
  refine ⟨F ∪ B, Finset.subset_union_left, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ hi
    · exact Finset.mem_union_right _ (selectedBatchLabels_subset S hb σ π hi)
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hF i hi
    · exact selectedBatchLabels_prime_mem data S hS hb σ π i hi
  · have hsub : (F ∪ B) \ F ⊆ B := by
      intro i hi
      obtain ⟨hi, hnF⟩ := Finset.mem_sdiff.mp hi
      exact (Finset.mem_union.mp hi).resolve_left hnF
    exact (Finset.card_le_card hsub).trans (selectedBatchLabels_card_le S hb σ π)
  · exact (residueLabels_union_log_weight_le data F B
      (selectedBatchLabels_prime_mem data S hS hb σ π)).trans
      (add_le_add le_rfl (selectedBatchLabels_log_weight_le data S hS hb σ π))
  · have heq := selectedBatchLabels_union_information data S hS F hb σ π
      (p.joint q) (fun v => X v.1) Prod.snd
    rw [heq]
    exact hinfo


/-- Genuine lower word-information rate from actual finite signed batch
coverage and point entropy, for an arbitrary actual forward kernel.
The package survival and information transport are proved from zero-class
avoidance, the bounded walk and actual finite displacement support. -/
theorem exists_pooled_walk_residue_batch_extension (data : SignedResidueData L)
    (S : Finset ℕ) (hne : S.Nonempty) (hS : ∀ q ∈ S, q ∈ data.primes)
    (F : Finset (ℕ × Bool)) (hF : ∀ i ∈ F, i.1 ∈ data.primes)
    (p : FinLaw Ω) (a : Ω → ℕ) (K : ForwardKernel) (z : ℕ → L)
    (basis : Module.Basis (Fin 2) ℤ L) (embedding : CoeffSpace ≃ₗ[ℝ] Plane)
    {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (planarEmbedding basis embedding (z t))
      (planarEmbedding basis embedding (z (t+1))) ≤ D)
    (havoid : ∀ t, z t ∈ avoiding data S) {b len : ℕ} (hb : b ≤ S.card)
    (hlen : 0 < len)
    (Good : BatchSignedIndex S → Ω → Prop)
    (exception : (i : BatchSignedIndex S) → Ω → Finset (ZMod (signedBatchPrime S i.2)))
    (e c : BatchSignedIndex S → ℝ) {A η δ r : ℝ} (n : ℕ) (hn : 0 < n)
    (hA : 0 ≤ A) (he : ∀ i, 0 ≤ e i) (hc : ∀ i, 0 ≤ c i)
    (hE : ∀ i ω, Good i ω → ((exception i ω).card : ℝ) ≤ e i)
    (hhit : ∀ i ω, Good i ω → ∀ x ∉ exception i ω,
      c i ≤ (K.packageLaw basis embedding z hD hs (a ω) len).prob
        (fun v => WalkPackage.Hits (data.phi (signedBatchPrime S i.2) (i.1 i.2)) v x))
    (hnum : ∀ i, Real.log (4 * e i + (signedBatchPrime S i.2 : ℝ) *
      Real.exp (-(n : ℝ) * (c i / 4))) ≤ Real.log (signedBatchPrime S i.2) - A)
    (hH : (1-δ) * (b : ℝ) * batchMeanLog S ≤
      signedPointEntropy data S p (fun ω => z (a ω)) b)
    (hBad : (𝔼 i : BatchSignedIndex S, p.prob (fun ω => ¬Good i ω)) ≤ η)
    (hrate : (n : ℝ) * ((len : ℝ) * r +
      2 * Real.log (wordStepBall basis embedding (D*K.bound)).card) ≤
      (b : ℝ) * (A * (1-2*η)-δ * batchMeanLog S)-F.sum (fun i => Real.log i.1)) :
    ∃ G : Finset (ℕ × Bool), F ⊆ G ∧ G ⊆ F ∪ (S ×ˢ (Finset.univ : Finset Bool)) ∧
      (∀ i ∈ G, i.1 ∈ data.primes) ∧ (G \ F).card ≤ b ∧
      G.sum (fun i => Real.log i.1) ≤ F.sum (fun i => Real.log i.1) +
        2 * S.sum (fun q => Real.log q) ∧
      r ≤ (p.joint (fun ω => K.law (a ω))).cIf
        (fun v => residueFamilyHom data G (z (a v.1+v.2.val)))
        (fun v => incrementWord z len (a v.1+v.2.val))
        (fun v => residueFamilyHom data F (z (a v.1+v.2.val))) / len := by
  let C : ℝ := Real.log (wordStepBall basis embedding (D*K.bound)).card
  have hlenR : (0 : ℝ) < len := by exact_mod_cast hlen
  have hrate' : (n : ℝ) * (len : ℝ) * (((len : ℝ)*r+2*C)/len) ≤
      (b : ℝ) * (A*(1-2*η)-δ*batchMeanLog S)-F.sum (fun i => Real.log i.1) := by
    convert hrate using 1; dsimp only [C]
    field_simp
  obtain ⟨G, hFG, hpool, hG, hcard, hcost, hinfo⟩ := exists_pooled_residueFamily_batch_extension
    data S hne hS p F hF (fun ω => z (a ω))
    (fun ω => K.packageLaw basis embedding z hD hs (a ω) len) hb
    (fun i => WalkPackage.Hits (data.phi (signedBatchPrime S i.2) (i.1 i.2)))
    Good exception e c n hA he hc
    (fun ω _ v hv i => K.signed_package_true_survives data S z havoid
      (signedBatchPrime_mem S i.2) (i.1 i.2) basis embedding hD hs (a ω) len v hv)
    hE hhit hnum hH hBad hlen hn hrate'
  refine ⟨G, hFG, hpool, hG, hcard, hcost, ?_⟩
  have hpackage := K.package_information_transport p a (residueFamilyHom data G)
    (residueFamilyHom data F) basis embedding z hD hs len
  have hi := (div_le_div_iff_of_pos_right hlenR).mp hinfo
  apply (le_div_iff₀ hlenR).mpr
  dsimp only [C] at hi
  nlinarith only [hi, hpackage]


theorem commonSchedule_passingGood_bad_mean_of_entropy
    (data : SignedResidueData L) (S : Finset ℕ) (hne : S.Nonempty)
    (hS : ∀ q ∈ S, q ∈ data.primes)
    (basis : Module.Basis (Fin 2) ℤ L) (embedding : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L) (pre post : List ℕ) (N : ℕ)
    {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (planarEmbedding basis embedding (z t))
      (planarEmbedding basis embedding (z (t+1)))≤D)
    (p : FinLaw Ω) (a : Ω → ℕ) (u u' c : BatchSignedIndex S → ℝ)
    {τ δ err η εK εR cR v : ℝ} {n m mR : ℕ}
    (hn : 0<n) (hm : 0<m) (hmk : m≤S.card) (hmR : 0<mR) (hmRk : mR≤S.card)
    (hτ : 0≤τ) (hτnext : τ+4*δ≤3/8) (hδ : 0<δ) (hδ1 : δ≤1/64)
    (herr0 : 0≤err) (hη : 0<η) (hcR : 0<cR) (hu : ∀ i, 0<u i)
    (hu'floor : ∀ i, 8*cR*(signedBatchPrime S i.2 : ℝ)≤u' i)
    (hK : ∀ a, (1-εK)*(m : ℝ)*batchMeanLog S≤
      signedPointEntropy data S ((commonSchedule z pre 0).law a) (fun t => z (a+t.val)) m)
    (hR : ∀ t, (1-εR)*(mR : ℝ)*batchMeanLog S≤
      signedPointEntropy data S ((commonSchedule z post N).law t) (fun j => z (t+j.val)) mR)
    (hsmall : εR*batchMeanLog S/cR+err≤η*δ/2)
    (hscale : 2*(1-Real.log (η*δ/2))≤v)
    (hgap : εK*batchMeanLog S+(n : ℝ)*
      Real.log (wordStepBall basis embedding (D*(post.sum+N))).card/m<η*δ*v/4)
    (hc : ∀ i, 1≤c i) (hv : ∀ i, v≤Real.log (signedBatchPrime S i.2)-Real.log (c i))
    (hu' : ∀ i, u' i/δ≤c i)
    (herr : ∀ i, (signedBatchPrime S i.2 : ℝ)*
      Real.exp (-(n : ℝ)*δ^2*u i/(2*(signedBatchPrime S i.2 : ℝ)))≤err) :
    (𝔼 i : BatchSignedIndex S, p.prob (fun ω =>
      ¬(commonSchedule z (pre++post) N).passingGood data S hS z a τ u i ω)) ≤ η := by
  let _ : Nonempty (BatchSignedIndex S) := ⟨(fun _ => true, ⟨0,hne.card_pos⟩)⟩
  let K := commonSchedule z (pre++post) N
  let Bad := fun (ω : Ω) (i : BatchSignedIndex S) =>
    u i ≤ ((K.passingException data S hS z (a ω) i τ).card : ℝ)
  have he (ω : Ω) : (FinLaw.uniform (BatchSignedIndex S)).prob (Bad ω) =
      𝔼 i : BatchSignedIndex S, (if Bad ω i then (1 : ℝ) else 0) := by
    rw [← FinLaw.uniform_expect]
    unfold FinLaw.prob
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  have hswap : (𝔼 i : BatchSignedIndex S, p.prob (fun ω => Bad ω i)) =
      ∑ ω, p ω*(FinLaw.uniform (BatchSignedIndex S)).prob (Bad ω) := by
    simp only [FinLaw.prob, Finset.expect_sum_comm]
    apply Finset.sum_congr rfl
    intro ω _
    change (𝔼 i : BatchSignedIndex S, (if Bad ω i then p ω else 0)) = _
    rw [show (∑ i : BatchSignedIndex S, if Bad ω i then
      FinLaw.uniform (BatchSignedIndex S) i else 0) =
      (FinLaw.uniform (BatchSignedIndex S)).prob (Bad ω) from rfl, he, Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro i _
    split_ifs <;> simp
  change (𝔼 i : BatchSignedIndex S, p.prob (fun ω =>
    ¬((K.passingException data S hS z (a ω) i τ).card : ℝ) < u i)) ≤ _
  simp only [not_lt]
  change (𝔼 i : BatchSignedIndex S, p.prob (fun ω => Bad ω i)) ≤ _
  rw [hswap]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun ω _ =>
    mul_le_mul_of_nonneg_left
      (commonSchedule_coverage_backward_of_entropy data S hne hS basis embedding z
        pre post N hD hs (a ω) u u' c hn hm hmk hmR hmRk hτ hτnext hδ hδ1
        herr0 hη hcR hu hu'floor (hK (a ω)) hR hsmall hscale hgap hc hv hu' herr)
      (p.nonneg ω))
  simpa only [← Finset.sum_mul, p.sum_one, one_mul] using hs

theorem exists_backward_commonSchedule_batch_charge
    (data : SignedResidueData L) (S : Finset ℕ) (hne : S.Nonempty)
    (hS : ∀ q ∈ S, q ∈ data.primes)
    (basis : Module.Basis (Fin 2) ℤ L) (embedding : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L) (pre post : List ℕ) (N : ℕ)
    {D : ℝ} (hD : 0≤D)
    (hs : ∀ t, dist (planarEmbedding basis embedding (z t))
      (planarEmbedding basis embedding (z (t+1)))≤D)
    (P : TimeLaw) (u u' c : BatchSignedIndex S → ℝ)
    {τ δ err η εK εR cR v : ℝ} {n m mR : ℕ}
    (hn : 0<n) (hm : 0<m) (hmk : m≤S.card) (hmR : 0<mR) (hmRk : mR≤S.card)
    (hτ : 0≤τ) (hτnext : τ+4*δ≤3/8) (hδ : 0<δ) (hδ1 : δ≤1/64)
    (herr0 : 0≤err) (hη : 0<η) (hcR : 0<cR) (hu : ∀ i, 0<u i)
    (hu'floor : ∀ i, 8*cR*(signedBatchPrime S i.2 : ℝ)≤u' i)
    (hK : ∀ a, (1-εK)*(m : ℝ)*batchMeanLog S≤
      signedPointEntropy data S ((commonSchedule z pre 0).law a) (fun t => z (a+t.val)) m)
    (hR : ∀ t, (1-εR)*(mR : ℝ)*batchMeanLog S≤
      signedPointEntropy data S ((commonSchedule z post N).law t) (fun j => z (t+j.val)) mR)
    (hsmall : εR*batchMeanLog S/cR+err≤η*δ/2)
    (hscale : 2*(1-Real.log (η*δ/2))≤v)
    (hgap : εK*batchMeanLog S+(n : ℝ)*
      Real.log (wordStepBall basis embedding (D*(post.sum+N))).card/m<η*δ*v/4)
    (hc : ∀ i, 1≤c i) (hv : ∀ i, v≤Real.log (signedBatchPrime S i.2)-Real.log (c i))
    (hu' : ∀ i, u' i/δ≤c i)
    (herr : ∀ i, (signedBatchPrime S i.2 : ℝ)*
      Real.exp (-(n : ℝ)*δ^2*u i/(2*(signedBatchPrime S i.2 : ℝ)))≤err)
    (F : Finset (ℕ × Bool)) (hF : ∀ i ∈ F, i.1 ∈ data.primes)
    (pool : Finset ℕ) (hFpool : F ⊆ pool ×ˢ (Finset.univ : Finset Bool))
    (hSpool : S ⊆ pool)
    (hz : Function.Injective z) (havoid : ∀ t, z t ∈ avoiding data S)
    {γ : ℝ}
    (hcollision : ∀ q ∈ data.primes, ∀ σ : Bool, ∀ x : L, x ≠ 0 → data.phi q σ x = 0 →
      γ*Real.sqrt (q : ℝ) ≤ ‖planarEmbedding basis embedding x‖)
    {k len : ℕ} (hk : k ≤ S.card) (hlen : 0 < len) (hLN : len ≤ N)
    (hshort : ∀ i : BatchSignedIndex S,
      D*len < γ*Real.sqrt (signedBatchPrime S i.2 : ℝ))
    (hsmooth : ∀ i : BatchSignedIndex S,
      (len : ℝ)/(N+1) ≤ (τ/(signedBatchPrime S i.2 : ℝ))/2)
    {A δAnchor r : ℝ} (hA : 0 ≤ A)
    (hAnchor : (1-δAnchor)*(k : ℝ)*batchMeanLog S ≤
      signedPointEntropy data S P.law (fun ω => z ω.val) k)
    (nsample : ℕ) (hnsample : 0 < nsample)
    (hnum : ∀ i : BatchSignedIndex S, Real.log (4*u i + (signedBatchPrime S i.2 : ℝ)*
      Real.exp (-(nsample : ℝ)*(((len : ℝ)*(τ/(signedBatchPrime S i.2 : ℝ))/2)/4))) ≤
        Real.log (signedBatchPrime S i.2)-A)
    (hrate : (nsample : ℝ)*((len : ℝ)*r +
      2*Real.log (wordStepBall basis embedding
        (D*(commonSchedule z (pre++post) N).bound)).card) ≤
      (k : ℝ)*(A*(1-2*η)-δAnchor*batchMeanLog S)-F.sum (fun i => Real.log i.1)) :
    ∃ G : Finset (ℕ × Bool), F ⊆ G ∧
      G ⊆ pool ×ˢ (Finset.univ : Finset Bool) ∧
      G ⊆ F ∪ (S ×ˢ (Finset.univ : Finset Bool)) ∧
      (∀ i ∈ G, i.1 ∈ data.primes) ∧ (G \ F).card ≤ k ∧
      G.sum (fun i => Real.log i.1) ≤ F.sum (fun i => Real.log i.1) +
        2*S.sum (fun q => Real.log q) ∧
      r ≤ (P.advance (commonSchedule z (pre++post) N)).info
        (fun t => residueFamilyHom data G (z t))
        (incrementWord z len) (fun t => residueFamilyHom data F (z t)) / len := by
  let K := commonSchedule z (pre++post) N
  let Good := K.passingGood data S hS z (fun ω : Fin (P.last+1) => ω.val) τ u
  let exception := fun (i : BatchSignedIndex S) ω =>
    K.passingException data S hS z (ω : Fin (P.last+1)).val i τ
  have hBad := commonSchedule_passingGood_bad_mean_of_entropy data S hne hS
    basis embedding z pre post N hD hs P.law Fin.val u u' c
    hn hm hmk hmR hmRk hτ hτnext hδ hδ1 herr0 hη hcR hu hu'floor
    hK hR hsmall hscale hgap hc hv hu' herr
  have hhit : ∀ i ω, Good i ω → ∀ x ∉ exception i ω,
      (len : ℝ)*(τ/(signedBatchPrime S i.2 : ℝ))/2 ≤
      (K.packageLaw basis embedding z hD hs ω.val len).prob
        (fun v => WalkPackage.Hits (data.phi (signedBatchPrime S i.2) (i.1 i.2)) v x) := by
    intro i ω _ x hx
    have hh := (commonSchedule z (pre++post) 0).smoothed_package_floor
      data S hS i basis embedding z hz hD hs
      (hcollision _ (hS _ (signedBatchPrime_mem S i.2)) (i.1 i.2))
      (hshort i) hLN (hsmooth i) ω.val x
    rw [← commonSchedule_smooth] at hh
    exact hh hx
  obtain ⟨G, hFG, hGlocal, hG, hcard, hcost, hinfo⟩ :=
    exists_pooled_walk_residue_batch_extension data S hne hS F hF P.law Fin.val
      K z basis embedding hD hs havoid hk hlen Good exception u
      (fun i => (len : ℝ)*(τ/(signedBatchPrime S i.2 : ℝ))/2)
      nsample hnsample hA (fun i => (hu i).le)
      (fun i => div_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hτ (Nat.cast_nonneg _)))
        (by norm_num)) (fun i ω hg => hg.le) hhit hnum hAnchor hBad hrate
  refine ⟨G, hFG, ?_, hGlocal, hG, hcard, hcost, ?_⟩
  · intro i hi
    rcases Finset.mem_union.mp (hGlocal hi) with hi | hi
    · exact hFpool hi
    · obtain ⟨hip, his⟩ := Finset.mem_product.mp hi
      exact Finset.mem_product.mpr ⟨hSpool hip, his⟩
  · simpa only [TimeLaw.advance_info] using hinfo


/-- Positive pooled charge with the actual one-step backward constants. The
three smallness hypotheses concern genuine entropy deficits and the actual
continuation-ball cost. No residue coverage or information rate is assumed. -/
theorem exists_positive_dyadic_backward_batch_charge
    (data : SignedResidueData L) (S : Finset ℕ) (hne : S.Nonempty)
    (hS : ∀ q ∈ S, q ∈ data.primes)
    (basis : Module.Basis (Fin 2) ℤ L) (embedding : CoeffSpace ≃ₗ[ℝ] Plane)
    (z : ℕ → L) (pre post : List ℕ) (N : ℕ) (P : TimeLaw)
    (J : ℕ → Finset ℕ) (W : ℕ) (hSpool : S ⊆ dyadicPrimePool data J W)
    (F : Finset (ℕ × Bool)) (hF : ∀ i ∈ F, i.1 ∈ data.primes)
    (hFpool : F ⊆ dyadicPrimePool data J W ×ˢ (Finset.univ : Finset Bool))
    {D γ X εK εR r : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (planarEmbedding basis embedding (z t))
      (planarEmbedding basis embedding (z (t+1))) ≤ D)
    (hz : Function.Injective z) (havoid : ∀ t, z t ∈ avoiding data S)
    (hcollision : ∀ q ∈ data.primes, ∀ σ : Bool, ∀ x : L,
      x ≠ 0 → data.phi q σ x = 0 → γ*Real.sqrt (q : ℝ) ≤
        ‖planarEmbedding basis embedding x‖)
    {n m mR k len : ℕ} (hn : 0 < n) (hm : 0 < m) (hmk : m ≤ S.card)
    (hmR : 0 < mR) (hmRk : mR ≤ S.card) (hk : k ≤ S.card)
    (hlen : 0 < len) (hLN : len ≤ N)
    (hprime : ∀ i : BatchSignedIndex S, Real.exp 100 ≤ (signedBatchPrime S i.2 : ℝ))
    (hK : ∀ a, (1-εK)*(m : ℝ)*batchMeanLog S ≤
      signedPointEntropy data S ((commonSchedule z pre 0).law a)
        (fun t => z (a+t.val)) m)
    (hR : ∀ t, (1-εR)*(mR : ℝ)*batchMeanLog S ≤
      signedPointEntropy data S ((commonSchedule z post N).law t)
        (fun j => z (t+j.val)) mR)
    (hbase : εR*batchMeanLog S ≤ Real.exp (-100)/(512*640000))
    (hmid : εK*batchMeanLog S ≤ 1/1024)
    (hcost : (n : ℝ)*Real.log
      (wordStepBall basis embedding (D*(post.sum+N))).card/m ≤ 1/1024)
    (hhazard : ∀ i : BatchSignedIndex S, (signedBatchPrime S i.2 : ℝ)*
      Real.exp (-(n : ℝ)*(1/64)^2*
        ((signedBatchPrime S i.2 : ℝ)*Real.exp (-X/200))/
        (2*(signedBatchPrime S i.2 : ℝ))) ≤ 1/640000)
    (hshort : ∀ i : BatchSignedIndex S,
      D*len < γ*Real.sqrt (signedBatchPrime S i.2 : ℝ))
    (hsmooth : ∀ i : BatchSignedIndex S,
      (len : ℝ)/(N+1) ≤ ((1/4)/(signedBatchPrime S i.2 : ℝ))/2)
    (hAnchor : (1-1/10000)*(k : ℝ)*batchMeanLog S ≤
      signedPointEntropy data S P.law (fun ω => z ω.val) k)
    (nsample : ℕ) (hnsample : 0 < nsample) (hX : 0 ≤ X) (hr : 0 < r)
    (hnum : ∀ i : BatchSignedIndex S, Real.log
      (4*((signedBatchPrime S i.2 : ℝ)*Real.exp (-X/200)) +
        (signedBatchPrime S i.2 : ℝ)*Real.exp (-(nsample : ℝ)*
          (((len : ℝ)*((1/4)/(signedBatchPrime S i.2 : ℝ))/2)/4))) ≤
      Real.log (signedBatchPrime S i.2)-X/400)
    (hrate : (nsample : ℝ)*((len : ℝ)*r +
      2*Real.log (wordStepBall basis embedding
        (D*(commonSchedule z (pre++post) N).bound)).card) ≤
      (k : ℝ)*((X/400)*(1-2*(1/100))-(1/10000)*batchMeanLog S)-
        F.sum (fun i => Real.log i.1)) :
    ∃ G : Finset (ℕ × Bool), F ⊆ G ∧
      G ⊆ dyadicPrimePool data J W ×ˢ (Finset.univ : Finset Bool) ∧
      G ⊆ F ∪ (S ×ˢ (Finset.univ : Finset Bool)) ∧
      (∀ i ∈ G, i.1 ∈ data.primes) ∧ (G \ F).card ≤ k ∧
      G.sum (fun i => Real.log i.1) ≤ F.sum (fun i => Real.log i.1) +
        2*S.sum (fun q => Real.log q) ∧
      r ≤ (P.advance (commonSchedule z (pre++post) N)).info
        (fun t => residueFamilyHom data G (z t)) (incrementWord z len)
        (fun t => residueFamilyHom data F (z t)) / len ∧
      0 < (P.advance (commonSchedule z (pre++post) N)).info
        (fun t => residueFamilyHom data G (z t)) (incrementWord z len)
        (fun t => residueFamilyHom data F (z t)) / len := by
  let u := fun i : BatchSignedIndex S =>
    (signedBatchPrime S i.2 : ℝ)*Real.exp (-X/200)
  let u' := fun i : BatchSignedIndex S => Real.exp (-100)*(signedBatchPrime S i.2 : ℝ)/64
  let c := fun i : BatchSignedIndex S => Real.exp (-100)*(signedBatchPrime S i.2 : ℝ)
  have scalar := fun i : BatchSignedIndex S =>
    one_step_coverage_scalar_guards (hprime i) hbase hmid hcost
  have hpi (i : BatchSignedIndex S) : 0 < (signedBatchPrime S i.2 : ℝ) :=
    (Real.exp_pos 100).trans_le (hprime i)
  let i₀ : BatchSignedIndex S := (fun _ => true, ⟨0,hne.card_pos⟩)
  obtain ⟨G, hFG, hpool, hlocal, hG, hcard, hweight, hinfo⟩ :=
    exists_backward_commonSchedule_batch_charge data S hne hS basis embedding z pre post N
      hD hs P u u' c hn hm hmk hmR hmRk (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (scalar i₀).1
      (fun i => mul_pos (hpi i) (Real.exp_pos _))
      (fun i => (scalar i).2.1.le) hK hR (scalar i₀).2.2.1
      (scalar i₀).2.2.2.1 (scalar i₀).2.2.2.2.1
      (fun i => (scalar i).2.2.2.2.2.1)
      (fun i => (scalar i).2.2.2.2.2.2.1)
      (fun i => (scalar i).2.2.2.2.2.2.2.le) hhazard
      F hF (dyadicPrimePool data J W) hFpool hSpool hz havoid hcollision hk hlen hLN
      hshort hsmooth (div_nonneg hX (by norm_num)) hAnchor nsample hnsample hnum hrate
  exact ⟨G, hFG, hpool, hlocal, hG, hcard, hweight, hinfo, hr.trans_le hinfo⟩

end Entry002
