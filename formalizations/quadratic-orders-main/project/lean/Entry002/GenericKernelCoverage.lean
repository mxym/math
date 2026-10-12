import Entry002.GenericWalkPackage
import Entry002.GenericBatchSelection

/-! Coverage for the actual signed-prime laws of actual forward walk kernels.
Low-mass exceptions are constructed, their entropy deficit bounds are derived,
and actual collision separation and uniform smoothing give package hit floors.
Adapted proof patterns: upstream-028 SignedResidues.lean 59–175,
EntropyBand.lean 60–131, WalkWords.lean 107–158, WalkPackage.lean 55–105,
commit adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0).
-/
namespace OAI.GaussianMoat.FinLaw
open scoped BigOperators Classical

noncomputable def lowResidues {G : Type*} [Fintype G] (p : FinLaw G) (τ : ℝ) : Finset G :=
  Finset.univ.filter (fun x => p x < τ/(Fintype.card G : ℝ))

lemma not_mem_lowResidues {G : Type*} [Fintype G] (p : FinLaw G) (τ : ℝ) (x : G) :
    x ∉ p.lowResidues τ ↔ τ/(Fintype.card G : ℝ) ≤ p x := by
  simp only [lowResidues, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]

lemma uniform_expect {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    (∑ i, FinLaw.uniform ι i*f i) = 𝔼 i, f i := by
  rw [Fintype.expect_eq_sum_div_card]
  simp only [FinLaw.uniform_mass, ← Finset.mul_sum, div_eq_inv_mul]

lemma cHf_const_right {Ω α β : Type*} [Fintype Ω]
    (p : FinLaw Ω) (X : Ω → α) (c : β) : p.cHf X (fun _ => c)=p.Hf X := by
  unfold cHf
  rw [p.Hf_const, sub_zero]
  apply p.Hf_eq_of_fibers
  intro ω ν
  simp only [Prod.mk.injEq, and_true]

theorem lowResidues_base {ι : Type*} [Fintype ι]
    (G : ι → Type*) [∀ i, Fintype (G i)] (w : FinLaw ι)
    (p : (i : ι) → FinLaw (G i)) (u : ι → ℝ) {τ c e : ℝ}
    (hτ : τ ≤ 3/8) (hc : 0 < c)
    (hu : ∀ i, 8*c*(Fintype.card (G i) : ℝ) ≤ u i)
    (hdef : (∑ i, w i*(Real.log (Fintype.card (G i))-(p i).entropy)) ≤ e) :
    w.prob (fun i => u i ≤ ((p i).lowResidues τ).card) ≤ e/c := by
  apply low_mass_average G w p (fun i => (p i).lowResidues τ) _ hc
  · intro i x hx
    exact ((Finset.mem_filter.mp hx).2).le.trans
      (div_le_div_of_nonneg_right hτ (Nat.cast_nonneg _))
  · intro i hi
    have hne := (p i).nonempty
    have hp : (0 : ℝ) < Fintype.card (G i) := by exact_mod_cast Fintype.card_pos
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8*(Fintype.card (G i) : ℝ))).mpr
    nlinarith only [hu i, hi]
  · exact hdef

end OAI.GaussianMoat.FinLaw

namespace Entry002
open OAI.GaussianMoat
open scoped BigOperators Classical
variable {L : Type*} [AddCommGroup L]

@[instance_reducible] noncomputable def batchResidueFintype (data : SignedResidueData L)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes) (i : BatchSignedIndex S) :
    Fintype (ZMod (signedBatchPrime S i.2)) := by
  let _ : NeZero (signedBatchPrime S i.2) :=
    ⟨(data.prime_mem _ (hS _ (signedBatchPrime_mem S i.2))).ne_zero⟩
  infer_instance

/-- Literal law of the signed residue of the actual endpoint displacement. -/
noncomputable def ForwardKernel.relativeResidueLaw (K : ForwardKernel)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes)
    (z : ℕ → L) (a : ℕ) (i : BatchSignedIndex S) :
    @FinLaw (ZMod (signedBatchPrime S i.2)) (batchResidueFintype data S hS i) := by
  let _ := batchResidueFintype data S hS i
  exact (K.law a).map (fun t => data.phi (signedBatchPrime S i.2) (i.1 i.2) (z (a+t.val)-z a))

/-- Constructed exceptional start residues are the negations of the actual
low-probability displacement residues. -/
noncomputable def ForwardKernel.passingException (K : ForwardKernel)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes)
    (z : ℕ → L) (a : ℕ) (i : BatchSignedIndex S) (τ : ℝ) :
    Finset (ZMod (signedBatchPrime S i.2)) := by
  let _ := batchResidueFintype data S hS i
  exact ((K.relativeResidueLaw data S hS z a i).lowResidues τ).image Neg.neg

lemma ForwardKernel.passingException_card (K : ForwardKernel)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes)
    (z : ℕ → L) (a : ℕ) (i : BatchSignedIndex S) (τ : ℝ) :
    (K.passingException data S hS z a i τ).card =
      (@FinLaw.lowResidues _ (batchResidueFintype data S hS i)
        (K.relativeResidueLaw data S hS z a i) τ).card := by
  apply Finset.card_image_of_injective
  exact neg_injective

lemma ForwardKernel.not_mem_passingException (K : ForwardKernel)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes)
    (z : ℕ → L) (a : ℕ) (i : BatchSignedIndex S) (τ : ℝ)
    (x : ZMod (signedBatchPrime S i.2)) (hx : x ∉ K.passingException data S hS z a i τ) :
    τ/(signedBatchPrime S i.2 : ℝ) ≤
      (K.law a).prob (fun t => data.phi (signedBatchPrime S i.2) (i.1 i.2) (z (a+t.val)-z a) = -x) := by
  let _ := batchResidueFintype data S hS i
  have hh : -x ∉ (K.relativeResidueLaw data S hS z a i).lowResidues τ := by
    intro h
    exact hx (Finset.mem_image.mpr ⟨-x, h, neg_neg x⟩)
  have he := ((K.relativeResidueLaw data S hS z a i).not_mem_lowResidues τ (-x)).mp hh
  let _ : NeZero (signedBatchPrime S i.2) :=
    ⟨(data.prime_mem _ (hS _ (signedBatchPrime_mem S i.2))).ne_zero⟩
  simpa only [ZMod.card, relativeResidueLaw, FinLaw.map_mass, FinLaw.prob] using he

/-- High actual signed point entropy controls the average signed residue
entropy deficit, also after an arbitrary old observation is revealed. -/
theorem signed_coverage_deficit {Ω O : Type*} [Fintype Ω]
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ q ∈ S, q ∈ data.primes)
    (p : FinLaw Ω) (Z : Ω → L) (C : Ω → O) (a : L) {m : ℕ}
    (hm : 0 < m) (hmk : m ≤ S.card) {ε E : ℝ}
    (hH : (1-ε)*(m : ℝ)*batchMeanLog S ≤ signedPointEntropy data S p Z m)
    (hC : p.Hf C ≤ E) :
    (𝔼 i : BatchSignedIndex S, (Real.log (signedBatchPrime S i.2) -
      p.cHf (fun ω => data.phi (signedBatchPrime S i.2) (i.1 i.2) (Z ω-a)) C)) ≤
      ε*batchMeanLog S + E/m := by
  have hc := p.signedEntropy_conditioning
    (fun σ ω => signedResidueVector data S σ (Z ω)) C hmk
  have he (i : BatchSignedIndex S) :
      p.cHf (fun ω => data.phi (signedBatchPrime S i.2) (i.1 i.2) (Z ω-a)) C =
        p.cHf (fun ω => signedResidueVector data S i.1 (Z ω) i.2) C := by
    let _ : NeZero (signedBatchPrime S i.2) :=
      ⟨(data.prime_mem _ (hS _ (signedBatchPrime_mem S i.2))).ne_zero⟩
    apply p.cHf_congr_fibers
    · intro ω ν
      rw [(data.phi (signedBatchPrime S i.2) (i.1 i.2)).map_sub,
        (data.phi (signedBatchPrime S i.2) (i.1 i.2)).map_sub, sub_left_inj]
      change _ ↔ (data.phi (signedBatchPrime S i.2) (i.1 i.2) (Z ω)).val =
        (data.phi (signedBatchPrime S i.2) (i.1 i.2) (Z ν)).val
      exact ⟨congrArg ZMod.val, fun h => ZMod.val_injective (signedBatchPrime S i.2) h⟩
    · intro ω ν; rfl
  have hd : (𝔼 i : BatchSignedIndex S, (Real.log (signedBatchPrime S i.2) -
      p.cHf (fun ω => data.phi (signedBatchPrime S i.2) (i.1 i.2) (Z ω-a)) C)) =
      batchMeanLog S - (𝔼 σ : Fin S.card → Bool, 𝔼 i : Fin S.card,
        p.cHf (fun ω => signedResidueVector data S σ (Z ω) i) C) := by
    simp only [he, Finset.expect_sub_distrib]
    simp only [BatchSignedIndex, ← Finset.univ_product_univ, Finset.expect_product,
      batchMeanLog, Fintype.expect_const]
  rw [hd]
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  apply (mul_le_mul_iff_right₀ hmp).mp
  rw [mul_add, mul_div_cancel₀ _ hmp.ne']
  change signedPointEntropy data S p Z m - p.Hf C ≤ _ at hc
  nlinarith only [hc, hH, hC]

/-- The previous deficit bound for the actual endpoint-displacement law. -/
lemma ForwardKernel.residue_deficit (K : ForwardKernel)
    (data : SignedResidueData L) (S : Finset ℕ) (_hne : S.Nonempty)
    (hS : ∀ q ∈ S, q ∈ data.primes) (z : ℕ → L) (a : ℕ)
    {m : ℕ} (hm : 0 < m) (hmk : m ≤ S.card) {ε : ℝ}
    (hH : (1-ε)*(m : ℝ)*batchMeanLog S ≤
      signedPointEntropy data S (K.law a) (fun t => z (a+t.val)) m) :
    (𝔼 i : BatchSignedIndex S, (Real.log (signedBatchPrime S i.2) -
      @FinLaw.entropy _ (batchResidueFintype data S hS i)
        (K.relativeResidueLaw data S hS z a i))) ≤ ε*batchMeanLog S := by
  let (i : BatchSignedIndex S) := batchResidueFintype data S hS i
  have hh := signed_coverage_deficit data S hS (K.law a) (fun t => z (a+t.val))
    (fun _ => ()) (z a) hm hmk hH (E := 0) (by rw [FinLaw.Hf_const])
  simp only [FinLaw.cHf_const_right, zero_div, add_zero] at hh
  simpa only [FinLaw.Hf_eq_H, FinLaw.H, relativeResidueLaw] using hh

/-- High actual point entropy makes the constructed exception sets small for
most actual signed primes. There is no assumed bad-prime bound. -/
theorem ForwardKernel.coverage_base (K : ForwardKernel)
    (data : SignedResidueData L) (S : Finset ℕ) (hne : S.Nonempty)
    (hS : ∀ q ∈ S, q ∈ data.primes) (z : ℕ → L) (a : ℕ)
    {m : ℕ} (hm : 0 < m) (hmk : m ≤ S.card) {ε τ c : ℝ}
    (u : BatchSignedIndex S → ℝ) (hτ : τ ≤ 3/8) (hc : 0 < c)
    (hu : ∀ i, 8*c*(signedBatchPrime S i.2 : ℝ) ≤ u i)
    (hH : (1-ε)*(m : ℝ)*batchMeanLog S ≤
      signedPointEntropy data S (K.law a) (fun t => z (a+t.val)) m) :
    let _ : Nonempty (BatchSignedIndex S) := ⟨(fun _ => true, ⟨0,hne.card_pos⟩)⟩
    (FinLaw.uniform (BatchSignedIndex S)).prob (fun i =>
      u i ≤ (K.passingException data S hS z a i τ).card) ≤ ε*batchMeanLog S/c := by
  let _ : Nonempty (BatchSignedIndex S) := ⟨(fun _ => true, ⟨0,hne.card_pos⟩)⟩
  let (i : BatchSignedIndex S) := batchResidueFintype data S hS i
  let (i : BatchSignedIndex S) : NeZero (signedBatchPrime S i.2) :=
    ⟨(data.prime_mem _ (hS _ (signedBatchPrime_mem S i.2))).ne_zero⟩
  simp only [passingException_card]
  apply FinLaw.lowResidues_base (fun i : BatchSignedIndex S => ZMod (signedBatchPrime S i.2))
    (FinLaw.uniform _) (K.relativeResidueLaw data S hS z a) u hτ hc
  · simpa only [ZMod.card] using hu
  · rw [FinLaw.uniform_expect]
    simpa only [ZMod.card] using K.residue_deficit data S hne hS z a hm hmk hH

/-- Actual collision separation makes the short residue-hit events disjoint. -/
lemma short_signed_residue_hits_disjoint (data : SignedResidueData L) (q : ℕ) (σ : Bool)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (z : ℕ → L) (hz : Function.Injective z) {D c : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D)
    (hcollision : ∀ x : L, x ≠ 0 → data.phi q σ x = 0 →
      c*Real.sqrt (q : ℝ) ≤ ‖planarEmbedding b e x‖)
    {len : ℕ} (hshort : D*len < c*Real.sqrt (q : ℝ)) (a t : ℕ) (x : ZMod q)
    (i j : Fin len) (hi : data.phi q σ (z (t+i.val)-z a) = x)
    (hj : data.phi q σ (z (t+j.val)-z a) = x) : i = j := by
  by_contra hij
  have hneq : z (t+i.val) ≠ z (t+j.val) := by
    intro he
    have ht := hz he
    apply hij
    apply Fin.ext
    omega
  have he : data.phi q σ (z (t+i.val)) = data.phi q σ (z (t+j.val)) := by
    have he := hi.trans hj.symm
    simpa only [map_sub, sub_left_inj] using he
  have hzero : data.phi q σ (z (t+i.val)-z (t+j.val)) = 0 := by
    rw [map_sub, he, sub_self]
  have hlo := hcollision _ (sub_ne_zero.mpr hneq) hzero
  have hhi := walk_pair_displacement b e z hD hs t len i.val j.val (by omega) (by omega)
  linarith only [hlo, hhi, hshort]

lemma short_signed_residue_hit_prob {Ω : Type*} [Fintype Ω] (p : FinLaw Ω)
    (data : SignedResidueData L) (q : ℕ) (σ : Bool)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (z : ℕ → L) (hz : Function.Injective z) {D c : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D)
    (hcollision : ∀ x : L, x ≠ 0 → data.phi q σ x = 0 →
      c*Real.sqrt (q : ℝ) ≤ ‖planarEmbedding b e x‖)
    {len : ℕ} (hshort : D*len < c*Real.sqrt (q : ℝ))
    (a : ℕ) (t : Ω → ℕ) (x : ZMod q) :
    p.prob (fun ω => ∃ i : Fin len, data.phi q σ (z (t ω+i.val)-z a)=x) =
      ∑ i : Fin len, p.prob (fun ω => data.phi q σ (z (t ω+i.val)-z a)=x) := by
  apply p.prob_exists_eq_sum_disjoint
  intro ω i j hi hj
  exact short_signed_residue_hits_disjoint data q σ b e z hz hD hs hcollision hshort
    a (t ω) x i j hi hj

/-- Uniform smoothing and actual short-hit disjointness amplify a scalar
residue floor into a genuine length-proportional package-hit floor. -/
theorem smoothed_signed_package_hit_lower {Ω : Type*} [Fintype Ω] (p : FinLaw Ω)
    (data : SignedResidueData L) (q : ℕ) (σ : Bool)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (z : ℕ → L) (hz : Function.Injective z) {D c τ : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D)
    (hcollision : ∀ x : L, x ≠ 0 → data.phi q σ x = 0 →
      c*Real.sqrt (q : ℝ) ≤ ‖planarEmbedding b e x‖)
    {len N : ℕ} (hshort : D*len < c*Real.sqrt (q : ℝ)) (hLN : len ≤ N)
    (herr : (len : ℝ)/(N+1) ≤ τ/2) (a : ℕ) (t : Ω → ℕ) (x : ZMod q)
    (hfloor : τ ≤ (p.joint (fun _ => FinLaw.uniform (Fin (N+1)))).prob
      (fun v => data.phi q σ (z (t v.1+v.2.val)-z a)=x)) :
    (len : ℝ)*τ/2 ≤ (p.joint (fun _ => FinLaw.uniform (Fin (N+1)))).prob
      (fun v => ∃ i : Fin len, data.phi q σ (z (t v.1+v.2.val+i.val)-z a)=x) := by
  rw [short_signed_residue_hit_prob _ data q σ b e z hz hD hs hcollision hshort a]
  have hh (i : Fin len) : τ/2 ≤
      (p.joint (fun _ => FinLaw.uniform (Fin (N+1)))).prob
        (fun v => data.phi q σ (z (t v.1+v.2.val+i.val)-z a)=x) := by
    have hp := p.smoothing_prob t N i.val (by omega) (fun u => data.phi q σ (z u-z a)=x)
    have he : (i.val : ℝ)/(N+1) ≤ τ/2 := by
      apply le_trans _ herr
      exact div_le_div_of_nonneg_right (by exact_mod_cast i.isLt.le) (by positivity)
    linarith only [hp, hfloor, he]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hh i)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_div_assoc] using h

/-- A derived hit floor outside the constructed actual residue exceptions. -/
theorem ForwardKernel.smoothed_package_floor (R : ForwardKernel)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes)
    (i : BatchSignedIndex S) (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (z : ℕ → L) (hz : Function.Injective z) {D c τ : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D)
    (hcollision : ∀ x : L, x ≠ 0 → data.phi (signedBatchPrime S i.2) (i.1 i.2) x = 0 →
      c*Real.sqrt (signedBatchPrime S i.2 : ℝ) ≤ ‖planarEmbedding b e x‖)
    {len N : ℕ} (hshort : D*len < c*Real.sqrt (signedBatchPrime S i.2 : ℝ))
    (hLN : len ≤ N) (herr : (len : ℝ)/(N+1) ≤ (τ/(signedBatchPrime S i.2 : ℝ))/2)
    (a : ℕ) (x : ZMod (signedBatchPrime S i.2))
    (hx : x ∉ (R.then (smoothingKernel N)).passingException data S hS z a i τ) :
    (len : ℝ)*(τ/(signedBatchPrime S i.2 : ℝ))/2 ≤
      ((R.then (smoothingKernel N)).packageLaw b e z hD hs a len).prob
        (fun v => WalkPackage.Hits (data.phi (signedBatchPrime S i.2) (i.1 i.2)) v x) := by
  have hfloor := (R.then (smoothingKernel N)).not_mem_passingException data S hS z a i τ x hx
  have hf : τ/(signedBatchPrime S i.2 : ℝ) ≤
      ((R.law a).joint (fun _ => FinLaw.uniform (Fin (N+1)))).prob
      (fun v => data.phi (signedBatchPrime S i.2) (i.1 i.2)
        (z (a+v.1.val+v.2.val)-z a) = -x) := by
    change _ ≤ (((R.law a).joint (fun _ => FinLaw.uniform (Fin (N+1)))).map
      (addOffsets R.bound N)).prob
      (fun u => data.phi (signedBatchPrime S i.2) (i.1 i.2) (z (a+u.val)-z a) = -x) at hfloor
    rw [FinLaw.prob_map] at hfloor
    simpa only [addOffsets, Nat.add_assoc] using hfloor
  have hh := smoothed_signed_package_hit_lower (R.law a) data (signedBatchPrime S i.2)
    (i.1 i.2) b e z hz hD hs hcollision hshort hLN herr a (fun u => a+u.val) (-x) hf
  rw [packageLaw, FinLaw.prob_map]
  simp only [WalkPackage.Hits, packageSymbol_prefix]
  change _ ≤ (((R.law a).joint (fun _ => FinLaw.uniform (Fin (N+1)))).map
    (addOffsets R.bound N)).prob
    (fun u => ∃ l : Fin len,
      data.phi (signedBatchPrime S i.2) (i.1 i.2) (z (a+u.val+l.val)-z a) = -x)
  rw [FinLaw.prob_map]
  simpa only [addOffsets, Nat.add_assoc] using hh

/-- The actual good event used by posterior coverage, constructed from the
actual package exception cardinality. -/
def ForwardKernel.passingGood {Ω : Type*} (K : ForwardKernel)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ q ∈ S, q ∈ data.primes)
    (z : ℕ → L) (a : Ω → ℕ) (τ : ℝ) (u : BatchSignedIndex S → ℝ)
    (i : BatchSignedIndex S) (ω : Ω) : Prop :=
  ((K.passingException data S hS z (a ω) i τ).card : ℝ) < u i

/-- Averaged bad-event probabilities are derived from high actual endpoint
point entropy at every actual starting time, with an explicit threshold scale. -/
theorem ForwardKernel.passingGood_bad_mean {Ω : Type*} [Fintype Ω]
    (K : ForwardKernel) (data : SignedResidueData L) (S : Finset ℕ) (hne : S.Nonempty)
    (hS : ∀ q ∈ S, q ∈ data.primes) (p : FinLaw Ω) (a : Ω → ℕ) (z : ℕ → L)
    {m : ℕ} (hm : 0 < m) (hmk : m ≤ S.card) {ε τ c : ℝ}
    (u : BatchSignedIndex S → ℝ) (hτ : τ ≤ 3/8) (hc : 0 < c)
    (hu : ∀ i, 8*c*(signedBatchPrime S i.2 : ℝ) ≤ u i)
    (hH : ∀ ω, (1-ε)*(m : ℝ)*batchMeanLog S ≤
      signedPointEntropy data S (K.law (a ω)) (fun t => z (a ω+t.val)) m) :
    (𝔼 i : BatchSignedIndex S,
      p.prob (fun ω => ¬K.passingGood data S hS z a τ u i ω)) ≤ ε*batchMeanLog S/c := by
  let _ : Nonempty (BatchSignedIndex S) := ⟨(fun _ => true, ⟨0,hne.card_pos⟩)⟩
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
      (K.coverage_base data S hne hS z (a ω) hm hmk u hτ hc hu (hH ω)) (p.nonneg ω))
  simpa only [← Finset.sum_mul, p.sum_one, one_mul] using hs

/-- A concrete finite residue-batch extension for the actual smoothed forward
kernel. Exceptional sets, good events, package survival, hit floors and the
averaged bad bound are all constructed and proved above. The remaining inputs
are actual point-entropy lower bounds, actual collision separation, the true
bounded injective avoiding walk, and explicit numerical sampling/rate guards. -/
theorem exists_smoothed_walk_residue_batch_extension {Ω : Type*} [Fintype Ω]
    (data : SignedResidueData L) (S : Finset ℕ) (hne : S.Nonempty)
    (hS : ∀ q ∈ S, q ∈ data.primes) (F : Finset (ℕ × Bool))
    (hF : ∀ i ∈ F, i.1 ∈ data.primes) (p : FinLaw Ω) (a : Ω → ℕ)
    (R : ForwardKernel) (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (z : ℕ → L) (hz : Function.Injective z) {D γ : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D)
    (havoid : ∀ t, z t ∈ avoiding data S)
    (hcollision : ∀ q ∈ data.primes, ∀ σ : Bool, ∀ x : L, x ≠ 0 → data.phi q σ x = 0 →
      γ*Real.sqrt (q : ℝ) ≤ ‖planarEmbedding b e x‖)
    {N len k m : ℕ} (hk : k ≤ S.card) (hm : 0 < m) (hmk : m ≤ S.card)
    (hlen : 0 < len) (hLN : len ≤ N)
    (hshort : ∀ i : BatchSignedIndex S, D*len < γ*Real.sqrt (signedBatchPrime S i.2 : ℝ))
    {τ c ε A δ r : ℝ} (hτ : 0 ≤ τ) (hτ1 : τ ≤ 3/8) (hc : 0 < c) (hA : 0 ≤ A)
    (u : BatchSignedIndex S → ℝ) (hu : ∀ i, 8*c*(signedBatchPrime S i.2 : ℝ) ≤ u i)
    (herr : ∀ i : BatchSignedIndex S,
      (len : ℝ)/(N+1) ≤ (τ/(signedBatchPrime S i.2 : ℝ))/2)
    (hEndpoint : ∀ ω, (1-ε)*(m : ℝ)*batchMeanLog S ≤
      signedPointEntropy data S ((R.then (smoothingKernel N)).law (a ω))
        (fun t => z (a ω+t.val)) m)
    (hH : (1-δ)*(k : ℝ)*batchMeanLog S ≤
      signedPointEntropy data S p (fun ω => z (a ω)) k)
    (n : ℕ) (hn : 0 < n)
    (hnum : ∀ i : BatchSignedIndex S, Real.log (4*u i + (signedBatchPrime S i.2 : ℝ)*
      Real.exp (-(n : ℝ)*(((len : ℝ)*(τ/(signedBatchPrime S i.2 : ℝ))/2)/4))) ≤
        Real.log (signedBatchPrime S i.2)-A)
    (hrate : (n : ℝ)*((len : ℝ)*r +
      2*Real.log (wordStepBall b e (D*(R.then (smoothingKernel N)).bound)).card) ≤
      (k : ℝ)*(A*(1-2*(ε*batchMeanLog S/c))-δ*batchMeanLog S)-
        F.sum (fun i => Real.log i.1)) :
    ∃ G : Finset (ℕ × Bool), F ⊆ G ∧ (∀ i ∈ G, i.1 ∈ data.primes) ∧ (G \ F).card ≤ k ∧
      G.sum (fun i => Real.log i.1) ≤ F.sum (fun i => Real.log i.1) +
        2*S.sum (fun q => Real.log q) ∧
      r ≤ (p.joint (fun ω => (R.then (smoothingKernel N)).law (a ω))).cIf
        (fun v => residueFamilyHom data G (z (a v.1+v.2.val)))
        (fun v => incrementWord z len (a v.1+v.2.val))
        (fun v => residueFamilyHom data F (z (a v.1+v.2.val))) / len := by
  let K := R.then (smoothingKernel N)
  let Good := K.passingGood data S hS z a τ u
  let exception := fun (i : BatchSignedIndex S) ω => K.passingException data S hS z (a ω) i τ
  apply exists_walk_residue_batch_extension data S hne hS F hF p a K z b e hD hs havoid
    hk hlen Good exception u (fun i => (len : ℝ)*(τ/(signedBatchPrime S i.2 : ℝ))/2)
    n hn hA
  · intro i
    have hp : (0 : ℝ) ≤ signedBatchPrime S i.2 := Nat.cast_nonneg _
    exact (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hc.le) hp).trans (hu i)
  · intro i
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hτ (Nat.cast_nonneg _)))
      (by norm_num)
  · intro i ω hg
    exact hg.le
  · intro i ω _ x hx
    exact R.smoothed_package_floor data S hS i b e z hz hD hs
      (hcollision _ (hS _ (signedBatchPrime_mem S i.2)) (i.1 i.2))
      (hshort i) hLN (herr i) (a ω) x hx
  · exact hnum
  · exact hH
  · exact K.passingGood_bad_mean data S hne hS p a z hm hmk u hτ1 hc hu hEndpoint
  · exact hrate

end Entry002
