import Entry002.GenericFreshCoverage
import Entry002.GenericWords
import Entry002.GenericWalkPackage

/-!
# Actual signed batch information selection

Finite-law selection infrastructure adapted from OpenAI family028,
GaussianMoat/WalkPackage.lean and InformationTelescope.lean, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (https://github.com/openai/math),
Apache-2.0; see ../../upstream-028/LICENSE. Gaussian package geometry is
replaced by explicit actual residue-hit and survival hypotheses. Entropy and
information inequalities are derived, never supplied as replacement axioms.
Exact spans and adaptations are recorded in the accompanying provenance log.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
universe uOmega uAlpha uIota uAlphaPrime uBeta uBetaPrime uGamma uGammaPrime
namespace Entry002
open OAI.GaussianMoat
lemma batch_cIf_congr_fibers {Ω : Type uOmega} {α : Type uAlpha} {α' : Type uAlphaPrime} {β : Type uBeta} {β' : Type uBetaPrime} {γ : Type uGamma} {γ' : Type uGammaPrime} [Fintype Ω]
    (p : FinLaw Ω) (X : Ω → α) (X' : Ω → α')
    (Y : Ω → β) (Y' : Ω → β') (O : Ω → γ) (O' : Ω → γ')
    (hX : ∀ ω ν, X ω=X ν ↔ X' ω=X' ν)
    (hY : ∀ ω ν, Y ω=Y ν ↔ Y' ω=Y' ν)
    (hO : ∀ ω ν, O ω=O ν ↔ O' ω=O' ν) :
    p.cIf X Y O=p.cIf X' Y' O' := by
  unfold FinLaw.cIf
  rw [p.cHf_congr_fibers X X' O O' hX hO]
  congr 1
  apply p.cHf_congr_fibers _ _ _ _ hX
  intro ω ν
  simp only [Prod.mk.injEq,hO,hY]
end Entry002

namespace Entry002
open OAI.GaussianMoat
open scoped BigOperators Classical

lemma perm_expect_uniform {ι : Type uIota} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (f : ι → ℝ) (i : ι) :
    (𝔼 π : Equiv.Perm ι, f (π i))=𝔼 j, f j := by
  have hf (π : Equiv.Perm ι) : (𝔼 j, f (π j))=𝔼 j, f j := by
    rw [Fintype.expect_eq_sum_div_card,Fintype.expect_eq_sum_div_card,Equiv.sum_comp π]
  calc
    _ = 𝔼 j : ι, 𝔼 π : Equiv.Perm ι, f (π j) := by
      simp_rw [← perm_expect_exchange f i]
      rw [Fintype.expect_const]
    _ = 𝔼 π : Equiv.Perm ι, 𝔼 j, f (π j) := Finset.expect_comm _ _ _
    _ = _ := by simp_rw [hf]; rw [Fintype.expect_const]

lemma selected_prefix_fibers {Ω : Type uOmega} {α : Type uAlpha} {k b : ℕ} (hb : b≤k)
    (X : Ω → Fin k → α) (π : Equiv.Perm (Fin k)) (ω ν : Ω) :
    (fun j : Fin b => X ω (π ⟨j.val,lt_of_lt_of_le j.isLt hb⟩))=
      (fun j : Fin b => X ν (π ⟨j.val,lt_of_lt_of_le j.isLt hb⟩)) ↔
    FinLaw.prefixVar X π b ω=FinLaw.prefixVar X π b ν := by
  constructor
  · intro h
    funext i
    by_cases hi : i.val<b
    · have hh := congrFun h ⟨i.val,hi⟩
      simpa only [FinLaw.prefixVar,hi,ite_true,Option.some.injEq] using hh
    · simp only [FinLaw.prefixVar,hi,ite_false]
  · intro h
    funext j
    have hh := congrFun h ⟨j.val,lt_of_lt_of_le j.isLt hb⟩
    simpa only [FinLaw.prefixVar,j.isLt,ite_true,Option.some.injEq] using hh

theorem greedy_finite_selection {α : Type*} (A : ℕ → Finset α)
    (hA : ∀ j, A j⊆A (j+1)) (n : ℕ)
    (R : ℕ → Finset α → Finset α → Prop)
    (hstep : ∀ j≤n, ∀ F⊆A j, ∃ G, F⊆G ∧ G⊆A (j+1) ∧ R j F G) :
    ∃ F : ℕ → Finset α,
      (∀ j, F j⊆A j) ∧ (∀ j, F j⊆F (j+1)) ∧ (∀ j≤n, R j (F j) (F (j+1))) := by
  have step (j : ℕ) (F : {F : Finset α // F⊆A j}) :
      ∃ G : {G : Finset α // G⊆A (j+1)}, F.val⊆G.val ∧ (j≤n → R j F.val G.val) := by
    by_cases hj : j≤n
    · obtain ⟨G,hFG,hG,hR⟩ := hstep j hj F.val F.property
      exact ⟨⟨G,hG⟩,hFG,fun _ => hR⟩
    · exact ⟨⟨F.val,F.property.trans (hA j)⟩,Finset.Subset.refl _,fun h => (hj h).elim⟩
  let f (j : ℕ) (F : {F : Finset α // F⊆A j}) := (step j F).choose
  let F : (j : ℕ) → {F : Finset α // F⊆A j} :=
    @Nat.rec (fun j => {F : Finset α // F⊆A j}) ⟨∅,Finset.empty_subset _⟩ f
  refine ⟨fun j => (F j).val,fun j => (F j).property,?_,?_⟩
  · intro j
    exact (step j (F j)).choose_spec.1
  · intro j hj
    exact (step j (F j)).choose_spec.2 hj



variable {L Ω Γ O : Type*} [AddCommGroup L] [Fintype Ω] [Fintype Γ] [Fintype O]

abbrev BatchSignedIndex (S : Finset ℕ) := (Fin S.card → Bool) × Fin S.card

noncomputable def batchSelectedIndex (S : Finset ℕ) {b : ℕ} (hb : b ≤ S.card)
    (σ : Fin S.card → Bool) (π : Equiv.Perm (Fin S.card)) (j : Fin b) :
    BatchSignedIndex S := (σ, π ⟨j.val, lt_of_lt_of_le j.isLt hb⟩)

noncomputable def batchMeanLog (S : Finset ℕ) : ℝ :=
  𝔼 i : Fin S.card, Real.log (signedBatchPrime S i)

noncomputable def selectedResidueCode (data : SignedResidueData L) (S : Finset ℕ)
    {b : ℕ} (hb : b ≤ S.card) (σ : Fin S.card → Bool)
    (π : Equiv.Perm (Fin S.card)) (x : L) : Fin b → ℕ :=
  fun j => signedResidueVector data S σ x (π ⟨j.val, lt_of_lt_of_le j.isLt hb⟩)

lemma batch_selected_sum_average (S : Finset ℕ) (hne : S.Nonempty)
    {b : ℕ} (hb : b ≤ S.card) (f : BatchSignedIndex S → ℝ) :
    (𝔼 σ : Fin S.card → Bool, 𝔼 π : Equiv.Perm (Fin S.card),
      ∑ j : Fin b, f (batchSelectedIndex S hb σ π j)) =
    (b : ℝ) * (𝔼 i : BatchSignedIndex S, f i) := by
  have : Nonempty (Fin S.card) := ⟨⟨0, hne.card_pos⟩⟩
  have hf (σ : Fin S.card → Bool) (j : Fin b) :
      (𝔼 π : Equiv.Perm (Fin S.card), f (batchSelectedIndex S hb σ π j)) =
        𝔼 i : Fin S.card, f (σ, i) := by
    exact perm_expect_uniform (fun i => f (σ, i)) ⟨j.val, lt_of_lt_of_le j.isLt hb⟩
  simp only [Finset.expect_sum_comm, hf, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_expect, ← Finset.univ_product_univ,
    Finset.expect_product]

lemma batch_selected_entropy_average (data : SignedResidueData L) (S : Finset ℕ)
    (p : FinLaw Ω) (X : Ω → L) {b : ℕ} (hb : b ≤ S.card) :
    (𝔼 σ : Fin S.card → Bool, 𝔼 π : Equiv.Perm (Fin S.card),
      p.Hf (fun ω => selectedResidueCode data S hb σ π (X ω))) =
    signedPointEntropy data S p X b := by
  have h (σ : Fin S.card → Bool) (π : Equiv.Perm (Fin S.card)) :=
    p.Hf_eq_of_fibers _ _ (selected_prefix_fibers hb
      (fun ω => signedResidueVector data S σ (X ω)) π)
  change (𝔼 σ : Fin S.card → Bool, 𝔼 π : Equiv.Perm (Fin S.card),
    p.Hf (fun ω (j : Fin b) => signedResidueVector data S σ (X ω)
      (π ⟨j.val, lt_of_lt_of_le j.isLt hb⟩))) = _
  simp only [h, signedPointEntropy, FinLaw.signedEntropy, FinLaw.orderedEntropy]

lemma batch_selected_log_average (S : Finset ℕ) (hne : S.Nonempty)
    {b : ℕ} (hb : b ≤ S.card) :
    (𝔼 σ : Fin S.card → Bool, 𝔼 π : Equiv.Perm (Fin S.card),
      ∑ j : Fin b, Real.log (signedBatchPrime S (batchSelectedIndex S hb σ π j).2)) =
    (b : ℝ) * batchMeanLog S := by
  rw [batch_selected_sum_average S hne hb (fun i => Real.log (signedBatchPrime S i.2))]
  simp only [← Finset.univ_product_univ, Finset.expect_product, Fintype.expect_const,
    batchMeanLog]

/-- One selected batch's information comes from its actual conditional entropy
and the posterior passing-list proof. -/
theorem selected_batch_posterior_information (data : SignedResidueData L)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q ∈ data.primes) (p : FinLaw Ω)
    (old : Ω → O) (X : Ω → L) (q : Ω → FinLaw Γ) {b : ℕ} (hb : b ≤ S.card)
    (σ : Fin S.card → Bool) (π : Equiv.Perm (Fin S.card))
    (hit : (i : BatchSignedIndex S) → Γ → ZMod (signedBatchPrime S i.2) → Prop)
    (Good : BatchSignedIndex S → Ω → Prop)
    (exception : (i : BatchSignedIndex S) → Ω → Finset (ZMod (signedBatchPrime S i.2)))
    (e c : BatchSignedIndex S → ℝ) {A : ℝ} (n : ℕ)
    (hA : 0 ≤ A) (he : ∀ i, 0 ≤ e i) (hc : ∀ i, 0 ≤ c i)
    (htrue : ∀ ω, p ω ≠ 0 → ∀ v, q ω v ≠ 0 → ∀ i,
      ¬hit i v (data.phi (signedBatchPrime S i.2) (i.1 i.2) (X ω)))
    (hE : ∀ i ω, Good i ω → ((exception i ω).card : ℝ) ≤ e i)
    (hhit : ∀ i ω, Good i ω → ∀ x ∉ exception i ω,
      c i ≤ (q ω).prob (fun v => hit i v x))
    (hnum : ∀ i, Real.log (4 * e i + (signedBatchPrime S i.2 : ℝ) *
      Real.exp (-(n : ℝ) * (c i / 4))) ≤ Real.log (signedBatchPrime S i.2) - A) :
    A * ((b : ℝ) - 2 * ∑ j : Fin b,
      p.prob (fun ω => ¬Good (batchSelectedIndex S hb σ π j) ω)) -
      ((∑ j : Fin b, Real.log (signedBatchPrime S (batchSelectedIndex S hb σ π j).2)) -
        p.cHf (fun ω => selectedResidueCode data S hb σ π (X ω)) old) ≤
    (n : ℝ) * (p.joint q).cIf
      (fun v => selectedResidueCode data S hb σ π (X v.1)) Prod.snd (fun v => old v.1) := by
  let I := batchSelectedIndex S hb σ π
  let (j : Fin b) : NeZero (signedBatchPrime S (I j).2) :=
    ⟨(data.prime_mem _ (hS _ (signedBatchPrime_mem S (I j).2))).ne_zero⟩
  let G := fun j : Fin b => ZMod (signedBatchPrime S (I j).2)
  let V := fun ω (j : Fin b) => data.phi (signedBatchPrime S (I j).2) ((I j).1 (I j).2) (X ω)
  have hf (ω ν : Ω) : V ω = V ν ↔
      selectedResidueCode data S hb σ π (X ω) = selectedResidueCode data S hb σ π (X ν) := by
    constructor
    · intro h; funext j; exact congrArg ZMod.val (congrFun h j)
    · intro h; funext j; exact ZMod.val_injective _ (congrFun h j)
  let H := (∑ j, Real.log (signedBatchPrime S (I j).2)) - p.cHf V old
  have hh := FinLaw.posterior_passing_information_lower G p old V q
    (fun j => hit (I j)) (fun j => Good (I j)) (fun j => exception (I j))
    (fun j => e (I j)) (fun j => c (I j)) n hA (fun j => he _) (fun j => hc _)
    (fun ω hω v hv j => htrue ω hω v hv (I j))
    (fun j => hE _) (fun j => hhit _)
    (show (∑ j, Real.log (Fintype.card (G j))) - H ≤ p.cHf V old by
      simp only [G, ZMod.card, H]; linarith)
    le_rfl (by intro j; simpa only [G, ZMod.card] using hnum (I j))
  have heH := p.cHf_congr_fibers V
    (fun ω => selectedResidueCode data S hb σ π (X ω)) old old hf (fun _ _ => Iff.rfl)
  have heI := batch_cIf_congr_fibers (p.joint q) (V ∘ Prod.fst)
    (fun v => selectedResidueCode data S hb σ π (X v.1)) Prod.snd Prod.snd
    (old ∘ Prod.fst) (old ∘ Prod.fst) (fun v w => hf v.1 w.1)
    (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl)
  change (p.joint q).cIf (fun v => V v.1) Prod.snd (fun v => old v.1) = _ at heI
  rw [heI] at hh
  simpa only [Fintype.card_fin, H, heH, I, Function.comp_def] using hh


/-- Actual point entropy and posterior hit coverage force averaged batch
information; the deficit is derived from the genuine conditional entropies. -/
theorem averaged_signed_batch_information (data : SignedResidueData L)
    (S : Finset ℕ) (hne : S.Nonempty) (hS : ∀ q ∈ S, q ∈ data.primes) (p : FinLaw Ω)
    (old : Ω → O) (X : Ω → L) (q : Ω → FinLaw Γ) {b : ℕ} (hb : b ≤ S.card)
    (hit : (i : BatchSignedIndex S) → Γ → ZMod (signedBatchPrime S i.2) → Prop)
    (Good : BatchSignedIndex S → Ω → Prop)
    (exception : (i : BatchSignedIndex S) → Ω → Finset (ZMod (signedBatchPrime S i.2)))
    (e c : BatchSignedIndex S → ℝ) {A η δ E : ℝ} (n : ℕ)
    (hA : 0 ≤ A) (he : ∀ i, 0 ≤ e i) (hc : ∀ i, 0 ≤ c i)
    (htrue : ∀ ω, p ω ≠ 0 → ∀ v, q ω v ≠ 0 → ∀ i,
      ¬hit i v (data.phi (signedBatchPrime S i.2) (i.1 i.2) (X ω)))
    (hE : ∀ i ω, Good i ω → ((exception i ω).card : ℝ) ≤ e i)
    (hhit : ∀ i ω, Good i ω → ∀ x ∉ exception i ω,
      c i ≤ (q ω).prob (fun v => hit i v x))
    (hnum : ∀ i, Real.log (4 * e i + (signedBatchPrime S i.2 : ℝ) *
      Real.exp (-(n : ℝ) * (c i / 4))) ≤ Real.log (signedBatchPrime S i.2) - A)
    (hH : (1-δ) * (b : ℝ) * batchMeanLog S ≤ signedPointEntropy data S p X b)
    (hO : p.Hf old ≤ E)
    (hBad : (𝔼 i : BatchSignedIndex S, p.prob (fun ω => ¬Good i ω)) ≤ η) :
    (b : ℝ) * (A * (1-2*η)-δ * batchMeanLog S)-E ≤ (n : ℝ) *
      (𝔼 σ : Fin S.card → Bool, 𝔼 π : Equiv.Perm (Fin S.card),
        (p.joint q).cIf (fun v => selectedResidueCode data S hb σ π (X v.1))
          Prod.snd (fun v => old v.1)) := by
  let V := fun (σ : Fin S.card → Bool) (π : Equiv.Perm (Fin S.card))
    (ω : Ω) => selectedResidueCode data S hb σ π (X ω)
  let Bad := fun i : BatchSignedIndex S => p.prob (fun ω => ¬Good i ω)
  have hi (σ : Fin S.card → Bool) (π : Equiv.Perm (Fin S.card)) :=
    selected_batch_posterior_information data S hS p old X q hb σ π hit Good
      exception e c n hA he hc htrue hE hhit hnum
  have hav := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ => hi σ π))
  simp only [Finset.expect_sub_distrib, ← Finset.mul_expect, Fintype.expect_const,
    Finset.expect_sum_comm] at hav
  have hx (σ : Fin S.card → Bool) (π : Equiv.Perm (Fin S.card)) :
      p.Hf (V σ π)-E ≤ p.cHf (V σ π) old := by
    have h := p.Hf_pair_ge_snd old (V σ π)
    rw [p.Hf_pair_comm] at h
    unfold FinLaw.cHf
    linarith only [h, hO]
  have hxa := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ => hx σ π))
  simp only [Finset.expect_sub_distrib, Fintype.expect_const] at hxa
  have hxe := batch_selected_entropy_average data S p X hb
  change (𝔼 σ, 𝔼 π, p.Hf (V σ π)) = _ at hxe
  rw [hxe] at hxa
  have hlog := batch_selected_log_average S hne hb
  have hbad := batch_selected_sum_average S hne hb Bad
  have hbR : 0 ≤ (b : ℝ) := Nat.cast_nonneg _
  have hbadle : (b : ℝ) * (𝔼 i, Bad i) ≤ b * η :=
    mul_le_mul_of_nonneg_left hBad hbR
  simp only [Finset.expect_sum_comm] at hlog hbad
  rw [hlog, hbad] at hav
  have hprod := mul_le_mul_of_nonneg_left hbadle hA
  nlinarith only [hav, hxa, hH, hprod]

/-- A genuine batch selection with the requested lower information rate. -/
theorem exists_signed_batch_information (data : SignedResidueData L)
    (S : Finset ℕ) (hne : S.Nonempty) (hS : ∀ q ∈ S, q ∈ data.primes) (p : FinLaw Ω)
    (old : Ω → O) (X : Ω → L) (q : Ω → FinLaw Γ) {b : ℕ} (hb : b ≤ S.card)
    (hit : (i : BatchSignedIndex S) → Γ → ZMod (signedBatchPrime S i.2) → Prop)
    (Good : BatchSignedIndex S → Ω → Prop)
    (exception : (i : BatchSignedIndex S) → Ω → Finset (ZMod (signedBatchPrime S i.2)))
    (e c : BatchSignedIndex S → ℝ) {A η δ E : ℝ} (n : ℕ)
    (hA : 0 ≤ A) (he : ∀ i, 0 ≤ e i) (hc : ∀ i, 0 ≤ c i)
    (htrue : ∀ ω, p ω ≠ 0 → ∀ v, q ω v ≠ 0 → ∀ i,
      ¬hit i v (data.phi (signedBatchPrime S i.2) (i.1 i.2) (X ω)))
    (hE : ∀ i ω, Good i ω → ((exception i ω).card : ℝ) ≤ e i)
    (hhit : ∀ i ω, Good i ω → ∀ x ∉ exception i ω,
      c i ≤ (q ω).prob (fun v => hit i v x))
    (hnum : ∀ i, Real.log (4 * e i + (signedBatchPrime S i.2 : ℝ) *
      Real.exp (-(n : ℝ) * (c i / 4))) ≤ Real.log (signedBatchPrime S i.2) - A)
    (hH : (1-δ) * (b : ℝ) * batchMeanLog S ≤ signedPointEntropy data S p X b)
    (hO : p.Hf old ≤ E)
    (hBad : (𝔼 i : BatchSignedIndex S, p.prob (fun ω => ¬Good i ω)) ≤ η)
    {len : ℕ} (hlen : 0 < len) (hn : 0 < n) {r : ℝ}
    (hrate : (n : ℝ) * (len : ℝ) * r ≤
      (b : ℝ) * (A * (1-2*η)-δ * batchMeanLog S)-E) :
    ∃ σ : Fin S.card → Bool, ∃ π : Equiv.Perm (Fin S.card),
      r ≤ (p.joint q).cIf
        (fun v => selectedResidueCode data S hb σ π (X v.1))
        Prod.snd (fun v => old v.1) / len := by
  have hlower := averaged_signed_batch_information data S hne hS p old X q hb
    hit Good exception e c n hA he hc htrue hE hhit hnum hH hO hBad
  let Info := fun (σ : Fin S.card → Bool) (π : Equiv.Perm (Fin S.card)) =>
    (p.joint q).cIf (fun v => selectedResidueCode data S hb σ π (X v.1))
      Prod.snd (fun v => old v.1)
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hav : (len : ℝ) * r ≤ 𝔼 σ, 𝔼 π, Info σ π := by
    apply (mul_le_mul_iff_right₀ hnR).mp
    simpa only [mul_assoc] using hrate.trans hlower
  obtain ⟨σ, _, hσ⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hav
  obtain ⟨π, _, hπ⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hσ
  refine ⟨σ, π, ?_⟩
  exact (le_div_iff₀ (show (0 : ℝ) < len by exact_mod_cast hlen)).mpr
    (by simpa only [mul_comm] using hπ)


/-- The actual finite signed-prime labels chosen by a permutation prefix. -/
noncomputable def selectedBatchLabel (S : Finset ℕ) {b : ℕ} (hb : b ≤ S.card)
    (σ : Fin S.card → Bool) (π : Equiv.Perm (Fin S.card)) (j : Fin b) : ℕ × Bool :=
  (signedBatchPrime S (π ⟨j.val, lt_of_lt_of_le j.isLt hb⟩),
    σ (π ⟨j.val, lt_of_lt_of_le j.isLt hb⟩))

noncomputable def selectedBatchLabels (S : Finset ℕ) {b : ℕ} (hb : b ≤ S.card)
    (σ : Fin S.card → Bool) (π : Equiv.Perm (Fin S.card)) : Finset (ℕ × Bool) :=
  Finset.univ.image (selectedBatchLabel S hb σ π)

lemma selectedBatchLabels_card_le (S : Finset ℕ) {b : ℕ} (hb : b ≤ S.card)
    (σ : Fin S.card → Bool) (π : Equiv.Perm (Fin S.card)) :
    (selectedBatchLabels S hb σ π).card ≤ b := by
  exact (Finset.card_image_le).trans_eq (Finset.card_univ.trans (Fintype.card_fin b))

lemma selectedBatchLabels_prime_mem (data : SignedResidueData L) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q ∈ data.primes) {b : ℕ} (hb : b ≤ S.card)
    (σ : Fin S.card → Bool) (π : Equiv.Perm (Fin S.card)) :
    ∀ i ∈ selectedBatchLabels S hb σ π, i.1 ∈ data.primes := by
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  exact hS _ (signedBatchPrime_mem S _)

omit [Fintype Γ] in
/-- Adding the selected finite labels spends precisely their conditional
information; existing coordinates do not count as new information. -/
theorem selectedBatchLabels_union_information (data : SignedResidueData L)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q ∈ data.primes) (F : Finset (ℕ × Bool))
    {b : ℕ} (hb : b ≤ S.card) (σ : Fin S.card → Bool)
    (π : Equiv.Perm (Fin S.card)) (p : FinLaw Ω) (X : Ω → L) (Y : Ω → Γ) :
    p.cIf (fun ω => residueFamilyHom data (F ∪ selectedBatchLabels S hb σ π) (X ω)) Y
      (fun ω => residueFamilyHom data F (X ω)) =
    p.cIf (fun ω => selectedResidueCode data S hb σ π (X ω)) Y
      (fun ω => residueFamilyHom data F (X ω)) := by
  rw [p.cIf_comm, p.cIf_comm (fun ω => selectedResidueCode data S hb σ π (X ω))]
  unfold FinLaw.cIf
  congr 1
  apply p.cHf_congr_fibers
  · intro ω ν; rfl
  · intro ω ν
    simp only [Prod.mk.injEq]
    constructor
    · rintro ⟨hO, hU⟩
      refine ⟨hO, funext fun j => ?_⟩
      have hm : selectedBatchLabel S hb σ π j ∈ F ∪ selectedBatchLabels S hb σ π :=
        Finset.mem_union_right F (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
      exact congrArg ZMod.val (congrFun hU ⟨selectedBatchLabel S hb σ π j, hm⟩)
    · rintro ⟨hO, hU⟩
      refine ⟨hO, funext fun g => ?_⟩
      rcases Finset.mem_union.mp g.property with hg | hg
      · exact congrFun hO ⟨g.val, hg⟩
      · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hg
        have hp := hS _ (signedBatchPrime_mem S (π ⟨j.val, lt_of_lt_of_le j.isLt hb⟩))
        have hpG : g.val.1 ∈ data.primes := (congrArg Prod.fst hj) ▸ hp
        let _ : NeZero g.val.1 := ⟨(data.prime_mem _ hpG).ne_zero⟩
        apply ZMod.val_injective g.val.1
        change ((data.phi g.val.1 g.val.2) (X ω)).val =
          ((data.phi g.val.1 g.val.2) (X ν)).val
        rw [← hj]
        exact congrFun hU j

omit [Fintype Ω] in
/-- Residue observations at two points differ by the actual additive shift;
conditioning on that shift makes their fibers identical. -/
lemma batch_additive_observation_shift {R : Type*} [AddCommGroup R]
    (ρ : L →+ R) (X Y : Ω → L) (ω ν : Ω) :
    (ρ (X ω), Y ω-X ω) = (ρ (X ν), Y ν-X ν) ↔
      (ρ (Y ω), Y ω-X ω) = (ρ (Y ν), Y ν-X ν) := by
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨hx, hs⟩
    refine ⟨?_, hs⟩
    have hω : Y ω = X ω + (Y ω-X ω) := by abel
    have hν : Y ν = X ν + (Y ν-X ν) := by abel
    rw [hω, hν, map_add, map_add, hx, hs]
  · rintro ⟨hy, hs⟩
    refine ⟨?_, hs⟩
    calc
      ρ (X ω) = ρ (Y ω) - ρ (Y ω-X ω) := by rw [map_sub]; abel
      _ = ρ (Y ν) - ρ (Y ν-X ν) := by rw [hy, hs]
      _ = ρ (X ν) := by rw [map_sub]; abel

/-- Generic package information transport with the honest actual displacement
entropy cost. Both old and extended observations are actual residue families. -/
theorem residueFamily_package_information_transport {Β : Type*}
    (data : SignedResidueData L) (F G : Finset (ℕ × Bool))
    (p : FinLaw Ω) (X Y : Ω → L) (W : Ω → Β) :
    p.cIf (fun ω => residueFamilyHom data G (X ω))
      (fun ω => (Y ω-X ω, W ω)) (fun ω => residueFamilyHom data F (X ω)) ≤
    p.cIf (fun ω => residueFamilyHom data G (Y ω)) W
      (fun ω => residueFamilyHom data F (Y ω)) + 2 * p.Hf (fun ω => Y ω-X ω) := by
  apply p.cIf_transport _ _ _ _ W (fun ω => Y ω-X ω)
  · exact batch_additive_observation_shift (residueFamilyHom data F) X Y
  · intro ω ν
    have hf := batch_additive_observation_shift (residueFamilyHom data F) X Y ω ν
    have hg := batch_additive_observation_shift (residueFamilyHom data G) X Y ω ν
    simp only [Prod.mk.injEq] at hf hg ⊢
    tauto



lemma selectedBatchLabels_log_weight_le (data : SignedResidueData L) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q ∈ data.primes) {b : ℕ} (hb : b ≤ S.card)
    (σ : Fin S.card → Bool) (π : Equiv.Perm (Fin S.card)) :
    (selectedBatchLabels S hb σ π).sum (fun i => Real.log i.1) ≤
      2 * S.sum (fun q => Real.log q) := by
  have hsub : selectedBatchLabels S hb σ π ⊆ S ×ˢ (Finset.univ : Finset Bool) := by
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_product.mpr ⟨signedBatchPrime_mem S _, Finset.mem_univ _⟩
  have hh : (selectedBatchLabels S hb σ π).sum (fun i => Real.log i.1) ≤
      (S ×ˢ (Finset.univ : Finset Bool)).sum (fun i => Real.log i.1) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsub
    intro i hi _
    exact Real.log_nonneg (by exact_mod_cast
      (data.prime_mem _ (hS i.1 (Finset.mem_product.mp hi).1)).one_le)
  apply hh.trans_eq
  simp only [Finset.sum_product, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
    nsmul_eq_mul, ← Finset.mul_sum, Nat.cast_ofNat]

lemma residueLabels_union_log_weight_le (data : SignedResidueData L)
    (F B : Finset (ℕ × Bool)) (hB : ∀ i ∈ B, i.1 ∈ data.primes) :
    (F ∪ B).sum (fun i => Real.log i.1) ≤
      F.sum (fun i => Real.log i.1) + B.sum (fun i => Real.log i.1) := by
  have hh := Finset.sum_union_inter (f := fun i : ℕ × Bool => Real.log i.1) (s₁ := F) (s₂ := B)
  have hnonneg : 0 ≤ (F ∩ B).sum (fun i => Real.log i.1) := by
    apply Finset.sum_nonneg
    intro i hi
    exact Real.log_nonneg (by exact_mod_cast
      (data.prime_mem _ (hB i (Finset.mem_inter.mp hi).2)).one_le)
  linarith only [hh, hnonneg]

/-- The batch selection creates a genuine finite residue-family extension,
with at most `b` fresh labels and the exact old `sum(log p)` budget. -/
theorem exists_residueFamily_batch_extension (data : SignedResidueData L)
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
    ∃ G : Finset (ℕ × Bool), F ⊆ G ∧
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
  refine ⟨F ∪ B, Finset.subset_union_left, ?_, ?_, ?_, ?_⟩
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
theorem exists_walk_residue_batch_extension (data : SignedResidueData L)
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
    ∃ G : Finset (ℕ × Bool), F ⊆ G ∧
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
  obtain ⟨G, hFG, hG, hcard, hcost, hinfo⟩ := exists_residueFamily_batch_extension
    data S hne hS p F hF (fun ω => z (a ω))
    (fun ω => K.packageLaw basis embedding z hD hs (a ω) len) hb
    (fun i => WalkPackage.Hits (data.phi (signedBatchPrime S i.2) (i.1 i.2)))
    Good exception e c n hA he hc
    (fun ω _ v hv i => K.signed_package_true_survives data S z havoid
      (signedBatchPrime_mem S i.2) (i.1 i.2) basis embedding hD hs (a ω) len v hv)
    hE hhit hnum hH hBad hlen hn hrate'
  refine ⟨G, hFG, hG, hcard, hcost, ?_⟩
  have hpackage := K.package_information_transport p a (residueFamilyHom data G)
    (residueFamilyHom data F) basis embedding z hD hs len
  have hi := (div_le_div_iff_of_pos_right hlenR).mp hinfo
  apply (le_div_iff₀ hlenR).mpr
  dsimp only [C] at hi
  nlinarith only [hi, hpackage]

end Entry002
