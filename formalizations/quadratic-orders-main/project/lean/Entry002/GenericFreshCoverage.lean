import Entry002.GenericResidues
import Entry002.PosteriorCoverage

/-!
# Fresh information and posterior coverage for actual signed residues

All residue observations here are the maps supplied by `SignedResidueData`.
The finite-law arguments are generic versions of PointEnrichment and
PassingInformation from the pinned OpenAI family028 source. Coverage assumptions
refer to actual residue hits and actual exceptional residue sets.
Proof patterns are adapted from upstream-028/GaussianMoat/PointEnrichment.lean
lines 250–258 and 290–339; the posterior theorem applies the preserved generic
PassingInformation body in `PosteriorCoverage`. Pinned upstream commit:
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`; Apache-2.0.
-/

set_option maxHeartbeats 800000

namespace Entry002
open OAI.GaussianMoat
open scoped BigOperators Classical

variable {L Ω : Type*} [AddCommGroup L] [Fintype Ω]

/-- A fresh difference residue, conditioned on the two actual old prefixes. -/
noncomputable def signedFreshCoordinate (data : SignedResidueData L) (S : Finset ℕ)
    (p : FinLaw Ω) (X Y : Ω → L) (s : ℕ) (hs : s < S.card) : ℝ :=
  𝔼 σ : Fin S.card → Bool, 𝔼 π : Equiv.Perm (Fin S.card),
    p.cHf (fun ω => signedResidueVector data S σ (X ω - Y ω) (π ⟨s,hs⟩))
      (fun ω => (FinLaw.prefixVar (fun x => signedResidueVector data S σ (X x)) π s ω,
        FinLaw.prefixVar (fun x => signedResidueVector data S σ (Y x)) π s ω))

/-- Residue coding retains the additive difference relation exactly. -/
theorem signedResidueCode_sub (data : SignedResidueData L) {q : ℕ}
    (hq : q ∈ data.primes) (σ : Bool) {x x' y y' : L}
    (hx : (data.phi q σ x).val = (data.phi q σ x').val)
    (hy : (data.phi q σ y).val = (data.phi q σ y').val) :
    (data.phi q σ (x-y)).val = (data.phi q σ (x'-y')).val := by
  let _ : NeZero q := ⟨(data.prime_mem q hq).ne_zero⟩
  rw [(data.phi q σ).map_sub, (data.phi q σ).map_sub,
    ZMod.val_injective q hx, ZMod.val_injective q hy]

theorem signedFreshCoordinate_map {Κ : Type*} [Fintype Κ]
    (data : SignedResidueData L) (S : Finset ℕ) (p : FinLaw Ω) (f : Ω → Κ)
    (X Y : Κ → L) (s : ℕ) (hs : s < S.card) :
    signedFreshCoordinate data S (p.map f) X Y s hs =
      signedFreshCoordinate data S p (X ∘ f) (Y ∘ f) s hs := by
  unfold signedFreshCoordinate
  simp only [FinLaw.cHf_map, Function.comp_def]
  rfl

theorem signedFreshCoordinate_nonneg (data : SignedResidueData L) (S : Finset ℕ)
    (p : FinLaw Ω) (X Y : Ω → L) (s : ℕ) (hs : s < S.card) :
    0 ≤ signedFreshCoordinate data S p X Y s hs :=
  Finset.expect_nonneg (fun _ _ => Finset.expect_nonneg (fun _ _ => p.cHf_nonneg _ _))

/-- The exact prime logarithm is the cost of each fresh coordinate. -/
theorem signedFreshCoordinate_le_meanLog (data : SignedResidueData L) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q ∈ data.primes) (p : FinLaw Ω) (X Y : Ω → L)
    (s : ℕ) (hs : s < S.card) :
    signedFreshCoordinate data S p X Y s hs ≤
      𝔼 π : Equiv.Perm (Fin S.card), Real.log (signedBatchPrime S (π ⟨s,hs⟩)) := by
  have hpoint (σ : Fin S.card → Bool) (π : Equiv.Perm (Fin S.card)) :
      p.cHf (fun ω => signedResidueVector data S σ (X ω-Y ω) (π ⟨s,hs⟩))
        (fun ω => (FinLaw.prefixVar (fun x => signedResidueVector data S σ (X x)) π s ω,
          FinLaw.prefixVar (fun x => signedResidueVector data S σ (Y x)) π s ω)) ≤
        Real.log (signedBatchPrime S (π ⟨s,hs⟩)) := by
    apply (p.cHf_le_Hf _ _).trans
    exact signedResidueVector_coordinate_entropy_le data S hS σ p
      (fun ω => X ω-Y ω) (π ⟨s,hs⟩)
  have h := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ => hpoint σ π))
  simpa only [signedFreshCoordinate, Fintype.expect_const] using h

theorem signedFreshCoordinate_joint_ge {ι : Type*} [Fintype ι]
    (data : SignedResidueData L) (S : Finset ℕ) (p : FinLaw ι)
    (q : ι → FinLaw Ω) (X Y : ι → Ω → L) {s : ℕ} (hs : s < S.card) :
    (∑ i, p i * signedFreshCoordinate data S (q i) (X i) (Y i) s hs) ≤
      signedFreshCoordinate data S (p.joint q)
        (fun v => X v.1 v.2) (fun v => Y v.1 v.2) s hs := by
  have h := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ =>
      p.cHf_joint_ge q (fun i ω => signedResidueVector data S σ (X i ω-Y i ω) (π ⟨s,hs⟩))
        (fun i ω => (FinLaw.prefixVar (fun x => signedResidueVector data S σ (X i x)) π s ω,
          FinLaw.prefixVar (fun x => signedResidueVector data S σ (Y i x)) π s ω))))
  simpa only [signedFreshCoordinate, Finset.expect_sum_comm, Finset.mul_expect] using! h

/-- Actual signed point entropy obeys the generic enrichment accounting law;
all four fiber implications come from additivity of the actual residue maps. -/
theorem signedPointEntropy_enrichment_accounting (data : SignedResidueData L)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p ∈ data.primes) (p : FinLaw Ω) (X Y Z : Ω → L)
    {s r : ℕ} (hs : 0 < s) (hsr : s < r) (hr : r ≤ S.card) :
    (s : ℝ) * ((r-s : ℕ) * signedFreshCoordinate data S p X Y s (by omega) +
      signedPointEntropy data S p Z r - p.Hf (fun ω => X ω-Y ω) -
      p.Hf (fun ω => X ω-Z ω)) ≤
      (r : ℝ) * (signedPointEntropy data S p X s + signedPointEntropy data S p Y s) := by
  have h (σ : Fin S.card → Bool) := p.ordered_enrichment_accounting
    (fun ω => signedResidueVector data S σ (X ω))
    (fun ω => signedResidueVector data S σ (Y ω))
    (fun ω => signedResidueVector data S σ (Z ω))
    (fun ω => signedResidueVector data S σ (X ω-Y ω))
    (fun ω => X ω-Y ω) (fun ω => X ω-Z ω) hs hsr hr
    (by
      intro i ω ν hx hy
      exact signedResidueCode_sub data (hS _ (signedBatchPrime_mem S i)) (σ i) hx hy)
    (by
      intro i ω ν hx hd
      have hh := signedResidueCode_sub data (hS _ (signedBatchPrime_mem S i)) (σ i) hx hd
      simpa only [sub_sub_cancel, signedResidueVector] using hh)
    (by intro i ω ν hh; rw [hh])
    (by
      intro i ω ν hx he
      have hh := signedResidueCode_sub data (hS _ (signedBatchPrime_mem S i)) (σ i)
        hx (congrArg (fun x => (data.phi (signedBatchPrime S i) (σ i) x).val) he)
      simpa only [sub_sub_cancel, signedResidueVector] using hh)
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun σ _ => h σ)
  simpa only [signedPointEntropy, FinLaw.signedEntropy, signedFreshCoordinate,
    Finset.expect_sub_distrib, Finset.expect_add_distrib, ← Finset.mul_expect,
    Fintype.expect_const] using hh

/-- The natural-number vector and the genuine dependent field vector have
identical conditional entropy, even under arbitrary conditioning. -/
theorem signedResidueVector_conditional_entropy_eq {O : Type*}
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ q ∈ S, q ∈ data.primes)
    (σ : Fin S.card → Bool) (p : FinLaw Ω) (X : Ω → L) (old : Ω → O) :
    p.cHf (fun ω => signedResidueVector data S σ (X ω)) old =
      p.cHf (fun ω => signedBatchResidueHom data S σ (X ω)) old := by
  apply p.cHf_congr_fibers
  · intro ω ν
    exact signedResidueVector_eq_iff data S hS σ
  · intro ω ν; rfl

/-- Coding also preserves the exact conditional information cost. -/
theorem signedResidueVector_information_eq {O Γ : Type*}
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ q ∈ S, q ∈ data.primes)
    (σ : Fin S.card → Bool) (p : FinLaw Ω) (X : Ω → L)
    (Y : Ω → Γ) (old : Ω → O) :
    p.cIf (fun ω => signedResidueVector data S σ (X ω)) Y old =
      p.cIf (fun ω => signedBatchResidueHom data S σ (X ω)) Y old := by
  unfold FinLaw.cIf
  rw [signedResidueVector_conditional_entropy_eq data S hS σ p X old,
    signedResidueVector_conditional_entropy_eq data S hS σ p X (fun ω => (old ω,Y ω))]

/-- A true translated point avoids every actual signed zero class. Thus the
sampled translation can never hit that point's genuine residue observation. -/
theorem avoiding_signedResidue_survives (data : SignedResidueData L)
    (S : Finset ℕ) (σ : Fin S.card → Bool) {x y : L}
    (h : x-y ∈ avoiding data S) (i : Fin S.card) :
    data.phi (signedBatchPrime S i) (σ i) y ≠
      signedBatchResidueHom data S σ x i := by
  have hn : data.phi (signedBatchPrime S i) (σ i) (x-y) ≠ 0 := by
    have hh := h _ (signedBatchPrime_mem S i)
    cases hσ : σ i
    · exact hh.2
    · exact hh.1
  intro he
  apply hn
  change data.phi (signedBatchPrime S i) (σ i) y =
    data.phi (signedBatchPrime S i) (σ i) x at he
  rw [(data.phi (signedBatchPrime S i) (σ i)).map_sub, ← he, sub_self]

/-- Exact posterior prime-code coverage. The information deficit is the actual
conditional entropy deficit, not a supplied information lower-bound premise.
The hypotheses are genuine translation survival, residue-hit floors off
explicit exceptional residue sets, and the numerical sampling budget. -/
theorem signedResidueVector_posterior_coverage {O Γ : Type*} [Fintype O] [Fintype Γ]
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ q ∈ S, q ∈ data.primes)
    (σ : Fin S.card → Bool) (p : FinLaw Ω) (old : Ω → O) (X : Ω → L)
    (q : Ω → FinLaw Γ) (translation : Γ → L)
    (Good : Fin S.card → Ω → Prop)
    (E : (i : Fin S.card) → Ω → Finset (ZMod (signedBatchPrime S i)))
    (e c : Fin S.card → ℝ) {A η : ℝ} (n : ℕ)
    (hA : 0 ≤ A) (he : ∀ i, 0 ≤ e i) (hc : ∀ i, 0 ≤ c i)
    (hsurvive : ∀ ω, p ω ≠ 0 → ∀ v, q ω v ≠ 0 →
      X ω - translation v ∈ avoiding data S)
    (hE : ∀ i ω, Good i ω → ((E i ω).card : ℝ) ≤ e i)
    (hhit : ∀ i ω, Good i ω → ∀ x ∉ E i ω,
      c i ≤ (q ω).prob (fun v => data.phi (signedBatchPrime S i) (σ i) (translation v) = x))
    (hBad : (∑ i, p.prob (fun ω => ¬Good i ω)) ≤ η)
    (hnum : ∀ i, Real.log (4*e i + (signedBatchPrime S i : ℝ)*
      Real.exp (-(n : ℝ)*(c i/4))) ≤ Real.log (signedBatchPrime S i) - A) :
    A * ((S.card : ℝ)-2*η) -
      ((∑ i, Real.log (signedBatchPrime S i)) -
        p.cHf (fun ω => signedResidueVector data S σ (X ω)) old) ≤
      (n : ℝ)*(p.joint q).cIf
        (fun v => signedResidueVector data S σ (X v.1)) Prod.snd (fun v => old v.1) := by
  let (i : Fin S.card) : NeZero (signedBatchPrime S i) :=
    ⟨(data.prime_mem _ (hS _ (signedBatchPrime_mem S i))).ne_zero⟩
  let G := fun i : Fin S.card => ZMod (signedBatchPrime S i)
  let hit := fun (i : Fin S.card) (v : Γ) (x : G i) =>
    data.phi (signedBatchPrime S i) (σ i) (translation v) = x
  let H := (∑ i, Real.log (signedBatchPrime S i)) -
    p.cHf (fun ω => signedBatchResidueHom data S σ (X ω)) old
  have hh := FinLaw.posterior_passing_information_lower G p old
    (fun ω => signedBatchResidueHom data S σ (X ω)) q hit Good E e c n
    hA he hc
    (fun ω hω v hv i => avoiding_signedResidue_survives data S σ (hsurvive ω hω v hv) i)
    hE hhit
    (show (∑ i, Real.log (Fintype.card (G i))) - H ≤
      p.cHf (fun ω => signedBatchResidueHom data S σ (X ω)) old by
      simp only [G, ZMod.card, H]; linarith)
    hBad (by simpa only [G, ZMod.card] using hnum)
  rw [signedResidueVector_information_eq data S hS σ (p.joint q)
    (fun v => X v.1) Prod.snd (fun v => old v.1)]
  rw [signedResidueVector_conditional_entropy_eq data S hS σ p X old]
  simpa only [Fintype.card_fin, H] using hh

/-- A single genuine prime coordinate with arbitrary old conditioning.
Finite coding of the old observation is constructed from its actual range. -/
theorem signedResidue_posterior_coverage {O Γ : Type*} [Fintype Γ]
    (data : SignedResidueData L) {a : ℕ} (ha : a ∈ data.primes) (σ : Bool)
    (p : FinLaw Ω) (old : Ω → O) (X : Ω → L) (q : Ω → FinLaw Γ)
    (translation : Γ → L) (Good : Ω → Prop) (E : Ω → Finset (ZMod a))
    {e c A η : ℝ} (n : ℕ) (hA : 0 ≤ A) (he : 0 ≤ e) (hc : 0 ≤ c)
    (hsurvive : ∀ ω, p ω ≠ 0 → ∀ v, q ω v ≠ 0 →
      data.phi a σ (X ω-translation v) ≠ 0)
    (hE : ∀ ω, Good ω → ((E ω).card : ℝ) ≤ e)
    (hhit : ∀ ω, Good ω → ∀ x ∉ E ω,
      c ≤ (q ω).prob (fun v => data.phi a σ (translation v) = x))
    (hBad : p.prob (fun ω => ¬Good ω) ≤ η)
    (hnum : Real.log (4*e + (a : ℝ)*Real.exp (-(n : ℝ)*(c/4))) ≤ Real.log a-A) :
    A*(1-2*η)-Real.log a + p.cHf (fun ω => (data.phi a σ (X ω)).val) old ≤
      (n : ℝ)*(p.joint q).cIf (fun v => (data.phi a σ (X v.1)).val)
        Prod.snd (fun v => old v.1) := by
  let _ : NeZero a := ⟨(data.prime_mem a ha).ne_zero⟩
  let V := fun ω (_ : Unit) => data.phi a σ (X ω)
  let C := FinLaw.outputCode old
  have hbase : p.cHf V C = p.cHf (fun ω => (data.phi a σ (X ω)).val) old := by
    apply p.cHf_congr_fibers
    · intro ω ν
      exact ⟨fun h => congrArg ZMod.val (congrFun h ()),
        fun h => funext (fun _ => ZMod.val_injective a h)⟩
    · intro ω ν; exact FinLaw.outputCode_eq_iff old ω ν
  have hinfo : (p.joint q).cIf (V ∘ Prod.fst) Prod.snd (C ∘ Prod.fst) =
      (p.joint q).cIf (fun v => (data.phi a σ (X v.1)).val)
        Prod.snd (fun v => old v.1) := by
    unfold FinLaw.cIf
    congr 1 <;> apply (p.joint q).cHf_congr_fibers
    · intro v w
      exact ⟨fun h => congrArg ZMod.val (congrFun h ()),
        fun h => funext (fun _ => ZMod.val_injective a h)⟩
    · intro v w; exact FinLaw.outputCode_eq_iff old v.1 w.1
    · intro v w
      exact ⟨fun h => congrArg ZMod.val (congrFun h ()),
        fun h => funext (fun _ => ZMod.val_injective a h)⟩
    · intro v w
      simp only [Prod.mk.injEq, Function.comp_def, C, FinLaw.outputCode_eq_iff]
  have hh := FinLaw.posterior_passing_information_lower (fun _ : Unit => ZMod a)
    p C V q (fun _ v x => data.phi a σ (translation v) = x)
    (fun _ => Good) (fun _ => E) (fun _ => e) (fun _ => c) n
    hA (fun _ => he) (fun _ => hc)
    (by
      intro ω hω v hv i hhit
      apply hsurvive ω hω v hv
      change data.phi a σ (translation v) = data.phi a σ (X ω) at hhit
      rw [(data.phi a σ).map_sub, ← hhit, sub_self])
    (fun _ => hE) (fun _ => hhit)
    (show (∑ _ : Unit, Real.log (Fintype.card (ZMod a))) -
      (Real.log a-p.cHf V C) ≤ p.cHf V C by simp only [ZMod.card, Fintype.sum_unique]; linarith)
    (by simpa only [Fintype.sum_unique] using hBad)
    (fun _ => by simpa only [ZMod.card] using hnum)
  change A*((Fintype.card Unit : ℝ)-2*η)-(Real.log a-p.cHf V C) ≤
    (n : ℝ)*(p.joint q).cIf (V ∘ Prod.fst) Prod.snd (C ∘ Prod.fst) at hh
  rw [hinfo, hbase] at hh
  simp only [Fintype.card_unit, Nat.cast_one] at hh
  linarith only [hh]

/-- The actual one-sample fresh-coordinate posterior information cost,
allowing the sampling law to depend on the chosen signs and permutation. -/
noncomputable def signedFreshPosteriorCost {Γ : Type*} [Fintype Γ]
    (data : SignedResidueData L) (S : Finset ℕ) (p : FinLaw Ω)
    (q : (Fin S.card → Bool) → Equiv.Perm (Fin S.card) → Ω → FinLaw Γ)
    (X Y : Ω → L) (s : ℕ) (hs : s < S.card) : ℝ :=
  𝔼 σ : Fin S.card → Bool, 𝔼 π : Equiv.Perm (Fin S.card),
    (p.joint (q σ π)).cIf
      (fun v => signedResidueVector data S σ (X v.1-Y v.1) (π ⟨s,hs⟩)) Prod.snd
      (fun v => (FinLaw.prefixVar (fun x => signedResidueVector data S σ (X x)) π s v.1,
        FinLaw.prefixVar (fun x => signedResidueVector data S σ (Y x)) π s v.1))

/-- Sampling can spend at most the genuine fresh entropy remaining after both
endpoint prefixes. The equality of the original marginal is proved from the
joint law rather than assumed. -/
theorem signedFreshPosteriorCost_le_fresh {Γ : Type*} [Fintype Γ]
    (data : SignedResidueData L) (S : Finset ℕ) (p : FinLaw Ω)
    (q : (Fin S.card → Bool) → Equiv.Perm (Fin S.card) → Ω → FinLaw Γ)
    (X Y : Ω → L) (s : ℕ) (hs : s < S.card) :
    signedFreshPosteriorCost data S p q X Y s hs ≤
      signedFreshCoordinate data S p X Y s hs := by
  apply Finset.expect_le_expect
  intro σ _
  apply Finset.expect_le_expect
  intro π _
  let A := fun ω => signedResidueVector data S σ (X ω-Y ω) (π ⟨s,hs⟩)
  let C := fun ω => (FinLaw.prefixVar (fun x => signedResidueVector data S σ (X x)) π s ω,
    FinLaw.prefixVar (fun x => signedResidueVector data S σ (Y x)) π s ω)
  have hm := (p.joint (q σ π)).cHf_map Prod.fst A C
  rw [FinLaw.joint_map_fst] at hm
  exact ((p.joint (q σ π)).cIf_le_cHf (A ∘ Prod.fst) Prod.snd (C ∘ Prod.fst)).trans
    (le_of_eq hm.symm)

/-- The genuine fresh-prime coverage inequality averaged over the actual
signed batch. It lower-bounds posterior information from the remaining fresh
entropy, actual prime logarithms and explicit exceptional-hit probabilities.
No information inequality is supplied as a hypothesis. -/
theorem signedFreshPosteriorCost_coverage_lower {Γ : Type*} [Fintype Γ]
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ a ∈ S, a ∈ data.primes)
    (p : FinLaw Ω)
    (q : (Fin S.card → Bool) → Equiv.Perm (Fin S.card) → Ω → FinLaw Γ)
    (X Y : Ω → L) (translation : Γ → L) (s : ℕ) (hs : s < S.card)
    (Good : (Fin S.card → Bool) → Equiv.Perm (Fin S.card) → Ω → Prop)
    (E : (σ : Fin S.card → Bool) → (π : Equiv.Perm (Fin S.card)) →
      Ω → Finset (ZMod (signedBatchPrime S (π ⟨s,hs⟩))))
    (e c : (Fin S.card → Bool) → Equiv.Perm (Fin S.card) → ℝ)
    {A η : ℝ} (n : ℕ) (hA : 0 ≤ A) (he : ∀ σ π, 0 ≤ e σ π) (hc : ∀ σ π, 0 ≤ c σ π)
    (hsurvive : ∀ σ π ω, p ω ≠ 0 → ∀ v, q σ π ω v ≠ 0 →
      (X ω-Y ω)-translation v ∈ avoiding data S)
    (hE : ∀ σ π ω, Good σ π ω → ((E σ π ω).card : ℝ) ≤ e σ π)
    (hhit : ∀ σ π ω, Good σ π ω → ∀ x ∉ E σ π ω,
      c σ π ≤ (q σ π ω).prob (fun v =>
        data.phi (signedBatchPrime S (π ⟨s,hs⟩)) (σ (π ⟨s,hs⟩)) (translation v) = x))
    (hBad : ∀ σ π, p.prob (fun ω => ¬Good σ π ω) ≤ η)
    (hnum : ∀ σ π, Real.log (4*e σ π + (signedBatchPrime S (π ⟨s,hs⟩) : ℝ)*
        Real.exp (-(n : ℝ)*(c σ π/4))) ≤
      Real.log (signedBatchPrime S (π ⟨s,hs⟩))-A) :
    A*(1-2*η) -
      (𝔼 π : Equiv.Perm (Fin S.card), Real.log (signedBatchPrime S (π ⟨s,hs⟩))) +
      signedFreshCoordinate data S p X Y s hs ≤
      (n : ℝ)*signedFreshPosteriorCost data S p q X Y s hs := by
  have hpoint (σ : Fin S.card → Bool) (π : Equiv.Perm (Fin S.card)) :=
    signedResidue_posterior_coverage data (hS _ (signedBatchPrime_mem S (π ⟨s,hs⟩)))
      (σ (π ⟨s,hs⟩)) p
      (fun ω => (FinLaw.prefixVar (fun x => signedResidueVector data S σ (X x)) π s ω,
        FinLaw.prefixVar (fun x => signedResidueVector data S σ (Y x)) π s ω))
      (fun ω => X ω-Y ω) (q σ π) translation (Good σ π) (E σ π) n
      hA (he σ π) (hc σ π)
      (by
        intro ω hω v hv
        have hn := hsurvive σ π ω hω v hv _ (signedBatchPrime_mem S (π ⟨s,hs⟩))
        cases hσ : σ (π ⟨s,hs⟩)
        · exact hn.2
        · exact hn.1)
      (hE σ π) (hhit σ π) (hBad σ π) (hnum σ π)
  have h := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ => hpoint σ π))
  simpa only [signedFreshCoordinate, signedFreshPosteriorCost, signedResidueVector,
    Finset.expect_add_distrib, Finset.expect_sub_distrib, ← Finset.mul_expect,
    Fintype.expect_const] using h

end Entry002
