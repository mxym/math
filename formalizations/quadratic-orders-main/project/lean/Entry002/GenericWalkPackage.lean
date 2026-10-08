import Entry002.GenericStepEnrichment

/-! Actual finite packages for arbitrary forward walk kernels and additive
residue observations. Proof patterns are adapted from WalkPackage.lean lines
9–52 and 152–228, Information.lean lines 335–360, and MultiscaleSchedule.lean
lines 84–106 of pinned upstream-028, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0).
Kernel probabilities require no word-fiber invariance: the same honest joint
law occurs on both sides of the proved information transport.
-/

namespace OAI.GaussianMoat.FinLaw
open scoped BigOperators Classical

lemma cIf_congr_fibers {Ω α α' β β' γ γ' : Type*} [Fintype Ω]
    (p : FinLaw Ω) (X : Ω → α) (X' : Ω → α')
    (Y : Ω → β) (Y' : Ω → β') (O : Ω → γ) (O' : Ω → γ')
    (hX : ∀ ω ν, X ω=X ν ↔ X' ω=X' ν)
    (hY : ∀ ω ν, Y ω=Y ν ↔ Y' ω=Y' ν)
    (hO : ∀ ω ν, O ω=O ν ↔ O' ω=O' ν) :
    p.cIf X Y O=p.cIf X' Y' O' := by
  unfold cIf
  rw [p.cHf_congr_fibers X X' O O' hX hO]
  congr 1
  apply p.cHf_congr_fibers _ _ _ _ hX
  intro ω ν
  simp only [Prod.mk.injEq,hO,hY]

lemma joint_map_cIf {Ω Γ Γ' α β : Type*} [Fintype Ω] [Fintype Γ] [Fintype Γ']
    (p : FinLaw Ω) (q : Ω → FinLaw Γ) (f : Ω → Γ → Γ') (X : Ω → α) (O : Ω → β) :
    (p.joint (fun ω => (q ω).map (f ω))).cIf (fun v => X v.1) Prod.snd (fun v => O v.1)=
      (p.joint q).cIf (fun v => X v.1) (fun v => f v.1 v.2) (fun v => O v.1) := by
  rw [← joint_map_fiber,cIf_map]
  rfl

end OAI.GaussianMoat.FinLaw

namespace Entry002
open OAI.GaussianMoat
open scoped BigOperators Classical
variable {L : Type*} [AddCommGroup L]

/-- Actual finite displacement and actual bounded increment word. -/
abbrev WalkPackage (b : Module.Basis (Fin 2) ℤ L)
    (e : CoeffSpace ≃ₗ[ℝ] Plane) (D : ℝ) (B len : ℕ) :=
  wordStepBall b e (D*B) × (Fin len → wordStepBall b e D)

noncomputable def ForwardKernel.displacementSymbol (K : ForwardKernel)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D) (a : ℕ) (u : Fin (K.bound+1)) :
    wordStepBall b e (D*K.bound) :=
  ⟨z (a+u.val)-z a, (mem_wordStepBall b e (D*K.bound) _).mpr (by
    simpa only [Nat.add_zero] using walk_pair_displacement b e z hD hs
      a K.bound u.val 0 (by omega) (by omega))⟩

noncomputable def ForwardKernel.packageSymbol (K : ForwardKernel)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D) (a len : ℕ) (u : Fin (K.bound+1)) :
    WalkPackage b e D K.bound len :=
  (K.displacementSymbol b e z hD hs a u,
    boundedWord z (wordStepBall b e D) (bounded_steps_in_wordStepBall b e z D hs) len (a+u.val))

noncomputable def ForwardKernel.packageLaw (K : ForwardKernel)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D) (a len : ℕ) :
    FinLaw (WalkPackage b e D K.bound len) :=
  (K.law a).map (K.packageSymbol b e z hD hs a len)

noncomputable def WalkPackage.prefix {b : Module.Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} {D : ℝ} {B len : ℕ}
    (v : WalkPackage b e D B len) (i : Fin len) : L :=
  v.1.val + ∑ j : Fin i.val, (v.2 ⟨j.val, lt_trans j.isLt i.isLt⟩).val

lemma ForwardKernel.packageSymbol_prefix (K : ForwardKernel)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D) (a len : ℕ) (u : Fin (K.bound+1)) (i : Fin len) :
    (K.packageSymbol b e z hD hs a len u).prefix i = z (a+u.val+i.val)-z a := by
  change z (a+u.val)-z a + ∑ j : Fin i.val, incrementWord z i.val (a+u.val) j = _
  rw [incrementWord_sum]
  abel

/-- The package records precisely displacement and word; subtype membership
proofs create no extra information. -/
lemma ForwardKernel.packageSymbol_fibers (K : ForwardKernel)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D) (a a' len : ℕ)
    (u u' : Fin (K.bound+1)) :
    K.packageSymbol b e z hD hs a len u = K.packageSymbol b e z hD hs a' len u' ↔
      (z (a+u.val)-z a, incrementWord z len (a+u.val)) =
      (z (a'+u'.val)-z a', incrementWord z len (a'+u'.val)) := by
  simp only [packageSymbol, Prod.mk.injEq, Subtype.mk.injEq, displacementSymbol,
    boundedWord_fibers]

/-- Shifting both observations by the same actual displacement preserves the
joint observation/displacement fibers, by additivity of the residue map. -/
lemma additive_observation_shift {R Ω : Type*} [AddCommGroup R]
    (ρ : L →+ R) (X Y : Ω → L) (ω ν : Ω) :
    (ρ (X ω), Y ω-X ω) = (ρ (X ν), Y ν-X ν) ↔
      (ρ (Y ω), Y ω-X ω) = (ρ (Y ν), Y ν-X ν) := by
  simp only [Prod.mk.injEq]
  constructor
  · rintro ⟨hx, hd⟩
    refine ⟨?_, hd⟩
    have he := congrArg ρ hd
    simpa only [map_sub, hx, sub_left_inj] using he
  · rintro ⟨hy, hd⟩
    refine ⟨?_, hd⟩
    have he := congrArg ρ hd
    simpa only [map_sub, hy, sub_right_inj] using he

/-- Actual information transport for arbitrary forward kernels and additive
observations. The finite-ball error is derived from the genuine displacement
support; no transport or kernel-invariance premise is used. -/
theorem ForwardKernel.package_information_transport {Ω R Rold : Type*}
    [Fintype Ω] [AddCommGroup R] [AddCommGroup Rold]
    (K : ForwardKernel) (p : FinLaw Ω) (a : Ω → ℕ)
    (ρ : L →+ R) (ρold : L →+ Rold)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D) (len : ℕ) :
    (p.joint (fun ω => K.packageLaw b e z hD hs (a ω) len)).cIf
      (fun v => ρ (z (a v.1))) Prod.snd (fun v => ρold (z (a v.1))) ≤
    (p.joint (fun ω => K.law (a ω))).cIf
      (fun v => ρ (z (a v.1+v.2.val)))
      (fun v => incrementWord z len (a v.1+v.2.val))
      (fun v => ρold (z (a v.1+v.2.val))) +
      2*Real.log (wordStepBall b e (D*K.bound)).card := by
  let P := p.joint (fun ω => K.law (a ω))
  let X := fun v : Ω × Fin (K.bound+1) => z (a v.1)
  let Y := fun v : Ω × Fin (K.bound+1) => z (a v.1+v.2.val)
  let S := fun v => Y v-X v
  let W := fun v : Ω × Fin (K.bound+1) => incrementWord z len (a v.1+v.2.val)
  have hemap := FinLaw.joint_map_cIf p (fun ω => K.law (a ω))
    (fun ω => K.packageSymbol b e z hD hs (a ω) len)
    (fun ω => ρ (z (a ω))) (fun ω => ρold (z (a ω)))
  change (p.joint (fun ω => K.packageLaw b e z hD hs (a ω) len)).cIf _ _ _ = _ at hemap
  rw [hemap]
  have he := P.cIf_congr_fibers (fun v => ρ (X v)) (fun v => ρ (X v))
    (fun v => K.packageSymbol b e z hD hs (a v.1) len v.2) (fun v => (S v,W v))
    (fun v => ρold (X v)) (fun v => ρold (X v))
    (fun _ _ => Iff.rfl)
    (fun v w => K.packageSymbol_fibers b e z hD hs (a v.1) (a w.1) len v.2 w.2)
    (fun _ _ => Iff.rfl)
  change P.cIf _ _ _ ≤ _
  rw [he]
  have ht := P.cIf_transport (fun v => ρ (X v)) (fun v => ρold (X v))
    (fun v => ρ (Y v)) (fun v => ρold (Y v)) W S
    (additive_observation_shift ρold X Y) (by
      intro v w
      have hf := additive_observation_shift ρ X Y v w
      have hg := additive_observation_shift ρold X Y v w
      simp only [Prod.mk.injEq, S] at hf hg ⊢
      tauto)
  have hc : P.Hf S ≤ Real.log (wordStepBall b e (D*K.bound)).card := by
    apply displacement_entropy_le_stepBall
    intro v
    simpa only [S, X, Y, Nat.add_zero] using walk_pair_displacement b e z hD hs
      (a v.1) K.bound v.2.val 0 (by omega) (by omega)
  exact ht.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hc (by norm_num)))

/-- A package hits a start residue when one of its actual relative positions
lies in the corresponding translated zero class. -/
def WalkPackage.Hits {R : Type*} [AddCommGroup R]
    {b : Module.Basis (Fin 2) ℤ L} {e : CoeffSpace ≃ₗ[ℝ] Plane}
    {D : ℝ} {B len : ℕ} (ρ : L →+ R) (v : WalkPackage b e D B len) (x : R) : Prop :=
  ∃ i : Fin len, ρ (v.prefix i) = -x

/-- Genuine zero-class avoidance gives package survival on the actual
pushforward support. -/
lemma ForwardKernel.package_true_survives {R : Type*} [AddCommGroup R]
    (K : ForwardKernel) (ρ : L →+ R)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    (havoid : ∀ t, ρ (z t) ≠ 0) {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D) (a len : ℕ) :
    ∀ v, K.packageLaw b e z hD hs a len v ≠ 0 →
      ¬WalkPackage.Hits ρ v (ρ (z a)) := by
  intro v hv
  rw [packageLaw, FinLaw.map_mass] at hv
  obtain ⟨u, _, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  have he : K.packageSymbol b e z hD hs a len u = v := by
    by_contra he
    simp only [ite_eq_right he, ne_self_iff_false] at hu
  rw [← he]
  rintro ⟨i, hi⟩
  rw [K.packageSymbol_prefix b e z hD hs a len u i, map_sub] at hi
  have hz := congrArg (fun r => r + ρ (z a)) hi
  have hz' : ρ (z (a+u.val+i.val)) = 0 := by simpa using hz
  exact havoid _ hz'

/-- The previous survival statement applied to actual selected prime maps. -/
lemma ForwardKernel.signed_package_true_survives (K : ForwardKernel)
    (data : SignedResidueData L) (S : Finset ℕ) (z : ℕ → L)
    (havoid : ∀ t, z t ∈ avoiding data S) {q : ℕ} (hq : q ∈ S) (σ : Bool)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    {D : ℝ} (hD : 0 ≤ D)
    (hs : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D) (a len : ℕ) :
    ∀ v, K.packageLaw b e z hD hs a len v ≠ 0 →
      ¬WalkPackage.Hits (data.phi q σ) v (data.phi q σ (z a)) := by
  apply K.package_true_survives (data.phi q σ) b e z _ hD hs a len
  intro t
  cases σ
  · exact (havoid t q hq).2
  · exact (havoid t q hq).1

/-- Actual coded prime prefixes lose at most the displacement entropy when
points are shifted. Each required prefix fiber relation is proved from the
actual additive prime maps. -/
theorem signedPointEntropy_shift {Ω : Type*} [Fintype Ω]
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ a ∈ S, a ∈ data.primes)
    (p : FinLaw Ω) (X Y : Ω → L) (s : ℕ) :
    signedPointEntropy data S p X s ≤ signedPointEntropy data S p Y s +
      p.Hf (fun ω => Y ω-X ω) := by
  have h (σ : Fin S.card → Bool) (π : Equiv.Perm (Fin S.card)) :
      p.Hf (FinLaw.prefixVar (fun ω => signedResidueVector data S σ (X ω)) π s) ≤
        p.Hf (FinLaw.prefixVar (fun ω => signedResidueVector data S σ (Y ω)) π s) +
          p.Hf (fun ω => Y ω-X ω) := by
    apply (p.Hf_le_of_determined _ (fun ω =>
      (FinLaw.prefixVar (fun ν => signedResidueVector data S σ (Y ν)) π s ω,Y ω-X ω)) ?_).trans
      (p.Hf_pair_subadd _ _)
    intro ω ν hh
    funext i
    by_cases hi : i.val < s
    · have hy : signedResidueVector data S σ (Y ω) (π i) =
          signedResidueVector data S σ (Y ν) (π i) := by
        simpa [FinLaw.prefixVar, hi] using congrFun (congrArg Prod.fst hh) i
      have hd := congrArg (fun x =>
        (data.phi (signedBatchPrime S (π i)) (σ (π i)) x).val) (congrArg Prod.snd hh)
      have hx := signedResidueCode_sub data (hS _ (signedBatchPrime_mem S (π i))) (σ (π i)) hy hd
      simpa only [sub_sub_cancel, signedResidueVector, FinLaw.prefixVar, hi, ite_eq_left]
        using congrArg some hx
    · simp [FinLaw.prefixVar, hi]
  have hh := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ => h σ π))
  simpa only [signedPointEntropy, FinLaw.signedEntropy, FinLaw.orderedEntropy,
    Finset.expect_add_distrib, Fintype.expect_const] using hh

/-- Equivalent lower-bound form with the `X-Y` displacement orientation. -/
theorem signedPointEntropy_shift_sub {Ω : Type*} [Fintype Ω]
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ a ∈ S, a ∈ data.primes)
    (p : FinLaw Ω) (X Y : Ω → L) (s : ℕ) :
    signedPointEntropy data S p X s - p.Hf (fun ω => X ω-Y ω) ≤
      signedPointEntropy data S p Y s := by
  have hh := signedPointEntropy_shift data S hS p X Y s
  have he : p.Hf (fun ω => Y ω-X ω) = p.Hf (fun ω => X ω-Y ω) := by
    apply p.Hf_eq_of_fibers
    intro ω ν
    exact ⟨fun h => by simpa only [neg_sub] using congrArg Neg.neg h,
      fun h => by simpa only [neg_sub] using congrArg Neg.neg h⟩
  rw [he] at hh
  linarith only [hh]

/-- Advancing the actual time law loses at most the logarithm of the actual
finite displacement ball. No entropy-loss estimate is assumed. -/
theorem TimeLaw.advance_entropy (P : TimeLaw) (K : ForwardKernel)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ a ∈ S, a ∈ data.primes)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) (z : ℕ → L)
    {D : ℝ} (hD : 0 ≤ D)
    (hstep : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D) (s : ℕ) :
    signedPointEntropy data S P.law (fun a => z a.val) s -
      Real.log (wordStepBall b e (D*K.bound)).card ≤
      signedPointEntropy data S (P.advance K).law (fun a => z a.val) s := by
  let Q := P.law.joint (fun a => K.law a.val)
  have hh := signedPointEntropy_shift data S hS Q (fun v => z v.1.val)
    (fun v => z (v.1.val+v.2.val)) s
  have hfst := signedPointEntropy_joint_fst data S P.law
    (fun a => K.law a.val) (fun a => z a.val) s
  change signedPointEntropy data S Q (fun v => z v.1.val) s = _ at hfst
  rw [hfst] at hh
  have he : signedPointEntropy data S (P.advance K).law (fun a => z a.val) s =
      signedPointEntropy data S Q (fun v => z (v.1.val+v.2.val)) s := by
    unfold TimeLaw.advance
    rw [signedPointEntropy_map]
    rfl
  rw [← he] at hh
  have hc := P.advance_displacement_entropy K b e z hD hstep
  change Q.Hf (fun v => z (v.1.val+v.2.val)-z v.1.val) ≤ _ at hc
  linarith only [hh, hc]

end Entry002
