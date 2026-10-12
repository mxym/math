import Entry002.GenericFreshCoverage
import Entry002.GenericTimeKernels

/-! Actual fair-endpoint enrichment for the genuine finite walk-difference
sampling kernel. The displacement cost is the logarithm of an actual finite
alphabet, with no Gaussian lattice counting constant or entropy certificate.
The generic map/fair-endpoint and accounting proof patterns are adapted from
upstream-028/GaussianMoat/PointEnrichment.lean lines 302–363 and TimeLaw.lean
lines 25–98, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a (Apache-2.0). -/

namespace Entry002
open OAI.GaussianMoat
open scoped BigOperators Classical
variable {L Ω : Type*} [AddCommGroup L] [Fintype Ω]

lemma signedPointEntropy_map {Κ : Type*} [Fintype Κ]
    (data : SignedResidueData L) (S : Finset ℕ) (p : FinLaw Ω) (f : Ω → Κ)
    (X : Κ → L) (s : ℕ) :
    signedPointEntropy data S (p.map f) X s = signedPointEntropy data S p (X ∘ f) s := by
  unfold signedPointEntropy FinLaw.signedEntropy FinLaw.orderedEntropy
  simp only [FinLaw.Hf_map]
  rfl

lemma signedPointEntropy_joint_fst {Κ : Type*} [Fintype Κ]
    (data : SignedResidueData L) (S : Finset ℕ) (p : FinLaw Ω)
    (q : Ω → FinLaw Κ) (X : Ω → L) (s : ℕ) :
    signedPointEntropy data S (p.joint q) (fun v => X v.1) s =
      signedPointEntropy data S p X s := by
  have h := signedPointEntropy_map data S (p.joint q) Prod.fst X s
  rw [FinLaw.joint_map_fst] at h
  exact h.symm

lemma signedPointEntropy_fair_endpoint (data : SignedResidueData L) (S : Finset ℕ)
    (p : FinLaw Ω) (X Y : Ω → L) (s : ℕ) :
    signedPointEntropy data S p X s + signedPointEntropy data S p Y s ≤
      2 * signedPointEntropy data S ((FinLaw.uniform Bool).joint (fun _ => p))
        (fun v => if v.1 then X v.2 else Y v.2) s := by
  have h := Finset.expect_le_expect (s := Finset.univ) (fun σ _ =>
    Finset.expect_le_expect (s := Finset.univ) (fun π _ =>
      (FinLaw.uniform Bool).Hf_joint_ge (fun _ => p)
        (fun c ω => FinLaw.prefixVar
          (fun x => signedResidueVector data S σ (if c then X x else Y x)) π s ω)))
  simp only [Fintype.sum_bool, FinLaw.uniform_mass, Fintype.card_bool, Nat.cast_ofNat,
    Bool.false_eq_true, ite_false, ite_true, Finset.expect_add_distrib,
    ← Finset.mul_expect] at h
  change (2 : ℝ)⁻¹*signedPointEntropy data S p X s +
    (2 : ℝ)⁻¹*signedPointEntropy data S p Y s ≤
    signedPointEntropy data S ((FinLaw.uniform Bool).joint (fun _ => p))
      (fun v => if v.1 then X v.2 else Y v.2) s at h
  linarith

omit [AddCommGroup L] in
/-- Membership in an actual finite displacement alphabet gives its genuine
log-cardinality entropy bound. -/
lemma finiteDisplacement_entropy_le (p : FinLaw Ω) (X : Ω → L) (A : Finset L)
    (hX : ∀ ω, X ω ∈ A) : p.Hf X ≤ Real.log A.card := by
  let Y := fun ω => (⟨X ω, hX ω⟩ : A)
  have he : p.Hf X = p.Hf Y :=
    p.Hf_eq_of_fibers _ _ (fun ω ν => by
      change (Y ω).val = (Y ν).val ↔ Y ω = Y ν
      exact Subtype.val_injective.eq_iff)
  rw [he]
  simpa only [Fintype.card_coe] using p.Hf_le_log_card_type Y

/-- Actual enrichment with two finite displacement costs. -/
theorem signedPointEntropy_actual_enrichment (data : SignedResidueData L)
    (S : Finset ℕ) (hS : ∀ a ∈ S, a ∈ data.primes) (p : FinLaw Ω)
    (X Y Z : Ω → L) (A : Finset L) {s r : ℕ}
    (hs : 0 < s) (hsr : s < r) (hr : r ≤ S.card) {F : ℝ}
    (hF : F ≤ signedFreshCoordinate data S p X Y s (by omega))
    (hXY : ∀ ω, X ω-Y ω ∈ A) (hXZ : ∀ ω, X ω-Z ω ∈ A) :
    (s : ℝ)*((r-s : ℕ)*F + signedPointEntropy data S p Z r - 2*Real.log A.card) ≤
      2*(r : ℝ)*signedPointEntropy data S ((FinLaw.uniform Bool).joint (fun _ => p))
        (fun v => if v.1 then X v.2 else Y v.2) s := by
  have h := signedPointEntropy_enrichment_accounting data S hS p X Y Z hs hsr hr
  have h1 := finiteDisplacement_entropy_le p (fun ω => X ω-Y ω) A hXY
  have h2 := finiteDisplacement_entropy_le p (fun ω => X ω-Z ω) A hXZ
  have he := signedPointEntropy_fair_endpoint data S p X Y s
  have hm := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg r)
  have hf := mul_le_mul_of_nonneg_left hF (show (0 : ℝ) ≤ (r-s : ℕ) by positivity)
  have hsub : (r-s : ℕ)*F + signedPointEntropy data S p Z r - 2*Real.log A.card ≤
      (r-s : ℕ)*signedFreshCoordinate data S p X Y s (by omega) +
      signedPointEntropy data S p Z r - p.Hf (fun ω => X ω-Y ω) -
      p.Hf (fun ω => X ω-Z ω) := by linarith
  have hmul := mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg s)
  nlinarith

/-- The literal resulting time of the chosen fair endpoint. -/
noncomputable def fairEndpointTime (a n : ℕ) :
    Bool × (Fin (a+1) × (Fin (n+1) × Fin (n+1))) → Fin (a+n+1) :=
  fun v => ⟨v.2.1.val + (if v.1 then v.2.2.1.val else v.2.2.2.val), by
    split_ifs <;> omega⟩

/-- Composing the genuine endpoint kernel equals the fair endpoint pushforward
of the joint starting-time and genuine walk-difference law. -/
lemma TimeLaw.advance_difference_law (P : TimeLaw) (z : ℕ → L) (n : ℕ) :
    (P.advance (differenceKernel z n)).law =
      ((FinLaw.uniform Bool).joint (fun _ => P.law.joint (fun a =>
        walkDifferenceLaw (fun t => z (a.val+t)) n))).map (fairEndpointTime P.last n) := by
  change (P.law.joint (fun a =>
    (((FinLaw.uniform Bool).joint (fun _ => walkDifferenceLaw (fun t => z (a.val+t)) n)).map
      (fun v => if v.1 then v.2.1 else v.2.2)))).map (addOffsets P.last n) = _
  rw [FinLaw.joint_observation_fun, FinLaw.joint_observation_fun]
  simp_rw [FinLaw.map_comp, FinLaw.joint_observation_fun]
  rw [FinLaw.mix_comm]
  congr 1
  funext c
  congr 1
  funext a
  congr 1
  funext ij
  apply Fin.ext
  dsimp only [Function.comp_def, addOffsets, fairEndpointTime]
  split_ifs <;> rfl

/-- Enrichment for the actual endpoint-kernel advance. The support hypothesis
is literal membership in one finite displacement alphabet, uniformly over
actual starting times and endpoint pairs. -/
theorem TimeLaw.advance_difference_enrichment (P : TimeLaw)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ a ∈ S, a ∈ data.primes)
    (z : ℕ → L) (A : Finset L) {n s r : ℕ} (hs : 0 < s)
    (hsr : s < r) (hr : r ≤ S.card) {F : ℝ}
    (hpair : ∀ a : Fin (P.last+1), ∀ i j : Fin (n+1),
      z (a.val+i.val)-z (a.val+j.val) ∈ A)
    (hF : ∀ a : Fin (P.last+1), F ≤ signedFreshCoordinate data S
      (walkDifferenceLaw (fun t => z (a.val+t)) n)
      (fun ij => z (a.val+ij.1.val)) (fun ij => z (a.val+ij.2.val)) s (by omega)) :
    (s : ℝ)*((r-s : ℕ)*F + signedPointEntropy data S P.law (fun a => z a.val) r -
      2*Real.log A.card) ≤
      2*(r : ℝ)*signedPointEntropy data S (P.advance (differenceKernel z n)).law
        (fun a => z a.val) s := by
  let K := P.law.joint (fun a => walkDifferenceLaw (fun t => z (a.val+t)) n)
  let X := fun v : Fin (P.last+1) × (Fin (n+1) × Fin (n+1)) => z (v.1.val+v.2.1.val)
  let Y := fun v : Fin (P.last+1) × (Fin (n+1) × Fin (n+1)) => z (v.1.val+v.2.2.val)
  let Z := fun v : Fin (P.last+1) × (Fin (n+1) × Fin (n+1)) => z v.1.val
  have hF' : F ≤ signedFreshCoordinate data S K X Y s (by omega) := by
    have hh := signedFreshCoordinate_joint_ge data S P.law
      (fun a => walkDifferenceLaw (fun t => z (a.val+t)) n)
      (fun a ij => z (a.val+ij.1.val)) (fun a ij => z (a.val+ij.2.val)) (by omega : s < S.card)
    apply le_trans _ hh
    have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ =>
      mul_le_mul_of_nonneg_left (hF a) (P.law.nonneg a))
    simpa only [← Finset.sum_mul, P.law.sum_one, one_mul] using hsum
  have h := signedPointEntropy_actual_enrichment data S hS K X Y Z A hs hsr hr hF'
    (fun v => hpair v.1 v.2.1 v.2.2)
    (fun v => by simpa only [X, Z, Fin.val_zero, Nat.add_zero] using hpair v.1 v.2.1 0)
  have hZ := signedPointEntropy_joint_fst data S P.law
    (fun a => walkDifferenceLaw (fun t => z (a.val+t)) n) (fun a => z a.val) r
  change signedPointEntropy data S K Z r = _ at hZ
  rw [hZ] at h
  have hout : signedPointEntropy data S (P.advance (differenceKernel z n)).law
      (fun a => z a.val) s =
      signedPointEntropy data S ((FinLaw.uniform Bool).joint (fun _ => K))
        (fun v => if v.1 then X v.2 else Y v.2) s := by
    rw [TimeLaw.advance_difference_law]
    change signedPointEntropy data S
      (((FinLaw.uniform Bool).joint (fun _ => K)).map (fairEndpointTime P.last n))
      (fun a => z a.val) s = _
    rw [signedPointEntropy_map]
    congr 1
    funext v
    simp only [Function.comp_def, fairEndpointTime, X, Y]
    split_ifs <;> rfl
  rw [hout]
  exact h

/-- The actual full-lattice step enrichment theorem. Its only entropy-rate
input is a genuine fresh-coordinate lower bound for the uniform walk-difference
law at every starting time. All displacement costs follow from the actual
planar metric and the actual finite lattice ball. -/
theorem TimeLaw.step_enrichment (P : TimeLaw)
    (data : SignedResidueData L) (S : Finset ℕ) (hS : ∀ a ∈ S, a ∈ data.primes)
    (b : Module.Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (z : ℕ → L) {D F : ℝ} (hD : 0 ≤ D)
    (hstep : ∀ t, dist (planarEmbedding b e (z t))
      (planarEmbedding b e (z (t+1))) ≤ D)
    {n s r : ℕ} (hs : 0 < s) (hsr : s < r) (hr : r ≤ S.card)
    (hF : ∀ a : Fin (P.last+1), F ≤ signedFreshCoordinate data S
      (walkDifferenceLaw (fun t => z (a.val+t)) n)
      (fun ij => z (a.val+ij.1.val)) (fun ij => z (a.val+ij.2.val)) s (by omega)) :
    (s : ℝ)*((r-s : ℕ)*F + signedPointEntropy data S P.law (fun a => z a.val) r -
      2*Real.log (wordStepBall b e (D*n)).card) ≤
      2*(r : ℝ)*signedPointEntropy data S (P.step z n).law (fun a => z a.val) s := by
  apply P.advance_difference_enrichment data S hS z (wordStepBall b e (D*n)) hs hsr hr
    (hF := hF)
  intro a i j
  rw [mem_wordStepBall]
  exact walk_pair_displacement b e z hD hstep a.val n i.val j.val (by omega) (by omega)

end Entry002
