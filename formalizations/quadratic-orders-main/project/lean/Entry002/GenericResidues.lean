import Entry002.Sieve
import Entry002.GenericCoverage

/-!
# Actual generic finite signed-prime residue observations

The observations below are the supplied additive maps in `SignedResidueData`.
Their alphabets are proved finite from the selected prime hypotheses, their
cardinalities and entropy budgets are exact, and larger observation families
genuinely refine smaller families. No Gaussian arithmetic is used.
-/

namespace Entry002

open Module
open OAI.GaussianMoat
open scoped BigOperators

variable {L : Type*} [AddCommGroup L]

/-- One actual prime-field coordinate for each selected prime/sign pair. -/
abbrev ResidueFamily (F : Finset (ℕ × Bool)) := (i : F) → ZMod i.val.1

/-- The actual joint additive residue map supplied by the arithmetic data. -/
def residueFamilyHom (data : SignedResidueData L) (F : Finset (ℕ × Bool)) :
    L →+ ResidueFamily F where
  toFun x i := data.phi i.val.1 i.val.2 x
  map_zero' := by funext i; exact (data.phi i.val.1 i.val.2).map_zero
  map_add' x y := by funext i; exact (data.phi i.val.1 i.val.2).map_add x y

@[simp] theorem residueFamilyHom_apply (data : SignedResidueData L)
    (F : Finset (ℕ × Bool)) (x : L) (i : F) :
    residueFamilyHom data F x i = data.phi i.val.1 i.val.2 x := rfl

/-- Finiteness follows from actual primality of every selected coordinate. -/
theorem residueFamily_finite (data : SignedResidueData L) (F : Finset (ℕ × Bool))
    (hF : ∀ i ∈ F, i.1 ∈ data.primes) : Finite (ResidueFamily F) := by
  let (i : F) : NeZero i.val.1 := ⟨(data.prime_mem _ (hF i.val i.property)).ne_zero⟩
  infer_instance

/-- A usable finite alphabet instance, constructed rather than assumed. -/
@[instance_reducible] noncomputable def residueFamilyFintype (data : SignedResidueData L)
    (F : Finset (ℕ × Bool)) (hF : ∀ i ∈ F, i.1 ∈ data.primes) :
    Fintype (ResidueFamily F) := by
  let _ := residueFamily_finite data F hF
  exact Fintype.ofFinite _

/-- The actual alphabet has precisely the product of the selected primes as
its cardinality; repeated primes with different signs contribute twice. -/
theorem residueFamily_natCard (data : SignedResidueData L) (F : Finset (ℕ × Bool))
    (hF : ∀ i ∈ F, i.1 ∈ data.primes) :
    Nat.card (ResidueFamily F) = F.prod (fun i => i.1) := by
  classical
  let (i : F) : NeZero i.val.1 := ⟨(data.prime_mem _ (hF i.val i.property)).ne_zero⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  simp only [ZMod.card]
  exact Finset.prod_coe_sort F (fun i => i.1)

theorem residueFamily_fintypeCard (data : SignedResidueData L) (F : Finset (ℕ × Bool))
    (hF : ∀ i ∈ F, i.1 ∈ data.primes) :
    @Fintype.card (ResidueFamily F) (residueFamilyFintype data F hF) =
      F.prod (fun i => i.1) := by
  let _ := residueFamilyFintype data F hF
  rw [← Nat.card_eq_fintype_card]
  exact residueFamily_natCard data F hF

/-- The exact logarithmic alphabet budget. -/
theorem residueFamily_logCard (data : SignedResidueData L) (F : Finset (ℕ × Bool))
    (hF : ∀ i ∈ F, i.1 ∈ data.primes) :
    Real.log (Nat.card (ResidueFamily F)) = F.sum (fun i => Real.log i.1) := by
  rw [residueFamily_natCard data F hF, Nat.cast_prod]
  exact Real.log_prod (fun i hi => by
    exact_mod_cast (data.prime_mem _ (hF i hi)).ne_zero)

/-- Restricting a refined observation is an actual additive projection. -/
def residueFamilyRestriction (F G : Finset (ℕ × Bool)) (hFG : F ⊆ G) :
    ResidueFamily G →+ ResidueFamily F where
  toFun r i := r ⟨i.val, hFG i.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem residueFamilyRestriction_comp (data : SignedResidueData L)
    (F G : Finset (ℕ × Bool)) (hFG : F ⊆ G) :
    (residueFamilyRestriction F G hFG).comp (residueFamilyHom data G) =
      residueFamilyHom data F := by
  ext x i
  rfl

/-- Equality of refined observations implies equality of the old observations. -/
theorem residueFamily_refines (data : SignedResidueData L)
    (F G : Finset (ℕ × Bool)) (hFG : F ⊆ G) {x y : L}
    (h : residueFamilyHom data G x = residueFamilyHom data G y) :
    residueFamilyHom data F x = residueFamilyHom data F y := by
  exact congrArg (residueFamilyRestriction F G hFG) h

variable {Ω : Type*} [Fintype Ω]

/-- Every finite-law residue observation is bounded by the exact sum of prime
logarithms, irrespective of dependencies between its coordinates. -/
theorem residueFamily_entropy_le (data : SignedResidueData L) (F : Finset (ℕ × Bool))
    (hF : ∀ i ∈ F, i.1 ∈ data.primes) (p : FinLaw Ω) (X : Ω → L) :
    p.Hf (fun ω => residueFamilyHom data F (X ω)) ≤ F.sum (fun i => Real.log i.1) := by
  let _ := residueFamilyFintype data F hF
  have h := p.Hf_le_log_card_type (fun ω => residueFamilyHom data F (X ω))
  rw [← Nat.card_eq_fintype_card, residueFamily_logCard data F hF] at h
  exact h

theorem residueFamily_entropy_mono (data : SignedResidueData L)
    (F G : Finset (ℕ × Bool)) (hFG : F ⊆ G) (p : FinLaw Ω) (X : Ω → L) :
    p.Hf (fun ω => residueFamilyHom data F (X ω)) ≤
      p.Hf (fun ω => residueFamilyHom data G (X ω)) := by
  exact p.Hf_le_of_determined _ _ (fun _ _ h => residueFamily_refines data F G hFG h)

/-- Conditioning on more actual prime residues decreases conditional entropy. -/
theorem residueFamily_conditional_entropy_mono {α : Type*}
    (data : SignedResidueData L) (F G : Finset (ℕ × Bool)) (hFG : F ⊆ G)
    (p : FinLaw Ω) (Y : Ω → α) (X : Ω → L) :
    p.cHf Y (fun ω => residueFamilyHom data G (X ω)) ≤
      p.cHf Y (fun ω => residueFamilyHom data F (X ω)) := by
  exact p.cHf_mono_of_refines _ _ _ (fun _ _ h => residueFamily_refines data F G hFG h)

/-- The entropy of one actual signed residue is at most `log p`. -/
theorem signedResidue_entropy_le (data : SignedResidueData L) {q : ℕ}
    (hq : q ∈ data.primes) (σ : Bool) (p : FinLaw Ω) (X : Ω → L) :
    p.Hf (fun ω => data.phi q σ (X ω)) ≤ Real.log q := by
  let _ : NeZero q := ⟨(data.prime_mem q hq).ne_zero⟩
  simpa only [ZMod.card] using p.Hf_le_log_card_type (fun ω => data.phi q σ (X ω))

/-- Finite batches use the literal enumeration of the selected prime set. -/
noncomputable def signedBatchIndex (S : Finset ℕ) : Fin S.card → S := S.equivFin.symm

noncomputable def signedBatchPrime (S : Finset ℕ) (i : Fin S.card) : ℕ :=
  (signedBatchIndex S i).val

theorem signedBatchPrime_mem (S : Finset ℕ) (i : Fin S.card) : signedBatchPrime S i ∈ S :=
  (signedBatchIndex S i).property

/-- The dependent residue alphabet of a genuine finite signed batch. -/
abbrev SignedBatchResidues (S : Finset ℕ) := (i : Fin S.card) → ZMod (signedBatchPrime S i)

noncomputable def signedBatchResidueHom (data : SignedResidueData L) (S : Finset ℕ)
    (σ : Fin S.card → Bool) : L →+ SignedBatchResidues S where
  toFun x i := data.phi (signedBatchPrime S i) (σ i) x
  map_zero' := by funext i; exact (data.phi _ _).map_zero
  map_add' x y := by funext i; exact (data.phi _ _).map_add x y

theorem signedBatchResidues_finite (data : SignedResidueData L) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q ∈ data.primes) : Finite (SignedBatchResidues S) := by
  let (i : Fin S.card) : NeZero (signedBatchPrime S i) :=
    ⟨(data.prime_mem _ (hS _ (signedBatchPrime_mem S i))).ne_zero⟩
  infer_instance

theorem signedBatchResidues_natCard (data : SignedResidueData L) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q ∈ data.primes) : Nat.card (SignedBatchResidues S) = S.prod id := by
  classical
  let (i : Fin S.card) : NeZero (signedBatchPrime S i) :=
    ⟨(data.prime_mem _ (hS _ (signedBatchPrime_mem S i))).ne_zero⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  simp only [ZMod.card]
  exact (S.equivFin.symm.prod_comp (fun q : S => q.val)).trans (Finset.prod_coe_sort S id)

/-- Natural-number coding of the actual residue coordinates for the common
alphabet required by the generic signed-entropy infrastructure. -/
noncomputable def signedResidueVector (data : SignedResidueData L) (S : Finset ℕ)
    (σ : Fin S.card → Bool) (x : L) : Fin S.card → ℕ :=
  fun i => (data.phi (signedBatchPrime S i) (σ i) x).val

theorem signedResidueVector_eq_iff (data : SignedResidueData L) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q ∈ data.primes) (σ : Fin S.card → Bool) {x y : L} :
    signedResidueVector data S σ x = signedResidueVector data S σ y ↔
      signedBatchResidueHom data S σ x = signedBatchResidueHom data S σ y := by
  constructor
  · intro h
    funext i
    let _ : NeZero (signedBatchPrime S i) :=
      ⟨(data.prime_mem _ (hS _ (signedBatchPrime_mem S i))).ne_zero⟩
    exact ZMod.val_injective _ (congrFun h i)
  · intro h
    funext i
    exact congrArg ZMod.val (congrFun h i)

theorem signedResidueVector_coordinate_entropy_le (data : SignedResidueData L)
    (S : Finset ℕ) (hS : ∀ q ∈ S, q ∈ data.primes) (σ : Fin S.card → Bool)
    (p : FinLaw Ω) (X : Ω → L) (i : Fin S.card) :
    p.Hf (fun ω => signedResidueVector data S σ (X ω) i) ≤ Real.log (signedBatchPrime S i) := by
  let _ : NeZero (signedBatchPrime S i) :=
    ⟨(data.prime_mem _ (hS _ (signedBatchPrime_mem S i))).ne_zero⟩
  have he : p.Hf (fun ω => signedResidueVector data S σ (X ω) i) =
      p.Hf (fun ω => data.phi (signedBatchPrime S i) (σ i) (X ω)) := by
    exact p.Hf_eq_of_fibers _ _ (fun _ _ => (ZMod.val_injective _).eq_iff)
  rw [he]
  exact signedResidue_entropy_le data (hS _ (signedBatchPrime_mem S i)) (σ i) p X

/-- The genuine finite-law signed point entropy, averaged over actual signs
and permutations of the finite batch as in the upstream enrichment method. -/
noncomputable def signedPointEntropy (data : SignedResidueData L) (S : Finset ℕ)
    (p : FinLaw Ω) (X : Ω → L) (s : ℕ) : ℝ :=
  p.signedEntropy (fun σ ω => signedResidueVector data S σ (X ω)) s

@[simp] theorem signedPointEntropy_zero (data : SignedResidueData L) (S : Finset ℕ)
    (p : FinLaw Ω) (X : Ω → L) : signedPointEntropy data S p X 0 = 0 := by
  simp [signedPointEntropy]

theorem signedPointEntropy_slope (data : SignedResidueData L) (S : Finset ℕ)
    (p : FinLaw Ω) (X : Ω → L) {s : ℕ} (hs : 0 < s) (hsk : s < S.card) :
    signedPointEntropy data S p X (s + 1) - signedPointEntropy data S p X s ≤
      signedPointEntropy data S p X s / s :=
  p.signedEntropy_slope _ hs hsk

end Entry002
