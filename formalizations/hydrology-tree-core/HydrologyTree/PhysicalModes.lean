import HydrologyTree.StieltjesNumerator
import HydrologyTree.TreeCancellation

/-! Full positive-mode classification in terms of the original tree's actual
sibling principal spectra. This is not a substitute for the still separate
coefficient-Jacobian singularity or ODE controllability statements. -/
open Polynomial
noncomputable section
namespace HydrologyTree

/-- No pole cancellation in the actual unreduced physical polynomials. -/
def NoRealPhysicalCancellation {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : Prop :=
  ∀ z : ℝ, (physicalCharacteristic t x).eval z = 0 →
    (physicalRootCofactor t x).eval z ≠ 0

lemma physicalCommonRoot_real {n : ℕ} (t : OrderedTree n) (x : TreeRates n) (z : ℝ) :
    PhysicalCommonRoot t x z ↔
      (physicalRootCofactor t x).eval z = 0 ∧ (physicalCharacteristic t x).eval z = 0 := by
  simp [PhysicalCommonRoot, Polynomial.aeval_def]

/-- The common-root theorem now gives a noncancellation statement on actual
real principal spectra, without any assumed stability or minimality bridge. -/
theorem noCancellation_iff_noSiblingCollision {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hx : NonzeroTreeEdges x) :
    NoRealPhysicalCancellation t x ↔ ∀ z : ℝ, ¬SiblingCollisionSomewhere t x z := by
  constructor
  · intro h z hz
    have hh := (physicalCommonRoot_real t x z).mp
      ((physicalCommonRoot_iff_siblingCollision t x hx z).mpr hz)
    exact h z hh.2 hh.1
  · intro h z hp hf
    apply h z
    apply (physicalCommonRoot_iff_siblingCollision t x hx z).mp
    exact (physicalCommonRoot_real t x z).mpr ⟨hf,hp⟩

/-- The exact full-size Stieltjes class: all n+1 distinct poles have strictly
positive weights; BOTH unreduced polynomials must equal the displayed formulas. -/
def FullPositiveModes {n : ℕ} (t : OrderedTree n) (x : TreeRates n) : Prop :=
  ∃ r w : Fin (n+1) → ℝ, (∀ i, 0 < r i) ∧ Function.Injective r ∧
    (∀ i, 0 < w i) ∧ (∑ i, w i)=1 ∧
      physicalCharacteristic t x = stieltjesDenominator r ∧
      physicalRootCofactor t x = stieltjesNumerator r w

/-- Positive physical parameters plus noncancellation give the full simple
positive-mode class, rather than assuming simple poles or positive residues. -/
theorem fullPositiveModes_of_noncancellation {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hell : 0 < x.1 0) (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e)
    (h : NoRealPhysicalCancellation t x) : FullPositiveModes t x := by
  obtain ⟨r,w,hr,hw,hm,hP,hF⟩ := physical_stieltjes_polynomials t x hell ha hf
  have hnc : ∀ z : ℝ, (stieltjesDenominator r).eval z = 0 →
      (stieltjesNumerator r w).eval z ≠ 0 := by
    intro z hz
    rw [← hP] at hz
    rw [← hF]
    exact h z hz
  obtain ⟨hinj,hwn⟩ := stieltjes_noncancellation_forces_modes r w hnc
  exact ⟨r,w,hr,hinj,fun i => lt_of_le_of_ne (hw i) (Ne.symm (hwn i)),hm,hP,hF⟩

/-- Full-size positive modes rule out actual common roots, with no regularity
assumption on a coefficient Jacobian. -/
theorem fullPositiveModes_noncancellation {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (h : FullPositiveModes t x) : NoRealPhysicalCancellation t x := by
  obtain ⟨r,w,hr,hinj,hw,hm,hP,hF⟩ := h
  intro z hz
  rw [hP] at hz
  rw [hF]
  exact stieltjes_modes_force_noncancellation r w hinj (fun i => ne_of_gt (hw i)) z hz

/-- Complete all-size positive-mode/collision equivalence for the ACTUAL tree.
Repeated poles or invisible modes occur precisely when a sibling spectral
collision occurs somewhere in the original tree. -/
theorem physical_full_modes_iff_no_sibling_collisions {n : ℕ} (t : OrderedTree n) (x : TreeRates n)
    (hell : 0 < x.1 0) (ha : ∀ e : Fin n, 0 < x.1 e.succ) (hf : ∀ e : Fin n, 0 < x.2 e) :
    FullPositiveModes t x ↔ ∀ z : ℝ, ¬SiblingCollisionSomewhere t x z := by
  have hx : NonzeroTreeEdges x := ⟨fun i => ne_of_gt (ha i), fun i => ne_of_gt (hf i)⟩
  rw [← noCancellation_iff_noSiblingCollision t x hx]
  exact ⟨fullPositiveModes_noncancellation t x,
    fullPositiveModes_of_noncancellation t x hell ha hf⟩

end HydrologyTree
