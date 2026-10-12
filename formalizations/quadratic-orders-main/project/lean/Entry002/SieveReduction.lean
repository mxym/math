import Entry002.PeriodicComponents
import Entry002.TinySteps

/-! Exact reduction of the all-lattice finite-sieve target to its analytic
no-infinite-walk part. These are implications/equivalences, not a proof of
either still-open universal target. The `Q²` bound is derived by true lattice
periodicity and König's lemma, with no component finiteness assumption. -/
set_option autoImplicit false
open Module
namespace Entry002

/-- The still-open analytic heart of the manuscript's generic sieve theorem.
The finite prime selection is made before quantifying over all walks. -/
def FiniteSieveNoWalkTarget : Prop :=
  ∀ (L : Type) [AddCommGroup L]
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (data : SignedResidueData L), ArithmeticInterface data b e →
  ∀D : ℝ, 0≤D → ∃S : Finset ℕ,
    (∀p∈S, p∈data.primes) ∧
    ∀w : ℕ → avoiding data S, Function.Injective w →
      (∀n, (latticeGraph b e D (avoiding data S)).Adj (w n) (w (n+1))) → False

theorem finiteSieveTarget_iff_noWalkTarget : FiniteSieveTarget ↔ FiniteSieveNoWalkTarget := by
  constructor
  · intro h L _ b e data hA D hD
    obtain ⟨S,hS,hB⟩ := h L b e data hA D hD
    refine ⟨S,hS,?_⟩
    intro w hinj hstep
    exact no_infinite_injective_walk _ hB w hstep hinj
  · intro h L _ b e data hA D hD
    obtain ⟨S,hS,hno⟩ := h L b e data hA D hD
    exact ⟨S,hS,avoiding_component_bound_of_no_infinite_walk b e data S hS D hno⟩

/-- Uniform selection for all sufficiently large step bounds suffices for the
complete finite sieve. A sieve valid at a larger bound also forbids every
walk at the requested smaller bound. -/
theorem finiteSieveTarget_of_large_step_no_walk
    (hlarge : ∀ (L : Type) [AddCommGroup L]
      (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane)
      (data : SignedResidueData L), ArithmeticInterface data b e →
      ∃δ : ℝ, 0<δ ∧
        (∀D : ℝ, δ≤D → ∃S : Finset ℕ,
          (∀p∈S, p∈data.primes) ∧
          ∀w : ℕ → avoiding data S, Function.Injective w →
            (∀n, (latticeGraph b e D (avoiding data S)).Adj (w n) (w (n+1))) → False)) :
    FiniteSieveTarget := by
  apply finiteSieveTarget_iff_noWalkTarget.mpr
  intro L _ b e data hA D _
  obtain ⟨δ,_,hbig⟩ := hlarge L b e data hA
  obtain ⟨S,hS,hno⟩ := hbig (max D δ) (le_max_right _ _)
  refine ⟨S,hS,?_⟩
  intro w hinj hstep
  apply hno w hinj
  intro n
  exact ⟨(hstep n).1,(hstep n).2.trans (le_max_left _ _)⟩

end Entry002
