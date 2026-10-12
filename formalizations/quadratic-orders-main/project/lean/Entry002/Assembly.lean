import Entry002.PrimeSupply
import Entry002.ArithmeticInterface
import Entry002.OrderRestoration

/-! End-to-end assembly with its TWO OPEN foundations displayed as hypotheses.
This file proves a conditional reduction, never an unconditional MainTarget.
The ray-class prime supply and analytic finite-sieve theorem remain unproved.
-/
set_option autoImplicit false
open Module
namespace Entry002

/-- The exact all-order main target follows from the two explicitly OPEN
mathematical foundations. They are arguments, not imported axioms or theorems.
This conditional reduction is not a proof of either premise or of MainTarget. -/
theorem mainTarget_of_supply_and_finiteSieve
    (hsupply : PrincipalSplitPrimeSupplyTarget) (hsieve : FiniteSieveTarget) : MainTarget := by
  intro K _ _ hK f hf b e D hD
  classical
  obtain ⟨data, α, τ, hτ, hnormkernel, hconj, hpair, hring, hdensity⟩ := hsupply K hK f hf
  have hinterface := order_interface_of_principal_residues K f hK hf b e data α
    (fun p hp s => (hnormkernel p hp s).1)
    (fun p hp s => (hnormkernel p hp s).2) hpair hdensity
  obtain ⟨S, hS, hB⟩ := hsieve (conductorOrder K f) b e data hinterface D hD
  let generators : Finset (conductorOrder K f) :=
    S.biUnion (fun p => {α p true, α p false})
  have hgen : ∀ a ∈ generators, ¬ IsUnit a := by
    intro a ha
    obtain ⟨p, hp, ha⟩ := Finset.mem_biUnion.mp ha
    have hp' := data.prime_mem p (hS p hp)
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · exact nonunit_of_natAbs_normHom_ne_one (Algebra.norm ℤ)
        (by rw [(hnormkernel p (hS p hp) true).1]; exact hp'.ne_one)
    · exact nonunit_of_natAbs_normHom_ne_one (Algebra.norm ℤ)
        (by rw [(hnormkernel p (hS p hp) false).1]; exact hp'.ne_one)
  have hav : avoiding data S =
      {x : conductorOrder K f | ∀ a ∈ generators, ¬ a ∣ x} := by
    ext x
    constructor
    · intro hx a ha
      obtain ⟨p, hp, ha⟩ := Finset.mem_biUnion.mp ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl
      · intro hd
        exact (hx p hp).1 (((hnormkernel p (hS p hp) true).2 x).mpr hd)
      · intro hd
        exact (hx p hp).2 (((hnormkernel p (hS p hp) false).2 x).mpr hd)
    · intro hx p hp
      constructor
      · intro hz
        exact hx (α p true) (Finset.mem_biUnion.mpr ⟨p, hp, by simp⟩)
          (((hnormkernel p (hS p hp) true).2 x).mp hz)
      · intro hz
        exact hx (α p false) (Finset.mem_biUnion.mpr ⟨p, hp, by simp⟩)
          (((hnormkernel p (hS p hp) false).2 x).mp hz)
  rw [hav] at hB
  obtain ⟨Bfull, hfull⟩ := quadraticOrder_restoration_of_principal_sieve K f hK hf b e hD
    generators hgen hB
  refine ⟨Bfull, hfull, ?_, ?_⟩
  · intro n w hi hw
    exact finite_injective_walk_terms_le (primeGraph b e D) hfull w hi hw
  · intro w hi hw
    exact no_infinite_injective_walk (primeGraph b e D) hfull w hw hi

end Entry002
