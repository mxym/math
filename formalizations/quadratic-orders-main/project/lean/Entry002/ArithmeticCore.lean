import Entry002.ArithmeticInterface

/-! The literal first four arithmetic conditions. This new interface permits
the weaker supply route without inventing the old natural-density field.
No generalized finite-sieve endpoint is asserted in this module. -/

namespace Entry002

open Module

variable {L : Type*} [AddCommGroup L]

/-- Exactly A1--A4 of the original arithmetic interface, with no supply
condition. All maps and geometric estimates retain their original meaning. -/
structure ArithmeticCore (data : SignedResidueData L)
    (b : Basis (Fin 2) ℤ L) (e : CoeffSpace ≃ₗ[ℝ] Plane) : Prop where
  crt : ∀ (S : Finset ℕ), (∀ p ∈ S, p ∈ data.primes) → ∀ σ : ℕ → Bool,
    Function.Surjective (fun x : L => fun p : S => data.phi p.val (σ p.val) x)
  paired_kernel : ∀ p ∈ data.primes, ∀ x : L,
    (data.phi p true x = 0 ∧ data.phi p false x = 0) ↔
      ∃ y : L, x = (p : ℤ) • y
  collision : ∃ c : ℝ, 0 < c ∧ ∀ p ∈ data.primes, ∀ σ : Bool, ∀ x : L,
    x ≠ 0 → data.phi p σ x = 0 →
      c * Real.sqrt (p : ℝ) ≤ ‖planarEmbedding b e x‖
  eligible_product : ∃ C : ℝ, 1 ≤ C ∧ ∀ v : L, IsPrimitive v →
    ∀ S : Finset ℕ, (∀ p ∈ S, p ∈ data.primes) →
      ((S.filter (fun p => data.phi p true v = 0 ∨ data.phi p false v = 0)).prod
        (fun p => (p : ℝ))) ≤ C * ‖planarEmbedding b e v‖ ^ 2

theorem ArithmeticInterface.toArithmeticCore
    {data : SignedResidueData L} {b : Basis (Fin 2) ℤ L}
    {e : CoeffSpace ≃ₗ[ℝ] Plane} (A : ArithmeticInterface data b e) :
    ArithmeticCore data b e :=
  ⟨A.crt, A.paired_kernel, A.collision, A.eligible_product⟩

/-- For every positive conductor in every real or imaginary quadratic number
field, the actual principal norm-prime residue witnesses prove A1--A4.
The theorem does not ask for or prove a natural-density field. -/
theorem order_core_of_principal_residues
    (K : Type*) [Field K] [NumberField K] (f : ℕ)
    (hK : Module.finrank ℚ K = 2) (hf : 0 < f)
    (b : Basis (Fin 2) ℤ (conductorOrder K f)) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (data : SignedResidueData (conductorOrder K f))
    (α : ℕ → Bool → conductorOrder K f)
    (hnorm : ∀ p ∈ data.primes, ∀ s : Bool, (Algebra.norm ℤ (α p s)).natAbs = p)
    (hkernel : ∀ p ∈ data.primes, ∀ s : Bool, ∀ x : conductorOrder K f,
      data.phi p s x = 0 ↔ α p s ∣ x)
    (hpair : ∀ p ∈ data.primes, ∀ x : conductorOrder K f,
      (data.phi p true x = 0 ∧ data.phi p false x = 0) ↔
        ∃ y : conductorOrder K f, x = (p : ℤ) • y) : ArithmeticCore data b e := by
  have hdiv : ∀ p ∈ data.primes, ∀ σ : Bool, ∀ x : conductorOrder K f,
      data.phi p σ x = 0 → p ∣ (Algebra.norm ℤ x).natAbs := by
    intro p hp σ x hx
    have hd := natAbs_order_norm_dvd_of_dvd ((hkernel p hp σ x).mp hx)
    rwa [hnorm p hp σ] at hd
  obtain ⟨hcollision, hproduct⟩ :=
    conductorOrder_collision_and_product K f hK hf b e data hdiv
  exact ⟨signedResidueData_crt data, hpair, hcollision, hproduct⟩

end Entry002
