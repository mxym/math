import Entry002.Sieve
import Entry002.NormBound
import Entry002.CRT

/-! Actual A3–A4 instantiation for every quadratic conductor order. Principal
kernel norm divisibility is explicit; the quadratic geometric estimate is proved.
The prime supply, CRT, paired kernels, and A5 density remain separate targets. -/
set_option autoImplicit false
open Module
namespace Entry002

/-- The real geometric collision and eligible-product conditions follow for
all conductor orders from the genuine integer-norm divisibility of the kernels. -/
theorem conductorOrder_collision_and_product
    (K : Type*) [Field K] [NumberField K] (f : ℕ)
    (hK : Module.finrank ℚ K = 2) (hf : 0 < f)
    (b : Basis (Fin 2) ℤ (conductorOrder K f)) (e : CoeffSpace ≃ₗ[ℝ] Plane)
    (data : SignedResidueData (conductorOrder K f))
    (hdiv : ∀ p ∈ data.primes, ∀ σ : Bool, ∀ x : conductorOrder K f,
      data.phi p σ x = 0 → p ∣ (Algebra.norm ℤ x).natAbs) :
    (∃ c : ℝ, 0 < c ∧ ∀ p ∈ data.primes, ∀ σ : Bool,
      ∀ x : conductorOrder K f, x ≠ 0 → data.phi p σ x = 0 →
        c * Real.sqrt (p : ℝ) ≤ ‖planarEmbedding b e x‖) ∧
    (∃ C : ℝ, 1 ≤ C ∧ ∀ v : conductorOrder K f, IsPrimitive v →
      ∀ S : Finset ℕ, (∀ p ∈ S, p ∈ data.primes) →
        ((S.filter (fun p => data.phi p true v = 0 ∨ data.phi p false v = 0)).prod
          (fun p => (p : ℝ))) ≤ C * ‖planarEmbedding b e v‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_order_norm_bound K f hK hf b e
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hnat (x : conductorOrder K f) :
      ((Algebra.norm ℤ x).natAbs : ℝ) ≤ C * ‖planarEmbedding b e x‖ ^ 2 := by
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hbound x
  constructor
  · refine ⟨(Real.sqrt C)⁻¹, inv_pos.mpr (Real.sqrt_pos.mpr hCpos), ?_⟩
    intro p hp σ x hx hphi
    have h := norm_collision_lower_bound hx (hdiv p hp σ x hphi)
      hCpos (norm_nonneg _) (hnat x)
    simpa only [div_eq_inv_mul] using h
  · refine ⟨C, hC, ?_⟩
    intro v hv S hS
    apply norm_prime_product_bound _ hv.1
    · intro p hp
      exact data.prime_mem p (hS p (Finset.mem_filter.mp hp).1)
    · intro p hp
      obtain ⟨hpS, hz⟩ := Finset.mem_filter.mp hp
      exact hz.elim (hdiv p (hS p hpS) true v) (hdiv p (hS p hpS) false v)
    · exact hnat v

/-- The complete A1–A5 interface is verified for actual principal norm-prime
residues once their genuinely separate supply/intersection/density data are
provided. No class-field theorem or density premise is disguised as a proof. -/
theorem order_interface_of_principal_residues
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
        ∃ y : conductorOrder K f, x = (p : ℤ) • y)
    (hdensity : ∃ ρ : ℝ, 0 < ρ ∧ Filter.Tendsto
      (fun T : ℝ => (dyadicPrimeCount data.primes T : ℝ) / (T / Real.log T))
      Filter.atTop (nhds ρ)) : ArithmeticInterface data b e := by
  have hdiv : ∀ p ∈ data.primes, ∀ σ : Bool, ∀ x : conductorOrder K f,
      data.phi p σ x = 0 → p ∣ (Algebra.norm ℤ x).natAbs := by
    intro p hp σ x hx
    have hd := natAbs_order_norm_dvd_of_dvd ((hkernel p hp σ x).mp hx)
    rwa [hnorm p hp σ] at hd
  obtain ⟨hcollision, hproduct⟩ := conductorOrder_collision_and_product K f hK hf b e data hdiv
  exact ⟨signedResidueData_crt data, hpair, hcollision, hproduct, hdensity⟩

end Entry002
