import Entry002.Sieve
import Mathlib.Data.Nat.ChineseRemainder

/-! The manuscript's A1 follows from the actual surjective additive prime
residue maps. Integer CRT selectors isolate each selected map. -/

namespace Entry002

open scoped BigOperators

/-- A scalar which is one at the selected prime and zero at all other
selected primes. This is the ordinary finite Chinese remainder theorem. -/
theorem prime_crt_selector (S : Finset ℕ) (hprime : ∀ q ∈ S, Nat.Prime q)
    (p : ℕ) : ∃ c : ℕ, ∀ q ∈ S, (c : ZMod q) = if q = p then 1 else 0 := by
  classical
  let c := Nat.chineseRemainderOfFinset (fun q => if q = p then 1 else 0) id S
    (fun q hq => (hprime q hq).ne_zero)
    (fun q hq r hr hqr => (Nat.coprime_primes (hprime q hq) (hprime r hr)).mpr hqr)
  refine ⟨c.val, ?_⟩
  intro q hq
  have hc := (ZMod.natCast_eq_natCast_iff c.val (if q = p then 1 else 0) q).mpr
    (c.property q hq)
  simpa using hc

/-- Joint surjectivity of all selected signed residue coordinates, for every
finite set of distinct actual rational primes. No ring structure on the
domain is needed. -/
theorem signedResidueData_crt {L : Type*} [AddCommGroup L]
    (data : SignedResidueData L) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p ∈ data.primes) (σ : ℕ → Bool) :
    Function.Surjective (fun x : L => fun p : S => data.phi p.val (σ p.val) x) := by
  classical
  intro z
  choose y hy using fun p : S => data.onto p.val (hS p.val p.property) (σ p.val) (z p)
  choose c hc using fun p : S => prime_crt_selector S
    (fun q hq => data.prime_mem q (hS q hq)) p.val
  refine ⟨∑ p : S, c p • y p, ?_⟩
  funext q
  change data.phi q.val (σ q.val) (∑ p : S, c p • y p) = z q
  rw [map_sum]
  have hsum : (∑ p : S, data.phi q.val (σ q.val) (c p • y p)) =
      ∑ p : S, if p = q then z q else 0 := by
    apply Finset.sum_congr rfl
    intro p hp
    rw [map_nsmul, nsmul_eq_mul, hc p q.val q.property]
    by_cases hpq : p = q
    · subst p
      simp [hy q]
    · have hval : q.val ≠ p.val := fun h => hpq (Subtype.ext h.symm)
      simp [hpq, hval]
  rw [hsum]
  simp

end Entry002
