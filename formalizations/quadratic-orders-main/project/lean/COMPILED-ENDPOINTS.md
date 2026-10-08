# Actual compiled endpoints, round 5

The unchanged all-quadratic-orders `MainTarget` is proved by the separately
audited external endpoint below. Both exact weak-sieve targets and the
all-conductor weak principal supply are closed. The original strong natural
density supply and universal natural number-field prime-ideal PNT remain open.

`overall-verification.json` combines the two projects; `verification.json`
reports only the mathlib-only main library. Official pinned artifacts and
the pinned precompiled class-field closure remain trusted inputs. No second
kernel, full mathlib rebuild, or fresh 995-module CFT rebuild is claimed.

## Entry002.arithmeticSupply_mainTarget_proved

```lean
Entry002.MainTarget
```

Stored type/body closure: 125368 declarations.
Logical axioms: propext, Classical.choice, Quot.sound.

## Entry002.arithmeticSupply_weakPrincipalSupply_from_Dirichlet

```lean
Entry002.WeakPrincipalSplitPrimeSupplyTarget
```

Stored type/body closure: 121469 declarations.
Logical axioms: propext, Classical.choice, Quot.sound.

## Entry002.weakFiniteSieveTarget_proved

```lean
Entry002.WeakFiniteSieveTarget
```

Stored type/body closure: 52278 declarations.
Logical axioms: propext, Classical.choice, Quot.sound.

## Entry002.weakFiniteSieveNoWalkTarget_proved

```lean
Entry002.WeakFiniteSieveNoWalkTarget
```

Stored type/body closure: 52296 declarations.
Logical axioms: propext, Classical.choice, Quot.sound.

## Entry002.positiveUpperLogGoodBinSupply_of_positiveUpperDirichletSupply

```lean
∀ (P : Set ℕ),
  (∀ p ∈ P, Nat.Prime p) → Entry002.PositiveUpperDirichletSupply P → Entry002.PositiveUpperLogGoodBinSupply P
```

Stored type/body closure: 18156 declarations.
Logical axioms: propext, Classical.choice, Quot.sound.

## Entry002.WeakA5.core_finite_sieve_of_log_good_bins

```lean
∀ {L : Type u_1} [inst : AddCommGroup L] {data : Entry002.SignedResidueData L} {b : Module.Basis (Fin 2) ℤ L}
  {e : Entry002.CoeffSpace ≃ₗ[ℝ] Entry002.Plane},
  Entry002.ArithmeticCore data b e →
    Entry002.PositiveUpperLogGoodBinSupply data.primes →
      ∀ (D : ℝ),
        0 ≤ D →
          ∃ S,
            (∀ p ∈ S, p ∈ data.primes) ∧
              Entry002.UniformComponentBound (Entry002.latticeGraph b e D (Entry002.avoiding data S)) (S.prod id ^ 2)
```

Stored type/body closure: 52175 declarations.
Logical axioms: propext, Classical.choice, Quot.sound.

## Entry002.completelySplittingRationalPrimes_aboveCutoff_positiveUpperDirichletSupply

```lean
∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] [IsGalois ℚ K] (f : ℕ),
  Entry002.PositiveUpperDirichletSupply {p | p ∈ Entry002.completelySplittingRationalPrimes K ∧ f < p}
```

Stored type/body closure: 75524 declarations.
Logical axioms: propext, Classical.choice, Quot.sound.

## Entry002.completelySplittingRationalPrimes_DirichletSeries_normalized_tendsto

```lean
∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] [IsGalois ℚ K],
  Filter.Tendsto
    (fun s =>
      Entry002.supplyPrimeDirichletSeries (Entry002.completelySplittingRationalPrimes K) s / Real.log (1 / (s - 1)))
    (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 / ↑(Module.finrank ℚ K)))
```

Stored type/body closure: 75512 declarations.
Logical axioms: propext, Classical.choice, Quot.sound.

## Entry002.actualDedekindZeta_real_log_eq_eulerLog

```lean
∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] {s : ℝ},
  1 < s →
    Real.log (NumberField.dedekindZeta K ↑s).re = (LSeries (fun n => ↑(Entry002.primeIdealLogCoefficient K n)) ↑s).re
```

Stored type/body closure: 70734 declarations.
Logical axioms: propext, Classical.choice, Quot.sound.

## Entry002.idealNormCoefficient_log_eq_convolution

```lean
∀ (K : Type u_1) [inst : Field K] [inst_1 : NumberField K] (n : ℕ),
  Entry002.idealNormCoefficient K n * Real.log ↑n =
    LSeries.convolution (Entry002.idealNormCoefficient K) (Entry002.primeIdealVonMangoldt K) n
```

Stored type/body closure: 35200 declarations.
Logical axioms: propext, Classical.choice, Quot.sound.

## Entry002.finiteSieveTarget_proved

```lean
Entry002.FiniteSieveTarget
```

Stored type/body closure: 52086 declarations.
Logical axioms: propext, Classical.choice, Quot.sound.

## Entry002.finiteSieveNoWalkTarget_proved

```lean
Entry002.FiniteSieveNoWalkTarget
```

Stored type/body closure: 52087 declarations.
Logical axioms: propext, Classical.choice, Quot.sound.

## Entry002.mainTarget_of_principalPrimeSupply

```lean
Entry002.PrincipalSplitPrimeSupplyTarget → Entry002.MainTarget
```

Stored type/body closure: 60284 declarations.
Logical axioms: propext, Classical.choice, Quot.sound.

## Entry002.mainTarget_of_weak_supply_and_weak_finiteSieve

```lean
Entry002.WeakPrincipalSplitPrimeSupplyTarget → Entry002.WeakFiniteSieveTarget → Entry002.MainTarget
```

Stored type/body closure: 55637 declarations.
Logical axioms: propext, Classical.choice, Quot.sound.
