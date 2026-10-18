import CircuitRecursion.NumericalDependencies
import Mathlib.Data.Vector.Mem

namespace CircuitRecursion

/-- Every source query is paired with its precision in the stored vector.
This is the abstract evaluation trace of the eager packet-cache builder. -/
def buildPacketCache (f : QuaternionOracle) (P : ℕ) :
    List.Vector (List.Vector ℚ 4) (P+1) × List ℕ :=
  let queried := List.Vector.ofFn (fun i : Fin (P+1) => (f i.val,i.val))
  (queried.map Prod.fst,queried.toList.map Prod.snd)

def readPacketCache {P : ℕ} (cache : List.Vector (List.Vector ℚ 4) (P+1)) : QuaternionOracle := fun p =>
  if hp : p≤P then cache.get ⟨p,by omega⟩ else quaternionOracleOne p

theorem buildPacketCache_agrees (f : QuaternionOracle) (P : ℕ) :
    AgreesThrough (readPacketCache (buildPacketCache f P).1) f P := by
  intro p hp
  simp [readPacketCache,buildPacketCache,hp]

theorem buildPacketCache_requests (f : QuaternionOracle) (P : ℕ) :
    (buildPacketCache f P).2.length=P+1 := by
  simp [buildPacketCache]

theorem buildPacketCache_precision (f : QuaternionOracle) (P q : ℕ)
    (hq : q∈(buildPacketCache f P).2) : q≤P := by
  simp only [buildPacketCache,List.mem_map] at hq
  obtain ⟨v,hv,he⟩ := hq
  obtain ⟨i,hi⟩ := (List.Vector.mem_iff_get v _).mp hv
  have h : v.2=i.val := by
    rw [← hi]
    simp only [List.Vector.get_ofFn]
  omega

structure CachedWordResult (m : ℕ) where
  word : List (Fin m)
  gateRequests : List (Fin m×ℕ)
  targetRequests : List ℕ

/-- This implementation eagerly materializes every gate and target packet
through the proved dependency bound. Subsequent calls read stored packets.
It deliberately makes the memoization policy part of the finite program. -/
def cachedNumericalRun {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (target : QuaternionOracle) : CachedWordResult m :=
  let depth := Nat.clog 2 (p+1)
  let P := numericalDemand L depth
  let gateCache := List.Vector.ofFn (fun i : Fin m => buildPacketCache (entry i) P)
  let targetCache := buildPacketCache target P
  let word := numericalPairWord (fun i => readPacketCache (gateCache.get i).1)
    inverseLabel table depth (readPacketCache targetCache.1)
  let gates := (List.finRange m).flatMap
    (fun i => ((gateCache.get i).2).map (fun q => (i,q)))
  ⟨word,gates,targetCache.2⟩

theorem cachedNumericalRun_word {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (hL : ∀ j,(table j).length≤L) (f : QuaternionOracle) :
    (cachedNumericalRun entry inverseLabel table L p f).word=
      numericalPairWord entry inverseLabel table (Nat.clog 2 (p+1)) f := by
  apply numericalPairWord_agrees _ _ inverseLabel table L hL (Nat.clog 2 (p+1))
  · intro i
    simpa only [List.Vector.get_ofFn] using
      buildPacketCache_agrees (entry i) (numericalDemand L (Nat.clog 2 (p+1)))
  · exact buildPacketCache_agrees f _

theorem cachedNumericalRun_gateRequests {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (f : QuaternionOracle) :
    (cachedNumericalRun entry inverseLabel table L p f).gateRequests.length=
      m*(numericalDemand L (Nat.clog 2 (p+1))+1) := by
  simp [cachedNumericalRun,List.length_flatMap,buildPacketCache_requests]

theorem cachedNumericalRun_targetRequests {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ) (f : QuaternionOracle) :
    (cachedNumericalRun entry inverseLabel table L p f).targetRequests.length=
      numericalDemand L (Nat.clog 2 (p+1))+1 := by
  exact buildPacketCache_requests f _

theorem cachedNumericalRun_gatePrecision {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (f : QuaternionOracle) (x : Fin m×ℕ)
    (hx : x∈(cachedNumericalRun entry inverseLabel table L p f).gateRequests) :
    x.2≤numericalDemand L (Nat.clog 2 (p+1)) := by
  obtain ⟨i,hi,hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨q,hq,hx⟩ := List.mem_map.mp hx
  subst x
  simp only [List.Vector.get_ofFn] at hq
  exact buildPacketCache_precision (entry i) _ q hq

theorem cachedNumericalRun_targetPrecision {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (f : QuaternionOracle) (q : ℕ)
    (hq : q∈(cachedNumericalRun entry inverseLabel table L p f).targetRequests) :
    q≤numericalDemand L (Nat.clog 2 (p+1)) := buildPacketCache_precision f _ q hq

/-- Correctness of the actual cached word, with the same inverse-closed
universal-library inputs as the earlier numerical algorithm. Provider
execution costs and internal arithmetic bit costs remain separate. -/
theorem cachedNumericalSU2Synthesis {m : ℕ} (G : Fin m → SU2)
    (hinv : ∀ i,∃ j,G j=(G i)⁻¹)
    (huniversal : Dense (Subgroup.closure (Set.range G) : Set SU2)) :
    ∃ (L n : ℕ) (table : Fin (n+1) → List (Fin m)),
      ∀ (entry : Fin m → QuaternionOracle), (∀ i,QApproximates (entry i) (G i)) →
      ∀ (inverseLabel : Fin m → Fin m), (∀ i,G (inverseLabel i)=(G i)⁻¹) →
      ∀ (p : ℕ) (U : SU2) (f : QuaternionOracle),QApproximates f U →
        (cachedNumericalRun entry inverseLabel table L p f).word.length≤32*L*(p+1)^5 ∧
        unitaryDistance (su2AsUnitary U) (su2AsUnitary (instructionWordValue G
          (cachedNumericalRun entry inverseLabel table L p f).word))≤(1/2:ℝ)^p := by
  obtain ⟨L,n,table,hL,hcover⟩ := precomputedNet_exists G hinv huniversal
  refine ⟨L,n,table,fun entry he inverseLabel hi p U f hf => ?_⟩
  rw [cachedNumericalRun_word entry inverseLabel table L p hL f]
  constructor
  · have ht := numericalPairWord_length entry inverseLabel table L hL (Nat.clog 2 (p+1)) f
    have hp := Nat.mul_le_mul_left L (precisionDepth_length p)
    exact ht.trans (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hp)
  · have ht := numericalPairWord_error entry G he inverseLabel hi table hcover (Nat.clog 2 (p+1)) U f hf
    have hp : p≤2^Nat.clog 2 (p+1) := (Nat.le_succ p).trans (Nat.le_pow_clog (by decide) (p+1))
    exact ht.trans (skPairError_precision _ p hp)

end CircuitRecursion
