import EffectiveEncoding.FiniteLabels
import CircuitNumerical.CachedArithmeticSynthesis

open scoped BigOperators Matrix.Norms.L2Operator
open CircuitCompletion CircuitRecursion SymmetricSupport Matrix
namespace EffectiveEncoding

/-- The actual numerical synthesis reads the computed packet of this
particular gate descriptor. No semantic U2 matrix is inspected. -/
def descriptorSynthesis {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (u : SingleCode) : List (Fin m) :=
  (cachedArithmeticRun entry inverseLabel table L p u.quaternionOracle).word

theorem descriptorSynthesis_spec {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → QuaternionOracle) (he : ∀ i,QApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (p : ℕ) (u : SingleCode) :
    (descriptorSynthesis entry inverseLabel table L p u).length≤32*L*(p+1)^5 ∧
      unitaryDistance (su2AsUnitary u.representative)
        (su2AsUnitary (instructionWordValue G (descriptorSynthesis entry inverseLabel table L p u)))≤
          (1/2:ℝ)^p := by
  have hw : descriptorSynthesis entry inverseLabel table L p u=
      numericalPairWord entry inverseLabel table (Nat.clog 2 (p+1)) u.quaternionOracle :=
    (cachedArithmeticRun_word entry inverseLabel table L p u.quaternionOracle).trans
      (cachedNumericalRun_word entry inverseLabel table L p hL u.quaternionOracle)
  rw [hw]
  constructor
  · have ht := numericalPairWord_length entry inverseLabel table L hL (Nat.clog 2 (p+1)) u.quaternionOracle
    have hp := Nat.mul_le_mul_left L (precisionDepth_length p)
    exact ht.trans (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hp)
  · have ht := numericalPairWord_error entry G he inverseLabel hi table hcover
      (Nat.clog 2 (p+1)) u.representative u.quaternionOracle u.quaternionOracle_correct
    have hp : p≤2^Nat.clog 2 (p+1) := (Nat.le_succ p).trans (Nat.le_pow_clog (by decide) (p+1))
    exact ht.trans (skPairError_precision _ p hp)

def extractionPrecision (k p : ℕ) : ℕ :=
  dyadicCircuitPrecision (extractionCode k).length (p+1)

/-- A literal finite dictionary-label/CNOT program on the original wires.
Its only provider input is the fixed dictionary's numerical entry routine. -/
def numericalExtractionCode {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : List (LabelGate m (originalWireCount k)) :=
  let w := extractionCode k
  let q := dyadicCircuitPrecision w.length (p+1)
  compileLabelWord (descriptorSynthesis entry inverseLabel table L q) w

theorem numericalExtractionCode_uses {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → QuaternionOracle) (inverseLabel : Fin m → Fin m)
    (table : Fin (n+1) → List (Fin m)) (L k p : ℕ) :
    ∀ g∈labelCircuit G (numericalExtractionCode entry inverseLabel table L k p),
      usesFiniteLibrary G g :=
  labelCircuit_uses G _

theorem numericalExtractionCode_error {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → QuaternionOracle) (he : ∀ i,QApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) :
    ‖(denote (extractionCircuit k) : Matrix (Bits (originalWireCount k))
      (Bits (originalWireCount k)) ℂ)-wordPhase (extractionCode k) •
        (denote (labelCircuit G (numericalExtractionCode entry inverseLabel table L k p)) :
          Matrix (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ)‖≤
            (1/2:ℝ)^(p+1) := by
  have heach := fun u => (descriptorSynthesis_spec G entry he inverseLabel hi table L hL hcover
    (extractionPrecision k p) u).2
  have hw := compileLabelWord_error G
    (descriptorSynthesis entry inverseLabel table L (extractionPrecision k p))
    (extractionCode k) ((1/2:ℝ)^extractionPrecision k p) (by positivity) heach
  exact hw.trans (dyadicCircuitPrecision_error (extractionCode k).length (p+1))

theorem numericalExtractionCode_length {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → QuaternionOracle) (he : ∀ i,QApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) :
    (numericalExtractionCode entry inverseLabel table L k p).length≤
      (extractionCode k).length*(32*(L+1)*(extractionPrecision k p+1)^5) := by
  have hs : ∀ u,(descriptorSynthesis entry inverseLabel table L (extractionPrecision k p) u).length≤
      32*(L+1)*(extractionPrecision k p+1)^5 := by
    intro u
    have h := (descriptorSynthesis_spec G entry he inverseLabel hi table L hL hcover
      (extractionPrecision k p) u).1
    exact h.trans (Nat.mul_le_mul_right _ (by omega : 32*L≤32*(L+1)))
  have hpos : 1≤32*(L+1)*(extractionPrecision k p+1)^5 :=
    Nat.succ_le_of_lt (by positivity)
  exact compileLabelWord_length _ _ hpos hs (extractionCode k)

theorem numericalExtractionCode_fidelity {m n : ℕ} (G : Fin m → SU2)
    (entry : Fin m → QuaternionOracle) (he : ∀ i,QApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (hi : ∀ i,G (inverseLabel i)=(G i)⁻¹)
    (table : Fin (n+1) → List (Fin m)) (L : ℕ) (hL : ∀ j,(table j).length≤L)
    (hcover : ∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
      (su2AsUnitary (instructionWordValue G (table j)))≤1/576)
    (k p : ℕ) (z : Fin 4 → ℂ) (hz : IsUnitVector z) :
    1-(1/2:ℝ)^p≤
      (Extraction.bellProjector (d := Bits (bellPairYield k))*
        approximateExtractionOutput k
          (denote (labelCircuit G (numericalExtractionCode entry inverseLabel table L k p)))
          (pureMatrix (bitPurePower k z))).trace.re := by
  have h := extractionOutput_robust_up_to_phase k _ z hz ((1/2:ℝ)^(p+1)) (by positivity)
    (wordPhase (extractionCode k)) (wordPhase_norm _)
    (numericalExtractionCode_error G entry he inverseLabel hi table L hL hcover k p)
  have hid : 2*(1/2:ℝ)^(p+1)=(1/2:ℝ)^p := by rw [pow_succ];ring
  simpa only [hid] using h

/-- The arithmetic count belongs to the actual cached run used for each
one-qubit output word. This bound does not include provider bit cost. -/
def descriptorArithmeticOperations {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) (u : SingleCode) : ℕ :=
  (cachedArithmeticRun entry inverseLabel table L p u.quaternionOracle).executedOperations

theorem descriptorArithmeticOperations_bound {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (hL : ∀ j,(table j).length≤L) (u : SingleCode) :
    descriptorArithmeticOperations entry inverseLabel table L p u≤
      (1001*(n+1)*(L+1)*offsetGrowth)*(p+1)^64 :=
  cachedArithmeticRun_executedOperations entry inverseLabel table L p hL u.quaternionOracle


def gateArithmeticOperations {m n q : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L p : ℕ) : GateCode q → ℕ
  | .single _ u => descriptorArithmeticOperations entry inverseLabel table L p u
  | .cnot _ _ _ => 0

def extractionArithmeticOperations {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) : ℕ :=
  ((extractionCode k).map (gateArithmeticOperations entry inverseLabel table L (extractionPrecision k p))).sum

theorem extractionArithmeticOperations_bound {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L k p : ℕ) (hL : ∀ j,(table j).length≤L) :
    extractionArithmeticOperations entry inverseLabel table L k p≤
      (extractionCode k).length*
        ((1001*(n+1)*(L+1)*offsetGrowth)*(extractionPrecision k p+1)^64) := by
  unfold extractionArithmeticOperations
  calc
    _ ≤ ((extractionCode k).map (fun _ =>
        (1001*(n+1)*(L+1)*offsetGrowth)*(extractionPrecision k p+1)^64)).sum := by
      apply List.sum_le_sum
      intro g hg
      cases g with
      | single i u => exact descriptorArithmeticOperations_bound entry inverseLabel table L _ hL u
      | cnot c t h => exact Nat.zero_le _
    _ = _ := by simp

/-- A universal inverse-closed dictionary admits fixed finite table data
for this actual target-descriptor algorithm. Provider bit cost remains
explicitly outside the arithmetic-expression count. -/
theorem numericalExtraction_from_universal {m : ℕ} (G : Fin m → SU2)
    (hinv : ∀ i,∃ j,G j=(G i)⁻¹)
    (huniversal : Dense (Subgroup.closure (Set.range G) : Set SU2)) :
    ∃ (L n : ℕ) (table : Fin (n+1) → List (Fin m)),
      (∀ j,(table j).length≤L) ∧
      ∀ (entry : Fin m → QuaternionOracle), (∀ i,QApproximates (entry i) (G i)) →
      ∀ (inverseLabel : Fin m → Fin m), (∀ i,G (inverseLabel i)=(G i)⁻¹) →
      ∀ k p : ℕ,
        (∀ g∈labelCircuit G (numericalExtractionCode entry inverseLabel table L k p),
          usesFiniteLibrary G g) ∧
        (numericalExtractionCode entry inverseLabel table L k p).length≤
          (extractionCode k).length*(32*(L+1)*(extractionPrecision k p+1)^5) ∧
        (‖(denote (extractionCircuit k) : Matrix (Bits (originalWireCount k))
          (Bits (originalWireCount k)) ℂ)-wordPhase (extractionCode k) •
            (denote (labelCircuit G (numericalExtractionCode entry inverseLabel table L k p)) :
              Matrix (Bits (originalWireCount k)) (Bits (originalWireCount k)) ℂ)‖≤
                (1/2:ℝ)^(p+1)) ∧
        (∀ z : Fin 4 → ℂ,IsUnitVector z →
          1-(1/2:ℝ)^p≤(Extraction.bellProjector (d := Bits (bellPairYield k))*
            approximateExtractionOutput k
              (denote (labelCircuit G (numericalExtractionCode entry inverseLabel table L k p)))
              (pureMatrix (bitPurePower k z))).trace.re) ∧
        extractionArithmeticOperations entry inverseLabel table L k p≤
          (extractionCode k).length*
            ((1001*(n+1)*(L+1)*offsetGrowth)*(extractionPrecision k p+1)^64) := by
  obtain ⟨L,n,table,hL,hcover⟩ := precomputedNet_exists G hinv huniversal
  refine ⟨L,n,table,hL,fun entry he inverseLabel hi k p => ?_⟩
  exact ⟨numericalExtractionCode_uses G entry inverseLabel table L k p,
    numericalExtractionCode_length G entry he inverseLabel hi table L hL hcover k p,
    numericalExtractionCode_error G entry he inverseLabel hi table L hL hcover k p,
    fun z hz => numericalExtractionCode_fidelity G entry he inverseLabel hi table L hL hcover k p z hz,
    extractionArithmeticOperations_bound entry inverseLabel table L k p hL⟩

end EffectiveEncoding
