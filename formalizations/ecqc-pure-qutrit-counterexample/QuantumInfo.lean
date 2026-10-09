import QuantumBorn

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
noncomputable section

namespace ECQC

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- Totalized spectral entropy. On Hermitian matrices this is exactly the sum over
Mathlib's actual eigenvalues; the unused non-Hermitian branch is zero. -/
def matrixEntropy (A : Matrix n n ℂ) : ℝ :=
  if hA : A.IsHermitian then vonNeumannEntropy A hA else 0

theorem matrixEntropy_eq (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    matrixEntropy A = vonNeumannEntropy A hA := by
  simp only [matrixEntropy, dif_pos hA]

/-- Quantum mutual information of the actual operator and its two partial traces. -/
def quantumMutualInformation (A : Matrix (n × m) (n × m) ℂ) : ℝ :=
  matrixEntropy (partialTraceRight A) + matrixEntropy (partialTraceLeft A) - matrixEntropy A

/-- Shannon entropy, with the standard zero-mass convention. -/
def shannon {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  ∑ i, -p i * Real.log (p i)

/-- Mutual information of a probability table, with its actual row and column marginals. -/
def mutualInformation (P : Matrix n m ℝ) : ℝ :=
  shannon (fun i => ∑ j, P i j) + shannon (fun j => ∑ i, P i j) -
    shannon (fun x : n × m => P x.1 x.2)

/-- A complete indexed MUB family in dimension d: d+1 unitary measurement
matrices and the defining squared cross-overlaps 1/d. -/
def IsCompleteMUB {d : ℕ} (B : Fin (d+1) → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  (∀ a, (B a)ᴴ * B a = 1) ∧
  (∀ a b, a ≠ b → ∀ i j, Complex.normSq (((B a)ᴴ * B b) i j) = 1/(d : ℝ))

/-- All d-term sums from the d+1 settings in the original ECQC conjecture. -/
def retainedValues {d : ℕ}
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (B : Fin (d+1) → Matrix (Fin d) (Fin d) ℂ) : Set ℝ :=
  {t | ∃ s : Finset (Fin (d+1)), s.card = d ∧
    t = ∑ a ∈ s, mutualInformation (bornTable A (B a) (B a))}

/-- The original minimum over retained settings. In the witness below its
value set is proved to be a nonempty singleton, so the infimum is attained. -/
def ecqcScore {d : ℕ}
    (A : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (B : Fin (d+1) → Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  sInf (retainedValues A B)

end ECQC
