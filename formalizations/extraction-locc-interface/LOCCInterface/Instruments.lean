import LOCCInterface.Tree

open scoped BigOperators ComplexOrder Kronecker
open Matrix
namespace ExtractionLOCC
noncomputable section

/-- A local instrument has a public outcome, a possibly hidden Kraus index,
and a public-outcome-dependent next local dimension. -/
structure Instrument (a r : ℕ) (next : Fin r → ℕ) where
  branches : Fin r → ℕ
  A : (i : Fin r) → Fin (branches i) → Matrix (Fin (next i)) (Fin a) ℂ
  complete : ∑ i, ∑ j, (A i j)ᴴ * A i j = 1

namespace Instrument
variable {a r : ℕ} {next : Fin r → ℕ}

def outcomeMap (I : Instrument a r next) (i : Fin r) :=
  ExtractionCP.krausLinearMap (I.A i)

theorem outcome_completelyPositive (I : Instrument a r next) (i : Fin r) :
    ExtractionCP.CompletelyPositive (I.outcomeMap i) :=
  ExtractionCP.krausLinearMap_completelyPositive _

/-- Every arbitrary finite local CP instrument with total trace preservation
has actual finite Kraus data. Complete positivity is the physical all-auxiliary
notion, and no completeness/Kraus certificate is a premise. -/
def ofCP
    (Φ : (i : Fin r) → Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ]
      Matrix (Fin (next i)) (Fin (next i)) ℂ)
    (hcp : ∀ i, ExtractionCP.CompletelyPositive (Φ i))
    (ht : ∀ X, ∑ i, (Φ i X).trace = X.trace) : Instrument a r next where
  branches i := Fintype.card (Fin (next i) × Fin a)
  A i := ExtractionCP.finiteKraus (Φ i)
  complete := by
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro X
    simp only [Matrix.one_mul, Matrix.sum_mul, Matrix.trace_sum]
    calc
      (∑ i, ∑ j, ((ExtractionCP.finiteKraus (Φ i) j)ᴴ *
          ExtractionCP.finiteKraus (Φ i) j * X).trace) = ∑ i, (Φ i X).trace := by
        apply Finset.sum_congr rfl
        intro i _
        have h := Extraction.krausApply_trace_duality
          (ExtractionCP.finiteKraus (Φ i)) X 1
        rw [ExtractionCP.finiteKraus_apply (Φ i) (hcp i)] at h
        simpa only [Matrix.one_mul, Extraction.krausApply, Matrix.mul_one,
          Matrix.conjTranspose_conjTranspose, Matrix.sum_mul, Matrix.trace_sum] using h.symm
      _ = X.trace := ht X

theorem ofCP_outcomeMap
    (Φ : (i : Fin r) → Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ]
      Matrix (Fin (next i)) (Fin (next i)) ℂ)
    (hcp : ∀ i, ExtractionCP.CompletelyPositive (Φ i))
    (ht : ∀ X, ∑ i, (Φ i X).trace = X.trace) (i : Fin r)
    (X : Matrix (Fin a) (Fin a) ℂ) :
    (ofCP Φ hcp ht).outcomeMap i X = Φ i X :=
  ExtractionCP.finiteKraus_apply (Φ i) (hcp i) X

end Instrument

namespace Tree
variable {a b c d r : ℕ} {next : Fin r → ℕ}

/-- Refine the local Kraus index while retaining exactly the same continuation
for each public instrument outcome. The next dimension also ignores this index. -/
def aliceInstrument (I : Instrument a r next)
    (f : (i : Fin r) → Tree c d (next i) b) : Tree c d a b := by
  let e := (Fintype.equivFin ((i : Fin r) × Fin (I.branches i))).symm
  refine .alice (Fintype.card ((i : Fin r) × Fin (I.branches i)))
    (fun j => next (e j).1) (fun j => I.A (e j).1 (e j).2) ?_ (fun j => f (e j).1)
  rw [e.sum_comp (fun j => (I.A j.1 j.2)ᴴ * I.A j.1 j.2), Fintype.sum_sigma]
  exact I.complete

def bobInstrument (I : Instrument b r next)
    (f : (i : Fin r) → Tree c d a (next i)) : Tree c d a b := by
  let e := (Fintype.equivFin ((i : Fin r) × Fin (I.branches i))).symm
  refine .bob (Fintype.card ((i : Fin r) × Fin (I.branches i)))
    (fun j => next (e j).1) (fun j => I.A (e j).1 (e j).2) ?_ (fun j => f (e j).1)
  rw [e.sum_comp (fun j => (I.A j.1 j.2)ᴴ * I.A j.1 j.2), Fintype.sum_sigma]
  exact I.complete

/-- Coarse public instrument semantics: the continuation depends only on the
communicated outcome i, and all Kraus indices j are summed internally. -/
theorem channel_aliceInstrument (I : Instrument a r next)
    (f : (i : Fin r) → Tree c d (next i) b)
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (aliceInstrument I f).channel X =
      ∑ i, ∑ j, (f i).channel ((I.A i j ⊗ₖ 1) * X * (I.A i j ⊗ₖ 1)ᴴ) := by
  unfold aliceInstrument
  rw [channel_alice]
  generalize he : (Fintype.equivFin ((i : Fin r) × Fin (I.branches i))).symm = e
  have hh := e.sum_comp
    (fun ij => (f ij.1).channel ((I.A ij.1 ij.2 ⊗ₖ 1) * X * (I.A ij.1 ij.2 ⊗ₖ 1)ᴴ))
  rw [Fintype.sum_sigma] at hh
  exact hh

theorem channel_bobInstrument (I : Instrument b r next)
    (f : (i : Fin r) → Tree c d a (next i))
    (X : Matrix (Fin a × Fin b) (Fin a × Fin b) ℂ) :
    (bobInstrument I f).channel X =
      ∑ i, ∑ j, (f i).channel ((1 ⊗ₖ I.A i j) * X * (1 ⊗ₖ I.A i j)ᴴ) := by
  unfold bobInstrument
  rw [channel_bob]
  generalize he : (Fintype.equivFin ((i : Fin r) × Fin (I.branches i))).symm = e
  have hh := e.sum_comp
    (fun ij => (f ij.1).channel ((1 ⊗ₖ I.A ij.1 ij.2) * X * (1 ⊗ₖ I.A ij.1 ij.2)ᴴ))
  rw [Fintype.sum_sigma] at hh
  exact hh

end Tree
end
end ExtractionLOCC
