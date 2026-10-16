import RankSupport.FlatWitness
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.OpenPos

open scoped BigOperators ComplexOrder
open Matrix MeasureTheory MeasureTheory.Measure TopologicalSpace

namespace ExtractionSchur

noncomputable section

abbrev OneCopyUnitary (D : ℕ) := Matrix.unitaryGroup (Fin D) ℂ

theorem unitary_entry_norm_le_one (D : ℕ) (U : OneCopyUnitary D) (i j : Fin D) :
    ‖(U : Matrix (Fin D) (Fin D) ℂ) i j‖ ≤ 1 := by
  have h := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => (M j j).re) U.prop.1
  simp only [Matrix.star_eq_conjTranspose, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply_eq, Complex.one_re, Complex.re_sum] at h
  have hsum : ∑ x : Fin D, Complex.normSq ((U : Matrix (Fin D) (Fin D) ℂ) x j) = 1 := by
    simpa only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply, neg_mul, mul_neg, sub_neg_eq_add, mul_comm] using h
  have hi : Complex.normSq ((U : Matrix (Fin D) (Fin D) ℂ) i j) ≤ 1 := by
    rw [← hsum]
    exact Finset.single_le_sum (fun x _ => Complex.normSq_nonneg
      ((U : Matrix (Fin D) (Fin D) ℂ) x j)) (Finset.mem_univ i)
  rw [Complex.normSq_eq_norm_sq] at hi
  nlinarith [norm_nonneg ((U : Matrix (Fin D) (Fin D) ℂ) i j)]

theorem isCompact_oneCopyUnitary (D : ℕ) :
    IsCompact (Matrix.unitaryGroup (Fin D) ℂ : Set (Matrix (Fin D) (Fin D) ℂ)) := by
  have hc : IsCompact ((Metric.closedBall (0 : ℂ) 1).matrix :
      Set (Matrix (Fin D) (Fin D) ℂ)) := (isCompact_closedBall (0 : ℂ) 1).matrix
  apply hc.of_isClosed_subset (isClosed_unitary (R := Matrix (Fin D) (Fin D) ℂ))
  intro U hU
  intro i j
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact unitary_entry_norm_le_one D ⟨U,hU⟩ i j

instance oneCopyUnitaryCompactSpace (D : ℕ) : CompactSpace (OneCopyUnitary D) :=
  isCompact_iff_compactSpace.mp (isCompact_oneCopyUnitary D)

instance oneCopyUnitaryMeasurableSpace (D : ℕ) : MeasurableSpace (OneCopyUnitary D) :=
  borel _

instance oneCopyUnitaryBorelSpace (D : ℕ) : BorelSpace (OneCopyUnitary D) :=
  ⟨rfl⟩

/-- The actual normalized Haar probability on the original one-copy unitary group. -/
def unitaryHaar (D : ℕ) : Measure (OneCopyUnitary D) :=
  haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ : PositiveCompacts (OneCopyUnitary D))

instance unitaryHaar_isProbabilityMeasure (D : ℕ) : IsProbabilityMeasure (unitaryHaar D) := by
  constructor
  exact haarMeasure_self

instance unitaryHaar_isMulLeftInvariant (D : ℕ) : IsMulLeftInvariant (unitaryHaar D) := by
  dsimp only [unitaryHaar]
  infer_instance

instance unitaryHaar_isHaarMeasure (D : ℕ) : IsHaarMeasure (unitaryHaar D) := by
  dsimp only [unitaryHaar]
  infer_instance

end
end ExtractionSchur
