import GaussianRegularFanClassification
import GaussianBoundaryCases

/-!
The final analytic reduction for the four-cell problem.

This file deliberately has no opaque declaration for the Gaussian multi-bubble
inequality.  Instead, the latter remains an explicit hypothesis
`EqualMassSimplicialPerimeterBound`; all consequences of that hypothesis are
closed here, including the sharp bound and the equality classification.  This
keeps the formal statement honest while making the exact interface needed to
replace the published geometric input completely visible.
-/

open MeasureTheory ProbabilityTheory Module Matrix Set
open scoped RealInnerProductSpace Topology

namespace GaussianMeasureBridge

variable {d e : ℕ}

def FourCellGlobalConclusion (d e : ℕ) : Prop :=
  ∀ F : FractionalPartition e (d+2),
    (∀ i, F.mass i = uniformMass (d+2) i) →
    F.momentEnergy ≤ simplexConstant (d+2)^2 ∧
      (F.momentEnergy = simplexConstant (d+2)^2 ↔ IsRegularGaussianFan F)

theorem fourCellGlobalConclusion_of_perimeter
    (hper : EqualMassSimplicialPerimeterBound d) :
    FourCellGlobalConclusion d e := by
  intro F hF
  refine ⟨momentEnergy_bound_of_perimeter hper F hF, ?_⟩
  exact equality_iff_regular_fan_of_perimeter hper F hF

theorem fourCell_upper_bound_of_perimeter
    (hper : EqualMassSimplicialPerimeterBound d)
    (F : FractionalPartition e (d+2))
    (hF : ∀ i, F.mass i = uniformMass (d+2) i) :
    F.momentEnergy ≤ simplexConstant (d+2)^2 :=
  (fourCellGlobalConclusion_of_perimeter hper F hF).1

theorem fourCell_equality_iff_of_perimeter
    (hper : EqualMassSimplicialPerimeterBound d)
    (F : FractionalPartition e (d+2))
    (hF : ∀ i, F.mass i = uniformMass (d+2) i) :
    F.momentEnergy = simplexConstant (d+2)^2 ↔ IsRegularGaussianFan F :=
  (fourCellGlobalConclusion_of_perimeter hper F hF).2

/- The four-cell specialization used in the manuscript: `d = 2` means four
labels in a three-dimensional simplicial score space.  The ambient Gaussian
dimension `e` is arbitrary; cylindrical extensions are included. -/
theorem fourCell_upper_bound_ambient
    (hper : EqualMassSimplicialPerimeterBound 2)
    (F : FractionalPartition e 4)
    (hF : ∀ i, F.mass i = uniformMass 4 i) :
    F.momentEnergy ≤ simplexConstant 4 ^ 2 := by
  simpa using (fourCell_upper_bound_of_perimeter (d := 2) (e := e) hper F hF)

theorem fourCell_equality_ambient
    (hper : EqualMassSimplicialPerimeterBound 2)
    (F : FractionalPartition e 4)
    (hF : ∀ i, F.mass i = uniformMass 4 i) :
    F.momentEnergy = simplexConstant 4 ^ 2 ↔ IsRegularGaussianFan (d := 2) F := by
  simpa using (fourCell_equality_iff_of_perimeter (d := 2) (e := e) hper F hF)

end GaussianMeasureBridge
