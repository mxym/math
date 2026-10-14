import APPTReview.FullEntropySaturation

open scoped BigOperators ComplexOrder
open Matrix
namespace APPTReview

/-- The singular endpoint cannot be included by allowing Taylor radius one.
This is a scalar control, not an assertion of physical realization. -/
theorem entropy_taylor_radius_one_rejected :
    ¬entropyKernel (-1)≤(-1:ℝ)^2/(2*(1-1)) := by
  norm_num [entropyKernel]

/-- Retaining the exceptional-head energy is essential in the scalar variance
combination. These numbers are not claimed to be an APPT spectrum. -/
theorem retained_head_cannot_be_deleted :
    (3:ℝ)*(8-4)+4*2*0*0+3*2^2*0^2≤4*3*1^2 ∧
    (8:ℝ)≤8+0*0+9/4*0^2 ∧
    max (4:ℝ) (9/2^2)*1^2<8 := by norm_num

/-- The exact pivot correction is nonzero even in a two-point trace-one
example; uniform-pivot substitution would change the quadratic objective. -/
theorem entropy_nonuniform_pivot_control :
    (∑ i : Fin 2,((![3/4,1/4] : Fin 2 → ℝ) i/(1/4)-1)^2)=4 ∧
    ((∑ i : Fin 2,((![3/4,1/4] : Fin 2 → ℝ) i)^2)-1/2)/(1/4)^2=2 ∧
    (2:ℝ)*(1/(2*(1/4))-1)^2=2 := by
  norm_num [Fin.sum_univ_two]

/-- The complete partition really removes both ends: for h=1,D=4 the
middle consists only of the index one. -/
theorem entropy_bulk_partition_control : entropyBulkIndices 4 1={1} := by
  ext i
  fin_cases i <;> norm_num [entropyBulkIndices]

/-- Both scalar remainder bounds are sharp at zero. -/
theorem entropy_zero_remainder_control : entropyRemainder 0=0 := by
  norm_num [entropyRemainder,entropyKernel]

end APPTReview
