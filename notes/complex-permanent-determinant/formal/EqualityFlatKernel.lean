import EqualityKernelUnique
import EqualityCauchyRigidity

namespace ComplexPencilEquality

open ComplexPencilMain
open ComplexPencilCert
open ComplexPencilLink

noncomputable section

/-- In the equal-magnitude first-row case, that same first row is
exactly a zero-energy vector for the sharp-lens Hermitian gap.
This is a universal complex-coefficient algebraic identity and does
not assume any equality conclusion for the other rows. -/
theorem flat_first_row_null_vector
    (lam a0 a1 a2 : ℂ)
    (he01 : ComplexPencilLink.sq a0 = ComplexPencilLink.sq a1)
    (he12 : ComplexPencilLink.sq a1 = ComplexPencilLink.sq a2) :
    ComplexPencilCert.Q3
      (diag1 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        (4/3 : ℝ) (qval lam) lam.re)
      (diag2 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        (4/3 : ℝ) (qval lam) lam.re)
      (diag3 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        (4/3 : ℝ) (qval lam) lam.re)
      (uentry lam a0 a1) (ventry lam a0 a2)
      (wentry lam a1 a2) a0 a1 a2 = 0 := by
  have ht0 : t0 lam a1 a2 a1 a2 = 2*a1*a2 := by
    simp [t0,p0,q0,alpha,beta]
    ring
  have ht1 : t1 lam a0 a2 a0 a2 = 2*a0*a2 := by
    simp [t1,p1,q1,alpha,beta]
    ring
  have ht2 : t2 lam a0 a1 a0 a1 = 2*a0*a1 := by
    simp [t2,p2,q2,alpha,beta]
    ring
  have hs0 :
      ComplexPencilLink.sq (2*a1*a2) =
        4*(ComplexPencilLink.sq a1)*(ComplexPencilLink.sq a2) := by
    rw [show 2*a1*a2=(2:ℂ)*(a1*a2) by ring,
      ComplexPencilLink.sq_mul,ComplexPencilLink.sq_mul]
    norm_num [ComplexPencilLink.sq] <;> ring
  have hs1 :
      ComplexPencilLink.sq (2*a0*a2) =
        4*(ComplexPencilLink.sq a0)*(ComplexPencilLink.sq a2) := by
    rw [show 2*a0*a2=(2:ℂ)*(a0*a2) by ring,
      ComplexPencilLink.sq_mul,ComplexPencilLink.sq_mul]
    norm_num [ComplexPencilLink.sq] <;> ring
  have hs2 :
      ComplexPencilLink.sq (2*a0*a1) =
        4*(ComplexPencilLink.sq a0)*(ComplexPencilLink.sq a1) := by
    rw [show 2*a0*a1=(2:ℂ)*(a0*a1) by ring,
      ComplexPencilLink.sq_mul,ComplexPencilLink.sq_mul]
    norm_num [ComplexPencilLink.sq] <;> ring
  have hgap := actual_complement lam a0 a1 a2 a0 a1 a2 (4/3 : ℝ)
  rw [ht0,ht1,ht2,hs0,hs1,hs2] at hgap
  have hleft :
      (4/3 : ℝ)*rowSq a0 a1 a2*rowSq a0 a1 a2 -
        (4*(ComplexPencilLink.sq a1)*(ComplexPencilLink.sq a2) +
         4*(ComplexPencilLink.sq a0)*(ComplexPencilLink.sq a2) +
         4*(ComplexPencilLink.sq a0)*(ComplexPencilLink.sq a1))=0 := by
    dsimp [rowSq]
    rw [←he12,←he01]
    ring
  rw [hleft] at hgap
  exact hgap.symm

#print axioms ComplexPencilEquality.flat_first_row_null_vector

end
end ComplexPencilEquality
