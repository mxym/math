import EqualityKernelUnique

open scoped ComplexConjugate
namespace ComplexPencilEquality
open ComplexPencilMain
open ComplexPencilCert

noncomputable section

theorem t0_on_diagonal (lam a0 a1 a2 : ℂ) :
    t0 lam a1 a2 a1 a2 = 2*a1*a2 := by
  unfold t0 p0 q0 alpha beta
  ring

theorem t1_on_diagonal (lam a0 a1 a2 : ℂ) :
    t1 lam a0 a2 a0 a2 = 2*a0*a2 := by
  unfold t1 p1 q1 alpha beta
  ring

theorem t2_on_diagonal (lam a0 a1 a2 : ℂ) :
    t2 lam a0 a1 a0 a1 = 2*a0*a1 := by
  unfold t2 p2 q2 alpha beta
  ring

theorem squared_pair (a b : ℂ) :
    ComplexPencilLink.sq (2*a*b) =
      4*ComplexPencilLink.sq a*ComplexPencilLink.sq b := by
  rw [ComplexPencilLink.sq_mul, ComplexPencilLink.sq_mul]
  norm_num [ComplexPencilLink.sq]

theorem flat_firstrow_null
    (lam a0 a1 a2 : ℂ)
    (h01 : ComplexPencilLink.sq a0=ComplexPencilLink.sq a1)
    (h12 : ComplexPencilLink.sq a1=ComplexPencilLink.sq a2) :
  Q3
      (diag1 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        (4/3:ℝ) (qval lam) lam.re)
      (diag2 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        (4/3:ℝ) (qval lam) lam.re)
      (diag3 (ComplexPencilLink.sq a0)
        (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
        (4/3:ℝ) (qval lam) lam.re)
      (uentry lam a0 a1)
      (ventry lam a0 a2)
      (wentry lam a1 a2) a0 a1 a2 = 0 := by
  have hbridge := actual_complement lam a0 a1 a2 a0 a1 a2 (4/3:ℝ)
  rw [t0_on_diagonal lam a0 a1 a2,
      t1_on_diagonal lam a0 a1 a2,
      t2_on_diagonal lam a0 a1 a2] at hbridge
  rw [squared_pair,squared_pair,squared_pair] at hbridge
  have hY : ComplexPencilLink.sq a1=ComplexPencilLink.sq a0 :=
    h01.symm
  have hZ : ComplexPencilLink.sq a2=ComplexPencilLink.sq a0 :=
    (h01.trans h12).symm
  have hzero :
      (4/3:ℝ)*rowSq a0 a1 a2*rowSq a0 a1 a2 -
       (4*ComplexPencilLink.sq a1*ComplexPencilLink.sq a2+
        4*ComplexPencilLink.sq a0*ComplexPencilLink.sq a2+
        4*ComplexPencilLink.sq a0*ComplexPencilLink.sq a1)=0 := by
    simp only [rowSq, hY, hZ]
    ring
  exact hbridge.symm.trans hzero

#print axioms ComplexPencilEquality.flat_firstrow_null

end
end ComplexPencilEquality
