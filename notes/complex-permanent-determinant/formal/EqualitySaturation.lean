import EqualityKernel

namespace ComplexPencilEquality
open ComplexPencilCert
open ComplexPencilMain
open ComplexPencilLink
open ComplexPencilAbsolute

noncomputable section

/-- Exact equality in the three-row complex pencil bound forces a
zero Hermitian energy remainder (provided the third row is nonzero). -/
theorem Q3_zero_of_pencil_saturation
    (lam a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) (B : ℝ)
    (hcpos : 0 < rowSq c0 c1 c2)
    (hsat :
      ComplexPencilLink.sq
      (permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2+
       lam*determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2) =
      B*rowSq a0 a1 a2*rowSq b0 b1 b2*
       rowSq c0 c1 c2)
    (hqnonneg : 0 ≤ ComplexPencilCert.Q3
      (ComplexPencilCert.diag1 (ComplexPencilLink.sq a0)
       (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
       B (qval lam) lam.re)
      (ComplexPencilCert.diag2 (ComplexPencilLink.sq a0)
       (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
       B (qval lam) lam.re)
      (ComplexPencilCert.diag3 (ComplexPencilLink.sq a0)
       (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
       B (qval lam) lam.re)
      (uentry lam a0 a1) (ventry lam a0 a2)
      (wentry lam a1 a2) b0 b1 b2) :
    ComplexPencilCert.Q3
      (ComplexPencilCert.diag1 (ComplexPencilLink.sq a0)
       (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
       B (qval lam) lam.re)
      (ComplexPencilCert.diag2 (ComplexPencilLink.sq a0)
       (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
       B (qval lam) lam.re)
      (ComplexPencilCert.diag3 (ComplexPencilLink.sq a0)
       (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
       B (qval lam) lam.re)
      (uentry lam a0 a1) (ventry lam a0 a2)
      (wentry lam a1 a2) b0 b1 b2 = 0 := by
  let T : ℝ :=
    ComplexPencilLink.sq (t0 lam a1 a2 b1 b2)+
    ComplexPencilLink.sq (t1 lam a0 a2 b0 b2)+
    ComplexPencilLink.sq (t2 lam a0 a1 b0 b1)
  let S : ℝ := B*rowSq a0 a1 a2*rowSq b0 b1 b2
  have hcauchy :=
    ComplexPencilLink.complex_three_cauchy c0 c1 c2
      (t0 lam a1 a2 b1 b2)
      (t1 lam a0 a2 b0 b2)
      (t2 lam a0 a1 b0 b1)
  have hsatle : S*rowSq c0 c1 c2 ≤ T*rowSq c0 c1 c2 := by
    have heq : S*rowSq c0 c1 c2 =
        ComplexPencilLink.sq
          (permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2+
           lam*determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2) := by
      simpa [S] using hsat.symm
    have he : rowSq c0 c1 c2 =
         ComplexPencilLink.sq c0+
         ComplexPencilLink.sq c1+
         ComplexPencilLink.sq c2 := rfl
    calc
      _ = ComplexPencilLink.sq
           (permanent3 a0 a1 a2 b0 b1 b2 c0 c1 c2+
            lam*determinant3 a0 a1 a2 b0 b1 b2 c0 c1 c2) := heq
      _ = ComplexPencilLink.sq
         (c0*t0 lam a1 a2 b1 b2+
          c1*t1 lam a0 a2 b0 b2+
          c2*t2 lam a0 a1 b0 b1) := by
            rw [←trilinear_pencil_identity]
      _ ≤ rowSq c0 c1 c2*T := by
        rw [he]
        exact hcauchy
      _ = _ := by ring
  have hSle : S ≤ T := by
    by_contra hnot
    have hlt : T < S := lt_of_not_ge hnot
    have hstrong := mul_lt_mul_of_pos_right hlt hcpos
    exact (not_lt_of_ge hsatle) hstrong
  have hbridge := actual_complement
    lam a0 a1 a2 b0 b1 b2 B
  change S-T = ComplexPencilCert.Q3
      (ComplexPencilCert.diag1 (ComplexPencilLink.sq a0)
       (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
       B (qval lam) lam.re)
      (ComplexPencilCert.diag2 (ComplexPencilLink.sq a0)
       (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
       B (qval lam) lam.re)
      (ComplexPencilCert.diag3 (ComplexPencilLink.sq a0)
       (ComplexPencilLink.sq a1) (ComplexPencilLink.sq a2)
       B (qval lam) lam.re)
      (uentry lam a0 a1) (ventry lam a0 a2)
      (wentry lam a1 a2) b0 b1 b2 at hbridge
  linarith

#print axioms ComplexPencilEquality.Q3_zero_of_pencil_saturation

end
end ComplexPencilEquality
