import AbsoluteEqFirstRow

open scoped ComplexConjugate
namespace ComplexPencilEquality
open ComplexPencilCert

noncomputable section

theorem hermitian3_zero_Q_linear_constraints
    (d1 d2 d3 : ℝ) (u v w b1 b2 b3 : ℂ)
    (hd1 : 0 < d1) (hm12 : 0 < m12 d1 d2 u)
    (hdet : 0 ≤ det3 d1 d2 d3 u v w)
    (hQ : Q3 d1 d2 d3 u v w b1 b2 b3=0) :
    (d1 : ℂ)*b1+u*b2+v*b3=0 ∧
    ((m12 d1 d2 u : ℝ):ℂ)*b2 +
      ((d1 : ℂ)*w-(conj u)*v)*b3=0 := by
  have hpoly := cholesky_polynomial d1 d2 d3 u v w b1 b2 b3
  rw [hQ] at hpoly
  have hA : 0 ≤ m12 d1 d2 u *
      ComplexPencilCert.sq ((d1 : ℂ)*b1+u*b2+v*b3) :=
    mul_nonneg (le_of_lt hm12) (ComplexPencilCert.sq_nonneg _)
  have hB : 0 ≤ ComplexPencilCert.sq (((m12 d1 d2 u : ℝ):ℂ)*b2+
     ((d1 : ℂ)*w-(conj u)*v)*b3) := ComplexPencilCert.sq_nonneg _
  have hC : 0 ≤ d1*det3 d1 d2 d3 u v w*ComplexPencilCert.sq b3 :=
    mul_nonneg (mul_nonneg (le_of_lt hd1) hdet) (ComplexPencilCert.sq_nonneg _)
  have hAz : m12 d1 d2 u *
      ComplexPencilCert.sq ((d1 : ℂ)*b1+u*b2+v*b3)=0 := by linarith
  have hBz : ComplexPencilCert.sq (((m12 d1 d2 u : ℝ):ℂ)*b2+
     ((d1 : ℂ)*w-(conj u)*v)*b3)=0 := by linarith
  have hE0 : (d1 : ℂ)*b1+u*b2+v*b3=0 := by
    apply sq_zero
    exact (mul_eq_zero.mp hAz).resolve_left (ne_of_gt hm12)
  exact ⟨hE0,sq_zero _ hBz⟩

theorem hermitian3_nullspace_line
    (d1 d2 d3 : ℝ) (u v w : ℂ)
    (a1 a2 a3 b1 b2 b3 : ℂ)
    (hd1 : 0 < d1) (hm12 : 0 < m12 d1 d2 u)
    (hdet : 0 ≤ det3 d1 d2 d3 u v w)
    (ha : Q3 d1 d2 d3 u v w a1 a2 a3=0)
    (hb : Q3 d1 d2 d3 u v w b1 b2 b3=0)
    (ha3 : a3 ≠ 0) :
    ∃ t : ℂ, b1=t*a1 ∧ b2=t*a2 ∧ b3=t*a3 := by
  obtain ⟨ha0, ha1⟩ :=
    hermitian3_zero_Q_linear_constraints
      d1 d2 d3 u v w a1 a2 a3 hd1 hm12 hdet ha
  obtain ⟨hb0, hb1⟩ :=
    hermitian3_zero_Q_linear_constraints
      d1 d2 d3 u v w b1 b2 b3 hd1 hm12 hdet hb
  let t : ℂ := b3/a3
  have hb3 : b3=t*a3 := by
    dsimp [t]
    field_simp [ha3]
  have hDelta2 :
      (((m12 d1 d2 u:ℝ):ℂ)*(b2-t*a2))=0 := by
    calc
      _ = (((m12 d1 d2 u:ℝ):ℂ)*b2+
        ((d1:ℂ)*w-(conj u)*v)*b3) -
        t*((((m12 d1 d2 u:ℝ):ℂ)*a2)+
          ((d1:ℂ)*w-(conj u)*v)*a3) := by
             rw [hb3]; ring
      _ = 0 := by rw [hb1, ha1]; ring
  have hb2 : b2=t*a2 := by
    have hh : b2-t*a2=0 :=
      (mul_eq_zero.mp hDelta2).resolve_left (by
        exact_mod_cast (ne_of_gt hm12))
    exact sub_eq_zero.mp hh
  have hDelta1 : (d1:ℂ)*(b1-t*a1)=0 := by
    calc
      _ = ((d1:ℂ)*b1+u*b2+v*b3) -
          t*((d1:ℂ)*a1+u*a2+v*a3) := by
          rw [hb2,hb3]; ring
      _ = 0 := by rw [hb0,ha0]; ring
  have hb1final : b1=t*a1 := by
    have hh : b1-t*a1=0 :=
      (mul_eq_zero.mp hDelta1).resolve_left (by
        exact_mod_cast (ne_of_gt hd1))
    exact sub_eq_zero.mp hh
  exact ⟨t,hb1final,hb2,hb3⟩

#print axioms ComplexPencilEquality.hermitian3_nullspace_line

end
end ComplexPencilEquality
