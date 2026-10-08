import EqualityGeometry

namespace ComplexPencilEquality
open ComplexPencilCert
open scoped ComplexConjugate

noncomputable section

/-- A positive-semidefinite complex Hermitian 3×3 matrix with a
nonzero quadratic-form null vector has zero determinant.
This is established directly from the division-free Cholesky identity,
including all possible zero pivots. -/
theorem Q3_zero_det_zero
    (d1 d2 d3 : ℝ) (u v w b1 b2 b3 : ℂ)
    (hd1 : 0 ≤ d1)
    (hm12 : 0 ≤ m12 d1 d2 u)
    (hm13 : 0 ≤ m13 d1 d3 v)
    (hdet : 0 ≤ det3 d1 d2 d3 u v w)
    (hb : b1 ≠ 0 ∨ b2 ≠ 0 ∨ b3 ≠ 0)
    (hq : Q3 d1 d2 d3 u v w b1 b2 b3 = 0) :
    det3 d1 d2 d3 u v w = 0 := by
  by_contra hne
  have hdp : 0 < det3 d1 d2 d3 u v w := by
    rcases lt_or_eq_of_le hdet with hpos | heq
    · exact hpos
    · exact False.elim (hne heq.symm)
  have hd1pos : 0 < d1 := by
    by_contra hnot
    have hzero : d1=0 := le_antisymm (le_of_not_gt hnot) hd1
    have hu : u=0 := by
      have hs : ComplexPencilCert.sq u = 0 := by
        dsimp [m12] at hm12
        rw [hzero] at hm12
        nlinarith [sq_nonneg u]
      exact sq_zero u hs
    have hv : v=0 := by
      have hs : ComplexPencilCert.sq v = 0 := by
        dsimp [m13] at hm13
        rw [hzero] at hm13
        nlinarith [sq_nonneg v]
      exact sq_zero v hs
    have hdet0 : det3 d1 d2 d3 u v w=0 := by
      simp [det3, hzero, hu, hv, ComplexPencilCert.sq]
    exact (ne_of_gt hdp) hdet0
  have hmpos : 0 < m12 d1 d2 u := by
    by_contra hnot
    have hmzero : m12 d1 d2 u=0 :=
      le_antisymm (le_of_not_gt hnot) hm12
    have hmid := minor_det3 d1 d2 d3 u v w
    rw [hmzero] at hmid
    have hx : 0 ≤ ComplexPencilCert.sq ((d1:ℂ)*w-(conj u)*v) := sq_nonneg _
    have hp : 0 < d1 * det3 d1 d2 d3 u v w :=
      mul_pos hd1pos hdp
    nlinarith
  have hs := cholesky_polynomial d1 d2 d3 u v w b1 b2 b3
  rw [hq] at hs
  simp only [mul_zero, zero_mul] at hs
  have ha : 0 ≤ m12 d1 d2 u *
      ComplexPencilCert.sq ((d1 : ℂ)*b1+u*b2+v*b3) :=
    mul_nonneg hm12 (sq_nonneg _)
  have hbterm : 0 ≤ ComplexPencilCert.sq
      (((m12 d1 d2 u : ℝ):ℂ)*b2+
       ((d1 : ℂ)*w-(conj u)*v)*b3) := sq_nonneg _
  have hc : 0 ≤ d1*det3 d1 d2 d3 u v w*ComplexPencilCert.sq b3 :=
    mul_nonneg (mul_nonneg hd1 hdet) (sq_nonneg _)
  have hc0 : d1*det3 d1 d2 d3 u v w*ComplexPencilCert.sq b3=0 := by
    linarith
  have hb3sq : ComplexPencilCert.sq b3=0 := by
    have hprod : 0 < d1*det3 d1 d2 d3 u v w :=
      mul_pos hd1pos hdp
    exact (mul_eq_zero.mp hc0).resolve_left (ne_of_gt hprod)
  have hb3 : b3=0 := sq_zero b3 hb3sq
  have hbterm0 : ComplexPencilCert.sq
      (((m12 d1 d2 u : ℝ):ℂ)*b2+
       ((d1 : ℂ)*w-(conj u)*v)*b3)=0 := by
    linarith
  have hb2prod : ((m12 d1 d2 u : ℝ):ℂ)*b2=0 := by
    have hz := sq_zero _ hbterm0
    rw [hb3] at hz
    simpa using hz
  have hb2 : b2=0 := by
    rcases mul_eq_zero.mp hb2prod with hh | hh
    · have hmz : m12 d1 d2 u=0 := by exact_mod_cast hh
      exact False.elim ((ne_of_gt hmpos) hmz)
    · exact hh
  have ha0 : m12 d1 d2 u *
      ComplexPencilCert.sq ((d1:ℂ)*b1+u*b2+v*b3)=0 := by
    linarith
  have hb1sq : ComplexPencilCert.sq ((d1:ℂ)*b1+u*b2+v*b3)=0 :=
    (mul_eq_zero.mp ha0).resolve_left (ne_of_gt hmpos)
  have hb1prod : (d1:ℂ)*b1=0 := by
    have hz := sq_zero _ hb1sq
    rw [hb2,hb3] at hz
    simpa using hz
  have hb1 : b1=0 := by
    rcases mul_eq_zero.mp hb1prod with hh | hh
    · have hd1z : d1=0 := by exact_mod_cast hh
      exact False.elim ((ne_of_gt hd1pos) hd1z)
    · exact hh
  rcases hb with hb | hb
  · exact hb hb1
  · rcases hb with hb | hb
    · exact hb hb2
    · exact hb hb3

#print axioms ComplexPencilEquality.Q3_zero_det_zero

end
end ComplexPencilEquality
