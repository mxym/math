import EqualityFlat

open scoped ComplexConjugate
namespace ComplexPencilEquality
open ComplexPencilCert
open ComplexPencilMain
open ComplexPencilAbsolute

noncomputable section

theorem flat_kernel_collinear
    (lam a0 a1 a2 b0 b1 b2 : ℂ)
    (hlam : Complex.normSq lam = detWeight^2)
    (hflat0 : ComplexPencilLink.sq a0=ComplexPencilLink.sq a1)
    (hflat1 : ComplexPencilLink.sq a1=ComplexPencilLink.sq a2)
    (hanonzero : a0 ≠ 0)
    (hQb : Q3
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
      (wentry lam a1 a2) b0 b1 b2 = 0) :
    ∃ t : ℂ, b0=t*a0 ∧ b1=t*a1 ∧ b2=t*a2 := by
  let B : ℝ := 4/3
  let q : ℝ := qval lam
  let x : ℝ := lam.re
  let X : ℝ := ComplexPencilLink.sq a0
  let Y : ℝ := ComplexPencilLink.sq a1
  let Z : ℝ := ComplexPencilLink.sq a2
  let d1 : ℝ := diag1 X Y Z B q x
  let d2 : ℝ := diag2 X Y Z B q x
  let d3 : ℝ := diag3 X Y Z B q x
  let u : ℂ := uentry lam a0 a1
  let v0 : ℂ := ventry lam a0 a2
  let w : ℂ := wentry lam a1 a2
  have hXpos : 0 < X := by
    rcases lt_or_eq_of_le (ComplexPencilLink.sq_nonneg a0) with hp|hz
    · exact hp
    · exact False.elim (hanonzero (link_sq_zero a0 hz.symm))
  have hYpos : 0 < Y := by
    dsimp [X,Y] at *
    rwa [←hflat0]
  have hZpos : 0 < Z := by
    dsimp [X,Y,Z] at *
    rwa [←hflat1]
  have hZnz : a2 ≠ 0 := by
    intro hz
    have hz0 : Z=0 := by simp [Z,hz,ComplexPencilLink.sq]
    exact (ne_of_gt hZpos) hz0
  have hlens := lens_of_normSq lam hlam
  obtain ⟨hB,h3B,hp,hm,hF⟩ := lens_preconditions lam hlens
  have hBpos : 0 < B := by dsimp [B]; norm_num
  have hd1 : 0 < d1 := by
    have hA : 0 < B*X := mul_pos hBpos hXpos
    have hBY : 0 ≤ (h B q+v x)*Y :=
      mul_nonneg hp (le_of_lt hYpos)
    have hCZ : 0 ≤ (h B q-v x)*Z :=
      mul_nonneg hm (le_of_lt hZpos)
    dsimp [d1, diag1]
    linarith
  have hqs : q=detWeight^2 := by
    dsimp [q]
    calc
      _ = Complex.normSq lam := by
         simp [qval,ComplexPencilLink.sq,
           Complex.normSq_apply]
      _ = _ := hlam
  have hspos : 0 < detWeight := by
    have hi := detWeight_identity
    have hn := detWeight_nonneg
    nlinarith
  have hhpos : 0 < h B q := by
    dsimp [B]
    rw [hqs]
    unfold h
    nlinarith [detWeight_identity]
  have hhs : 0 ≤ (h B q)^2-(v x)^2 :=
    hsq_sub_vsq_nonneg B q x hp hm
  have hmp : 0 < 2*B*(h B q)*X*Y := by positivity
  have hminorpos : 0 < minorCertificate X Y Z B q x := by
    unfold minorCertificate
    have h1 : 0 ≤ B*(h B q-v x)*X*X := by positivity
    have h2 : 0 ≤ B*(h B q+v x)*Y*Y := by positivity
    have h3 : 0 ≤ ((h B q)^2-(v x)^2)*Z*Z := by positivity
    have h5 : 0 ≤ (B*(h B q+v x)+(h B q-v x)^2)*X*Z := by positivity
    have h6 : 0 ≤ ((h B q+v x)^2+B*(h B q-v x))*Y*Z := by positivity
    linarith
  have hm12 : 0 < m12 d1 d2 u := by
    have heq := minor01_actual lam a0 a1 a2 B
    change m12 d1 d2 u = minorDirect X Y Z B q x at heq
    rw [minor_global_identity] at heq
    rw [heq]
    exact hminorpos
  have hdet : 0 ≤ det3 d1 d2 d3 u v0 w := by
    have heq := determinant_actual lam a0 a1 a2 B
    change det3 d1 d2 d3 u v0 w=detDirect X Y Z B q x at heq
    rw [heq]
    exact determinant_certificate_nonneg X Y Z B q x
      (le_of_lt hXpos) (le_of_lt hYpos) (le_of_lt hZpos)
      hB h3B hp hm hF
  have hQa : Q3 d1 d2 d3 u v0 w a0 a1 a2=0 :=
    flat_firstrow_null lam a0 a1 a2 hflat0 hflat1
  have hbQ : Q3 d1 d2 d3 u v0 w b0 b1 b2=0 := hQb
  exact hermitian3_nullspace_line d1 d2 d3 u v0 w
    a0 a1 a2 b0 b1 b2
    hd1 hm12 hdet hQa hbQ hZnz

#print axioms ComplexPencilEquality.flat_kernel_collinear

end
end ComplexPencilEquality
