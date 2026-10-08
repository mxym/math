import NormCanonical
import Mathlib.Tactic.FieldSimp

open scoped ComplexConjugate

namespace ComplexPencilAbsolute
open ComplexPencilFull
open ComplexPencilMain

noncomputable section

theorem normSq_of_real (r : ℝ) :
   Complex.normSq (r : ℂ) = r^2 := by
  rw [Complex.normSq_ofReal]
  ring

theorem aligned_phase (P D : ℂ) (s : ℝ) (hs : 0 ≤ s) :
    ∃ lam : ℂ, Complex.normSq lam = s^2 ∧
      Complex.normSq (P+lam*D) = (‖P‖+s*‖D‖)^2 := by
  by_cases hP : P=0
  · refine ⟨(s:ℂ), normSq_of_real s, ?_⟩
    rw [hP]
    simp only [zero_add]
    rw [Complex.normSq_mul, normSq_of_real,
        Complex.normSq_eq_norm_sq]
    simp
    ring
  by_cases hD : D=0
  · refine ⟨(s:ℂ), normSq_of_real s, ?_⟩
    rw [hD]
    simp [Complex.normSq_eq_norm_sq]
  let p : ℝ := ‖P‖
  let d : ℝ := ‖D‖
  have hp : 0 < p := by
    dsimp [p]
    exact norm_pos_iff.mpr hP
  have hd : 0 < d := by
    dsimp [d]
    exact norm_pos_iff.mpr hD
  let r : ℝ := s/(p*d)
  let lam : ℂ := (r:ℂ)*P*(conj D)
  have hr1 : r^2*p^2*d^2=s^2 := by
    dsimp [r]
    field_simp <;> ring
  have hr2 : r*d*d=s*d/p := by
    dsimp [r]
    field_simp <;> ring
  have hnormLam : Complex.normSq lam=s^2 := by
    calc
      Complex.normSq lam =
        r^2*(‖P‖^2)*(‖D‖^2) := by
          dsimp [lam]
          rw [Complex.normSq_mul,Complex.normSq_mul,
              Complex.normSq_conj,normSq_of_real,
              Complex.normSq_eq_norm_sq,
              Complex.normSq_eq_norm_sq] <;> ring
      _ = s^2 := by simpa [p,d] using hr1
  have hconj : (conj D)*D = ((d*d : ℝ) : ℂ) := by
    calc
      _ = ((Complex.normSq D) : ℂ) :=
            (Complex.normSq_eq_conj_mul_self).symm
      _ = (((‖D‖)^2:ℝ):ℂ) := by rw [Complex.normSq_eq_norm_sq]
      _ = ((d*d:ℝ):ℂ) := by dsimp [d]; ring
  have hmul : lam*D = ((s*d/p:ℝ):ℂ)*P := by
    dsimp [lam]
    calc
      _ = ((r:ℝ):ℂ)*P*((conj D)*D) := by ring
      _ = ((r:ℝ):ℂ)*P*((d*d:ℝ):ℂ) := by rw [hconj]
      _ = ((r*d*d:ℝ):ℂ)*P := by push_cast; ring
      _ = ((s*d/p:ℝ):ℂ)*P := by rw [hr2]
  have hsum : P+lam*D = ((1+s*d/p:ℝ):ℂ)*P := by
    rw [hmul]
    push_cast
    ring
  have hmain : Complex.normSq (P+lam*D)=(p+s*d)^2 := by
    rw [hsum,Complex.normSq_mul,normSq_of_real,
        Complex.normSq_eq_norm_sq]
    change (1+s*d/p)^2*p^2=(p+s*d)^2
    field_simp <;> ring
  exact ⟨lam, hnormLam, hmain⟩

#print axioms ComplexPencilAbsolute.aligned_phase

def detWeight : ℝ := ComplexPencilFull.rho-1

theorem detWeight_nonneg : 0 ≤ detWeight := by
  unfold detWeight
  have hρ := ComplexPencilFull.rho_pos
  have hs := ComplexPencilFull.rho_sq
  nlinarith

theorem detWeight_identity :
    detWeight^2+2*detWeight=(1/3:ℝ) := by
  unfold detWeight
  have hρ := ComplexPencilFull.rho_sq
  nlinarith

theorem lens_of_normSq
    (lam : ℂ) (h : Complex.normSq lam=detWeight^2) :
    ComplexPencilMain.qval lam+2*|lam.re|≤(1/3:ℝ) := by
  have hre : lam.re^2≤detWeight^2 := by
    rw [←h]
    simp [Complex.normSq_apply]
    nlinarith [mul_self_nonneg lam.im]
  have ha : |lam.re|≤detWeight := by
    rcases le_total (0:ℝ) lam.re with hr | hr
    · rw [abs_of_nonneg hr]
      nlinarith [detWeight_nonneg]
    · rw [abs_of_nonpos hr]
      nlinarith [detWeight_nonneg]
  have hq : ComplexPencilMain.qval lam=detWeight^2 := by
    calc
       _ = Complex.normSq lam := by
         simp [ComplexPencilMain.qval,ComplexPencilLink.sq,
           Complex.normSq_apply,pow_two]
       _ = _ := h
  nlinarith [detWeight_identity]

theorem sharp_absolute_squared
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) :
    (‖ComplexPencilMain.permanent3
             a0 a1 a2 b0 b1 b2 c0 c1 c2‖+
        detWeight*‖ComplexPencilMain.determinant3
             a0 a1 a2 b0 b1 b2 c0 c1 c2‖)^2 ≤
       (4/3:ℝ)*
       ComplexPencilMain.rowSq a0 a1 a2*
       ComplexPencilMain.rowSq b0 b1 b2*
       ComplexPencilMain.rowSq c0 c1 c2 := by
  let P := ComplexPencilMain.permanent3
             a0 a1 a2 b0 b1 b2 c0 c1 c2
  let D := ComplexPencilMain.determinant3
             a0 a1 a2 b0 b1 b2 c0 c1 c2
  obtain ⟨lam, hlam, halign⟩ :=
     aligned_phase P D detWeight detWeight_nonneg
  have hlens := lens_of_normSq lam hlam
  have hbound :=
    ComplexPencilMain.sharp_complex_lens_upper
      lam a0 a1 a2 b0 b1 b2 c0 c1 c2 hlens
  change ComplexPencilLink.sq (P+lam*D)≤_ at hbound
  rw [← ComplexPencilFull.normSq_eq_sq] at hbound
  rw [halign] at hbound
  exact hbound

def rowNorm (a0 a1 a2 : ℂ) : ℝ :=
    Real.sqrt (ComplexPencilMain.rowSq a0 a1 a2)

theorem rowNorm_nonneg (a0 a1 a2 : ℂ) :
    0≤rowNorm a0 a1 a2 :=
  Real.sqrt_nonneg _

theorem rowNorm_sq (a0 a1 a2 : ℂ) :
    (rowNorm a0 a1 a2)^2 =
       ComplexPencilMain.rowSq a0 a1 a2 := by
  unfold rowNorm
  apply Real.sq_sqrt
  unfold ComplexPencilMain.rowSq
  have h0 := ComplexPencilLink.sq_nonneg a0
  have h1 := ComplexPencilLink.sq_nonneg a1
  have h2 := ComplexPencilLink.sq_nonneg a2
  linarith

theorem sharp_absolute_value
    (a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ) :
    ‖ComplexPencilMain.permanent3
             a0 a1 a2 b0 b1 b2 c0 c1 c2‖+
        detWeight*‖ComplexPencilMain.determinant3
             a0 a1 a2 b0 b1 b2 c0 c1 c2‖ ≤
      ComplexPencilFull.rho*
        rowNorm a0 a1 a2*rowNorm b0 b1 b2*
        rowNorm c0 c1 c2 := by
  have hh := sharp_absolute_squared
     a0 a1 a2 b0 b1 b2 c0 c1 c2
  have hr := ComplexPencilFull.rho_sq
  have ha := rowNorm_sq a0 a1 a2
  have hb := rowNorm_sq b0 b1 b2
  have hc := rowNorm_sq c0 c1 c2
  have hpos : 0≤ComplexPencilFull.rho*
        rowNorm a0 a1 a2*rowNorm b0 b1 b2*
        rowNorm c0 c1 c2 := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (le_of_lt ComplexPencilFull.rho_pos)
          (rowNorm_nonneg a0 a1 a2))
        (rowNorm_nonneg b0 b1 b2))
      (rowNorm_nonneg c0 c1 c2)
  have htarget_sq :
    (‖ComplexPencilMain.permanent3
             a0 a1 a2 b0 b1 b2 c0 c1 c2‖+
        detWeight*‖ComplexPencilMain.determinant3
             a0 a1 a2 b0 b1 b2 c0 c1 c2‖)^2 ≤
      (ComplexPencilFull.rho*rowNorm a0 a1 a2*
        rowNorm b0 b1 b2*rowNorm c0 c1 c2)^2 := by
    calc
      _ ≤ (4/3:ℝ)*
        ComplexPencilMain.rowSq a0 a1 a2*
        ComplexPencilMain.rowSq b0 b1 b2*
        ComplexPencilMain.rowSq c0 c1 c2 := hh
      _ = _ := by rw [←hr,←ha,←hb,←hc]; ring
  have hleft : 0≤
     ‖ComplexPencilMain.permanent3
             a0 a1 a2 b0 b1 b2 c0 c1 c2‖+
        detWeight*‖ComplexPencilMain.determinant3
             a0 a1 a2 b0 b1 b2 c0 c1 c2‖ := by
    exact add_nonneg (norm_nonneg _)
       (mul_nonneg detWeight_nonneg (norm_nonneg _))
  nlinarith

#print axioms ComplexPencilAbsolute.sharp_absolute_value

theorem determinant_weight_sharp (w : ℝ)
    (hAll : ∀ a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ,
     ‖ComplexPencilMain.permanent3
       a0 a1 a2 b0 b1 b2 c0 c1 c2‖+
       w*‖ComplexPencilMain.determinant3
       a0 a1 a2 b0 b1 b2 c0 c1 c2‖ ≤
       ComplexPencilFull.rho*
        rowNorm a0 a1 a2*rowNorm b0 b1 b2*
        rowNorm c0 c1 c2) :
    w≤detWeight := by
  have h := hAll 1 0 0 0 1 0 0 0 1
  have hn : (1:ℝ)+w≤ComplexPencilFull.rho := by
    simpa [ComplexPencilMain.permanent3,
      ComplexPencilMain.determinant3,
      rowNorm, ComplexPencilMain.rowSq,
      ComplexPencilLink.sq] using h
  unfold detWeight
  linarith

theorem prefactor_sharp (R : ℝ)
    (hAll : ∀ a0 a1 a2 b0 b1 b2 c0 c1 c2 : ℂ,
     ‖ComplexPencilMain.permanent3
       a0 a1 a2 b0 b1 b2 c0 c1 c2‖+
       detWeight*‖ComplexPencilMain.determinant3
       a0 a1 a2 b0 b1 b2 c0 c1 c2‖ ≤
       R*rowNorm a0 a1 a2*rowNorm b0 b1 b2*
        rowNorm c0 c1 c2) :
    ComplexPencilFull.rho≤R := by
  have h := hAll 1 1 1 1 1 1 1 1 1
  have hρ := ComplexPencilFull.rho_sq
  have hp := ComplexPencilFull.rho_pos
  have hr := ComplexPencilFull.rt3_sq
  have hrpos := ComplexPencilFull.rt3_pos
  have hf : (6:ℝ)≤R*ComplexPencilFull.rt3^3 := by
    norm_num [ComplexPencilMain.permanent3,
      ComplexPencilMain.determinant3,
      rowNorm, ComplexPencilMain.rowSq,
      ComplexPencilLink.sq] at h
    simpa [ComplexPencilFull.rt3, pow_succ, mul_assoc] using h
  have hcoe : ComplexPencilFull.rho*
                 ComplexPencilFull.rt3^3=6 := by
    unfold ComplexPencilFull.rho
    nlinarith [hr]
  have h3 : 0<ComplexPencilFull.rt3^3 := pow_pos hrpos _
  nlinarith

#print axioms ComplexPencilAbsolute.determinant_weight_sharp
#print axioms ComplexPencilAbsolute.prefactor_sharp

end
end ComplexPencilAbsolute
