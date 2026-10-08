import MatrixTheorem
import Mathlib.Analysis.Complex.Basic

namespace ComplexPencilFull

noncomputable section

def rho : ℝ := 2*rt3/3
def imaginaryOffset : ℂ := ⟨0,rt3/3⟩

theorem rho_pos : 0 < rho := by
  unfold rho
  have h := rt3_pos
  positivity

theorem rho_sq : rho^2 = (4/3:ℝ) := by
  unfold rho
  calc
    _ = (4/9:ℝ)*rt3^2 := by ring
    _ = _ := by rw [rt3_sq]; ring

theorem imaginaryOffset_sq_plus (lam : ℂ) :
    ComplexPencilLink.sq (lam+imaginaryOffset) =
      ComplexPencilMain.qval lam+1/3+(2*rt3/3)*lam.im := by
  have hr := rt3_sq
  simp [ComplexPencilLink.sq, imaginaryOffset,ComplexPencilMain.qval,
        Complex.add_re, Complex.add_im]
  nlinarith [hr]

theorem imaginaryOffset_sq_minus (lam : ℂ) :
    ComplexPencilLink.sq (lam-imaginaryOffset) =
      ComplexPencilMain.qval lam+1/3-(2*rt3/3)*lam.im := by
  have hr := rt3_sq
  simp [ComplexPencilLink.sq, imaginaryOffset,ComplexPencilMain.qval,
        Complex.sub_re, Complex.sub_im]
  nlinarith [hr]

theorem norm_sq_equals_sq (z : ℂ) :
    ‖z‖^2 = ComplexPencilLink.sq z := by
  rw [← Complex.normSq_eq_norm_sq]
  exact ComplexPencilFull.normSq_eq_sq z

theorem max_square (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (max a b)^2 = max (a^2) (b^2) := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (by nlinarith)]
  · rw [max_eq_left h, max_eq_left (by nlinarith)]

def normFormula (lam : ℂ) : ℝ :=
  max rho
    (max ‖(1:ℂ)+lam‖
    (max ‖(1:ℂ)-lam‖
    (max ‖lam+imaginaryOffset‖
         ‖lam-imaginaryOffset‖)))

theorem normFormula_nonneg (lam : ℂ) : 0 ≤ normFormula lam := by
  unfold normFormula
  exact le_trans (le_of_lt rho_pos) (le_max_left _ _)

theorem normFormula_sq (lam : ℂ) :
    (normFormula lam)^2 = normBoundSq lam := by
  have hh0 : 0 ≤ rho := le_of_lt rho_pos
  have h1 : 0 ≤ ‖(1:ℂ)+lam‖ := norm_nonneg _
  have h2 : 0 ≤ ‖(1:ℂ)-lam‖ := norm_nonneg _
  have h3 : 0 ≤ ‖lam+imaginaryOffset‖ := norm_nonneg _
  have h4 : 0 ≤ ‖lam-imaginaryOffset‖ := norm_nonneg _
  have h34 : 0 ≤ max ‖lam+imaginaryOffset‖ ‖lam-imaginaryOffset‖ :=
    le_trans h3 (le_max_left _ _)
  have h234 : 0 ≤ max ‖(1:ℂ)-lam‖
       (max ‖lam+imaginaryOffset‖ ‖lam-imaginaryOffset‖) :=
    le_trans h2 (le_max_left _ _)
  have h1234 : 0 ≤ max ‖(1:ℂ)+lam‖
       (max ‖(1:ℂ)-lam‖
        (max ‖lam+imaginaryOffset‖ ‖lam-imaginaryOffset‖)) :=
    le_trans h1 (le_max_left _ _)
  unfold normFormula
  rw [max_square _ _ hh0 h1234,
      max_square _ _ h1 h234,
      max_square _ _ h2 h34,
      max_square _ _ h3 h4]
  rw [rho_sq, norm_sq_equals_sq, norm_sq_equals_sq,
      norm_sq_equals_sq, norm_sq_equals_sq]
  change max (4/3 : ℝ)
     (max (ComplexPencilLink.sq (1+lam))
     (max (ComplexPencilLink.sq (1-lam))
     (max (ComplexPencilLink.sq (lam+imaginaryOffset))
          (ComplexPencilLink.sq (lam-imaginaryOffset))))) =
        normBoundSq lam
  rw [show ComplexPencilLink.sq (1+lam)=
        1+ComplexPencilMain.qval lam+2*lam.re by
        simpa [ComplexPencilMain.beta,ComplexPencilMain.qval] using ComplexPencilMain.sq_beta lam,
      show ComplexPencilLink.sq (1-lam)=
        1+ComplexPencilMain.qval lam-2*lam.re by
        simpa [ComplexPencilMain.alpha,ComplexPencilMain.qval] using ComplexPencilMain.sq_alpha lam,
      imaginaryOffset_sq_plus, imaginaryOffset_sq_minus]
  rfl

theorem matrix_canonical_squared_iff (lam : ℂ) (B : ℝ) :
    matrixSquaredIneq lam B ↔ (normFormula lam)^2 ≤ B := by
  rw [matrix_squared_norm_iff, normFormula_sq]

#print axioms ComplexPencilFull.matrix_canonical_squared_iff

end
end ComplexPencilFull
