import NormCurve
open scoped ComplexConjugate

namespace ComplexPencilFull
open ComplexPencilMain
open ComplexPencilLink

noncomputable section

def omega : ℂ := ⟨-(1/2 : ℝ), rt3/2⟩
def omegaBar : ℂ := ⟨-(1/2 : ℝ), -rt3/2⟩

theorem omega_sq : omega*omega=omegaBar := by
  apply Complex.ext
  · simp [omega,omegaBar,Complex.mul_re]
    nlinarith [rt3_sq]
  · simp [omega,omegaBar,Complex.mul_im]
    ring

theorem omegaBar_sq : omegaBar*omegaBar=omega := by
  apply Complex.ext
  · simp [omega,omegaBar,Complex.mul_re]
    nlinarith [rt3_sq]
  · simp [omega,omegaBar,Complex.mul_im]
    ring

theorem omega_add : omega+omegaBar=-1 := by
  apply Complex.ext
  · norm_num [omega,omegaBar,Complex.add_re]
  · simp [omega,omegaBar,Complex.add_im]
    ring

theorem sq_omega : ComplexPencilLink.sq omega=1 := by
  simp [omega,ComplexPencilLink.sq]
  nlinarith [rt3_sq]

theorem sq_omegaBar : ComplexPencilLink.sq omegaBar=1 := by
  simp [omegaBar,ComplexPencilLink.sq]
  nlinarith [rt3_sq]

theorem per_fourier :
    permanent3 1 1 1 1 omega omegaBar 1 omegaBar omega = -3 := by
  calc
    _ = 3*(omega+omegaBar) := by
      simp [permanent3]
      rw [omega_sq,omegaBar_sq]
      ring
    _ = -3 := by rw [omega_add]; ring

theorem det_fourier :
    determinant3 1 1 1 1 omega omegaBar 1 omegaBar omega =
       (⟨0,-3*rt3⟩:ℂ) := by
  calc
    _ = 3*(omegaBar-omega) := by
      simp [determinant3]
      rw [omega_sq,omegaBar_sq]
      ring
    _ = (⟨0,-3*rt3⟩:ℂ) := by
      apply Complex.ext
      · simp [omega,omegaBar,Complex.mul_re,Complex.sub_re]
      · simp [omega,omegaBar,Complex.mul_im,Complex.sub_im]
        ring

theorem sq_linear_fourier_minus (lam : ℂ) :
    ComplexPencilLink.sq ((-3:ℂ)+lam*(⟨0,-3*rt3⟩:ℂ)) =
       27*(qval lam+1/3-(2*rt3/3)*lam.im) := by
  have hrx :
     rt3^2*lam.re^2=3*lam.re^2 := by rw [rt3_sq]
  have hry :
     rt3^2*lam.im^2=3*lam.im^2 := by rw [rt3_sq]
  simp [ComplexPencilLink.sq, qval, Complex.mul_re,Complex.mul_im,
        Complex.add_re,Complex.add_im]
  nlinarith [hrx,hry]

theorem fourier_minus_exact (lam : ℂ) :
    ComplexPencilLink.sq (permanent3 1 1 1 1 omega omegaBar 1 omegaBar omega +
       lam*determinant3 1 1 1 1 omega omegaBar 1 omegaBar omega) =
       27*(qval lam+1/3-(2*rt3/3)*lam.im) := by
  rw [per_fourier,det_fourier]
  exact sq_linear_fourier_minus lam

theorem fourier_plus_exact (lam : ℂ) :
    ComplexPencilLink.sq (permanent3 1 1 1 1 omegaBar omega 1 omega omegaBar +
       lam*determinant3 1 1 1 1 omegaBar omega 1 omega omegaBar) =
       27*(qval lam+1/3+(2*rt3/3)*lam.im) := by
  have hper : permanent3 1 1 1 1 omegaBar omega 1 omega omegaBar = -3 := by
    simpa [permanent3,add_comm,add_left_comm,add_assoc,mul_comm,mul_left_comm,mul_assoc] using per_fourier
  have hdet : determinant3 1 1 1 1 omegaBar omega 1 omega omegaBar =
    (⟨0,3*rt3⟩:ℂ) := by
    calc
      _ = 3*(omega-omegaBar) := by
        simp [determinant3]
        rw [omega_sq,omegaBar_sq]
        ring
      _ = _ := by
        apply Complex.ext
        · simp [omega,omegaBar,Complex.mul_re,Complex.sub_re]
        · simp [omega,omegaBar,Complex.mul_im,Complex.sub_im]
          ring
  have hx :
    ComplexPencilLink.sq ((-3:ℂ)+lam*(⟨0,3*rt3⟩:ℂ)) =
     27*(qval lam+1/3+(2*rt3/3)*lam.im) := by
    have hrx : rt3^2*lam.re^2=3*lam.re^2 := by rw [rt3_sq]
    have hry : rt3^2*lam.im^2=3*lam.im^2 := by rw [rt3_sq]
    simp [ComplexPencilLink.sq,qval,Complex.mul_re,Complex.mul_im,
      Complex.add_re,Complex.add_im]
    nlinarith [hrx,hry]
  rw [hper,hdet]
  exact hx

theorem witness_rows : rowSq 1 1 1=3 ∧
    rowSq 1 omega omegaBar=3 ∧
    rowSq 1 omegaBar omega=3 := by
  dsimp [rowSq]
  simp only [sq_omega, sq_omegaBar]
  norm_num [ComplexPencilLink.sq]

end
end ComplexPencilFull
