import EffectiveEncoding.SerializedInputExtraction

open CircuitCompletion CircuitRecursion
namespace EffectiveEncoding

/-- Algebraic view of the already fixed online coefficient; not a new
execution-cost field or a supplied complexity certificate. -/
def onlineCoefficientForm (D O R A : ℕ) : ℕ :=
  40000*(40*(D*(8*A+10))+4)^2*(20*O)+R


theorem onlineCoefficientForm_mono (D O R : ℕ) {A B : ℕ} (h : A≤B) :
    onlineCoefficientForm D O R A≤onlineCoefficientForm D O R B := by
  unfold onlineCoefficientForm
  gcongr


theorem onlineCoefficientForm_dilation (D O R A s : ℕ) (hs : 1≤s) :
    onlineCoefficientForm D O R (A*s)≤onlineCoefficientForm D O R A*s^2 := by
  have ha : 8*(A*s)+10≤(8*A+10)*s := by nlinarith
  have hd:=Nat.mul_le_mul_left D ha
  have hlin : 40*(D*(8*(A*s)+10))+4≤(40*(D*(8*A+10))+4)*s := by nlinarith
  have hnum:=Nat.mul_le_mul_right (20*O) (Nat.mul_le_mul_left 40000 (Nat.pow_le_pow_left hlin 2))
  have hpow : 1≤s^2 := Nat.one_le_pow _ _ hs
  have hr : R≤R*s^2 := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left R hpow
  exact (Nat.add_le_add hnum hr).trans_eq (by unfold onlineCoefficientForm;ring)


theorem actualInputOnlineCoefficient_form (m n L k gateB : ℕ) :
    actualInputOnlineCoefficient m n L k gateB=
      onlineCoefficientForm (1000000000002*(n+1)*(L+1)*traceRGrowth)
        (1020*(n+1)*(2*L+1)*offsetGrowth)
        (80*(m+51200000*(L+1)+5)*(1020*(n+1)*(2*L+1)*offsetGrowth))
        (nativeTargetInputCoefficient k L gateB) := by
  simp only [actualInputOnlineCoefficient,actualNativeBooleanCoefficient,onlineCoefficientForm,
    Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm]


theorem actualInputOnlineCoefficient_polynomial (m n L k gateB : ℕ) :
    actualInputOnlineCoefficient m n L k gateB≤
      actualInputOnlineCoefficient m n L 0 gateB*(k+3)^14 := by
  have hs : 1≤(k+3)^7 := Nat.one_le_pow _ _ (by omega)
  have hA : nativeTargetInputCoefficient k L gateB≤nativeTargetInputCoefficient 0 L gateB*(k+3)^7 := by
    unfold nativeTargetInputCoefficient
    have h3 : 1≤(0+3)^7 := by norm_num
    have h:=Nat.mul_le_mul_left (gateB+1000000*(51200000*(L+1)+5)) h3
    simpa only [Nat.mul_one,Nat.mul_assoc] using Nat.mul_le_mul_right ((k+3)^7) h
  rw [actualInputOnlineCoefficient_form,actualInputOnlineCoefficient_form]
  apply (onlineCoefficientForm_mono _ _ _ hA).trans
  exact (onlineCoefficientForm_dilation _ _ _ _ _ hs).trans_eq (by rw [←pow_mul])


theorem labelFieldWidth_polynomial (m k : ℕ) :
    labelFieldWidth m (originalWireCount k)+1≤(m+2)*(k+3) := by
  have hw : originalWireCount k=2*k := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [originalWireCount,ih];omega
  unfold labelFieldWidth
  rw [hw]
  nlinarith


theorem preparationCoefficient_polynomial (k : ℕ) :
    200*(4*k+2)^2≤3200*(k+3)^2 := by
  have h : 4*k+2≤4*(k+3) := by omega
  exact (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left h 2)).trans_eq (by ring)

end EffectiveEncoding
