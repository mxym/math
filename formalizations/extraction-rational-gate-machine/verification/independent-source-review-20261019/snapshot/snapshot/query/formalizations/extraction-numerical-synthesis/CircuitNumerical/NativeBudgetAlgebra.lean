import CircuitNumerical.NativeDataBudgets

namespace CircuitRecursion

theorem nativeBudget_height_scale (A Q a : ℕ) (hQ : 1≤Q) :
    8*(A*Q^a+1)+2≤(8*A+10)*Q^a := by
  have hp : 1≤Q^a := Nat.one_le_pow _ _ hQ
  nlinarith

/-- Record-free algebra: none of the native ASTs or numerical records is
unfolded to normalize these products. -/
theorem nativeBudget_precision_product (D S A Q a X G : ℕ) (hQ : 1≤Q) (hX : X≤G*Q^128) :
    20*(D*(8*(A*Q^a+1)+2)*S*X)≤(20*(D*(8*A+10)*S*G))*Q^(a+128) := by
  have hb:=nativeBudget_height_scale A Q a hQ
  have hm:=Nat.mul_le_mul (Nat.mul_le_mul_right S (Nat.mul_le_mul_left D hb)) hX
  have h20:=Nat.mul_le_mul_left 20 hm
  convert h20 using 1 <;> first | rfl | (rw [pow_add];ring)

theorem nativeBudget_operations_product (D Q X G : ℕ) (hX : X≤G*Q^64) :
    20*(D*X)≤(20*(D*G))*Q^64 := by
  have hm:=Nat.mul_le_mul_left (20*D) hX
  convert hm using 1 <;> ring

theorem nativeBudget_charge_normalization (C O Q a : ℕ) :
    40000*(2*(20*C)+4)^2*(20*O)*Q^(2*(a+128)+64)=
      40000*(40*C+4)^2*(20*O)*Q^(2*a+320) := by
  rw [show 2*(a+128)+64=2*a+320 by omega]
  rw [show 2*(20*C)+4=40*C+4 by ring]

end CircuitRecursion
