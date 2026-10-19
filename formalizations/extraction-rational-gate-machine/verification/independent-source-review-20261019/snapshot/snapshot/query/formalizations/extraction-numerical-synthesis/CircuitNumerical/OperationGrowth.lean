import CircuitNumerical.NumericalOperationCount

namespace CircuitRecursion

def slopeGrowth : ℕ := 2^40
def offsetGrowth : ℕ := 2^64

theorem pairOperationSlope_pos (n k : ℕ) : 1≤pairOperationSlope n k := by
  cases k <;> simp only [pairOperationSlope,correctionOperationSlope] <;> omega

theorem pairOperationSlope_bound (n k : ℕ) : pairOperationSlope n k≤(n+1)*slopeGrowth^k := by
  induction k with
  | zero => simp [pairOperationSlope]
  | succ k ih =>
    have hp := pairOperationSlope_pos n k
    have hs : pairOperationSlope n (k+1)≤slopeGrowth*pairOperationSlope n k := by
      simp only [pairOperationSlope,correctionOperationSlope]
      norm_num [slopeGrowth]
      omega
    apply hs.trans
    have ht := Nat.mul_le_mul_left slopeGrowth ih
    convert ht using 1 <;> first | rfl | rw [pow_succ]; ring

theorem pairOperationSlope_length_bound (n L k : ℕ) :
    pairOperationSlope n k*(L*25^k)≤(n+1)*offsetGrowth^k*L := by
  have ha := pairOperationSlope_bound n k
  have hb : (slopeGrowth*25)^k≤offsetGrowth^k := Nat.pow_le_pow_left (by norm_num [slopeGrowth,offsetGrowth]) _
  calc
    _≤((n+1)*slopeGrowth^k)*(L*25^k) := Nat.mul_le_mul_right _ ha
    _=(n+1)*(slopeGrowth*25)^k*L := by rw [mul_pow]; ring
    _≤_ := Nat.mul_le_mul_right L (Nat.mul_le_mul_left (n+1) hb)

theorem pairedOffset_step_bound (A B w H L : ℕ) (hH : 1≤H) (hA : A≤H)
    (hAw : A*w≤H*L) (hw : w≤H*L) (hB : B≤1000*H*(L+1)) :
    correctionOperationOffset (correctionOperationSlope A)
      (correctionOperationOffset A B w) (5*w)≤1000*H*(L+1)*offsetGrowth := by
  unfold correctionOperationOffset correctionOperationSlope offsetGrowth
  norm_num
  nlinarith

theorem pairOperationOffset_bound (n L k : ℕ) :
    pairOperationOffset n L k≤1000*(n+1)*(L+1)*offsetGrowth^k := by
  induction k with
  | zero => simp only [pairOperationOffset,pow_zero,mul_one]; nlinarith
  | succ k ih =>
    let H := (n+1)*offsetGrowth^k
    have hH : 1≤H := by
      have h := Nat.one_le_pow k offsetGrowth (by norm_num [offsetGrowth])
      dsimp [H]
      exact h.trans (Nat.le_mul_of_pos_left _ (by omega))
    have hbase : slopeGrowth^k≤offsetGrowth^k := Nat.pow_le_pow_left (by norm_num [slopeGrowth,offsetGrowth]) _
    have hA : pairOperationSlope n k≤H :=
      (pairOperationSlope_bound n k).trans (Nat.mul_le_mul_left _ hbase)
    have hw : L*25^k≤H*L := by
      have h := Nat.pow_le_pow_left (by norm_num [offsetGrowth] : 25≤offsetGrowth) k
      dsimp [H]
      calc
        _≤L*offsetGrowth^k := Nat.mul_le_mul_left L h
        _≤(n+1)*(L*offsetGrowth^k) := Nat.le_mul_of_pos_left _ (by omega)
        _=_ := by ring
    have hB : pairOperationOffset n L k≤1000*H*(L+1) := by
      convert ih using 1 <;> dsimp [H] <;> ring
    have h := pairedOffset_step_bound _ _ (L*25^k) H L hH hA
      (pairOperationSlope_length_bound n L k) hw hB
    change correctionOperationOffset _ _ _≤_
    apply h.trans_eq
    dsimp [H]
    rw [pow_succ]
    ring

theorem tracedPairWord_literal_operations {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L k : ℕ)
    (hL : ∀ j,(table j).length≤L) (f : QuaternionOracle) :
    (tracedPairWord (fun i p => .literal (entry i p)) inverseLabel table k
      (fun p => .literal (f p))).operations≤1001*(n+1)*(L+1)*offsetGrowth^k := by
  have h := tracedPairWord_operations (fun i p => .literal (entry i p)) (fun _ _ => le_refl 1)
    inverseLabel table L hL k (fun p => .literal (f p)) 1 (fun _ => le_refl 1)
  have ha := pairOperationSlope_bound n k
  have hb := pairOperationOffset_bound n L k
  have ht := Nat.pow_le_pow_left (by norm_num [slopeGrowth,offsetGrowth] : slopeGrowth≤offsetGrowth) k
  have hA : pairOperationSlope n k≤(n+1)*offsetGrowth^k := ha.trans (Nat.mul_le_mul_left _ ht)
  nlinarith

theorem offsetGrowth_precision_bound (p : ℕ) :
    offsetGrowth^(Nat.clog 2 (p+1))≤offsetGrowth*(p+1)^64 := by
  have h := pow_clog_two_le (p+1) (by omega)
  calc
    _=(2^Nat.clog 2 (p+1))^64 := by
      unfold offsetGrowth
      rw [← Nat.pow_mul,← Nat.pow_mul,Nat.mul_comm]
    _≤(2*(p+1))^64 := Nat.pow_le_pow_left h _
    _=_ := by rw [mul_pow]; rfl

end CircuitRecursion
