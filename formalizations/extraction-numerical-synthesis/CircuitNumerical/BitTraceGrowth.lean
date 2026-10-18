import CircuitNumerical.NumericalBitTrace

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

def traceTGrowth : ℕ := 2^24
def traceSGrowth : ℕ := 2^64
def traceRGrowth : ℕ := 2^128

theorem pairTraceT_pos (n k : ℕ) : 1≤pairTraceT n k := by
  cases k <;> simp only [pairTraceT,correctionTraceT] <;> omega

theorem pairTraceT_bound (n k : ℕ) : pairTraceT n k≤2*(n+1)*traceTGrowth^k := by
  induction k with
  | zero => simp [pairTraceT]
  | succ k ih =>
    have hp:=pairTraceT_pos n k
    have hs : pairTraceT n (k+1)≤traceTGrowth*pairTraceT n k := by
      simp only [pairTraceT,correctionTraceT]
      norm_num [traceTGrowth]
      omega
    have h:=Nat.mul_le_mul_left traceTGrowth ih
    apply hs.trans
    convert h using 1 <;> first | rfl | rw [pow_succ];ring

theorem numericalThreshold_pow_bound (k : ℕ) : numericalThreshold k≤44*2^k := by
  have h:=Nat.one_le_pow k 2 (by decide)
  unfold numericalThreshold
  omega

theorem traceT_threshold_bound (n k : ℕ) :
    pairTraceT n k*numericalThreshold k≤88*(n+1)*(traceTGrowth*2)^k := by
  have h:=Nat.mul_le_mul (pairTraceT_bound n k) (numericalThreshold_pow_bound k)
  convert h using 1 <;> first | rfl | rw [mul_pow];ring

theorem pairedTraceS_step (S T t H : ℕ) (hH : 1≤H) (hS : S≤1000000*H)
    (hT : T≤2*H) (hTt : T*t≤88*H) (ht : t≤44*H) :
    correctionTraceS (correctionTraceS S T t) (correctionTraceT T) t≤1000000*H*traceSGrowth := by
  unfold correctionTraceS correctionTraceT traceSGrowth
  norm_num
  nlinarith

theorem pairTraceS_bound (n k : ℕ) : pairTraceS n k≤1000000*(n+1)*traceSGrowth^k := by
  induction k with
  | zero => simp only [pairTraceS,pow_zero,mul_one];omega
  | succ k ih =>
    let H:=(n+1)*traceSGrowth^k
    have hH : 1≤H := by
      have h:=Nat.one_le_pow k traceSGrowth (by norm_num [traceSGrowth])
      exact h.trans (Nat.le_mul_of_pos_left _ (by omega))
    have hS : pairTraceS n k≤1000000*H := by simpa only [H,Nat.mul_assoc] using ih
    have hT : pairTraceT n k≤2*H := by
      apply (pairTraceT_bound n k).trans
      have h:=Nat.pow_le_pow_left (by norm_num [traceTGrowth,traceSGrowth] : traceTGrowth≤traceSGrowth) k
      simpa only [H,Nat.mul_assoc] using Nat.mul_le_mul_left (2*(n+1)) h
    have hTt : pairTraceT n k*numericalThreshold k≤88*H := by
      apply (traceT_threshold_bound n k).trans
      have h:=Nat.pow_le_pow_left (by norm_num [traceTGrowth,traceSGrowth] : traceTGrowth*2≤traceSGrowth) k
      simpa only [H,Nat.mul_assoc] using Nat.mul_le_mul_left (88*(n+1)) h
    have ht : numericalThreshold k≤44*H := by
      apply (numericalThreshold_pow_bound k).trans
      have h:=Nat.pow_le_pow_left (by norm_num [traceSGrowth] : 2≤traceSGrowth) k
      have hn : traceSGrowth^k≤H := Nat.le_mul_of_pos_left _ (by omega)
      exact Nat.mul_le_mul_left 44 (h.trans hn)
    have hs:=pairedTraceS_step _ _ _ H hH hS hT hTt ht
    change correctionTraceS _ _ _≤_
    apply hs.trans_eq
    dsimp [H]
    rw [pow_succ]
    ring

theorem pairedTraceR_step (S T R gateB L t H : ℕ) (hH : 1≤H)
    (hS : S≤1000000*H) (hT : T≤2*H) (hTt : T*t≤88*H)
    (hTX : T*((gateB+2)*L)≤2*H) (hX : (gateB+2)*L≤H)
    (ht : t≤44*H) (hR : R≤1000000000000*H) :
    correctionTraceR (correctionTraceS S T t) (correctionTraceT T)
      (correctionTraceR S T R gateB L t) gateB (5*L) t≤1000000000000*H*traceRGrowth := by
  unfold correctionTraceR correctionTraceS correctionTraceT traceRGrowth
  norm_num
  nlinarith

theorem mul_extra_scale (a x y Q : ℕ) (hxy : x≤y) (hQ : 1≤Q) : a*x≤a*Q*y := by
  calc
    _≤a*y := Nat.mul_le_mul_left a hxy
    _≤_ := by
      have h:=Nat.mul_le_mul_right (a*y) hQ
      convert h using 1 <;> ring

theorem pairTraceR_bound (n gateB L k : ℕ) :
    pairTraceR n gateB L k≤1000000000000*(n+1)*(gateB+2)*(L+1)*traceRGrowth^k := by
  induction k with
  | zero =>
    simp only [pairTraceR,pow_zero,mul_one]
    have h : 2*(gateB+2)*L+12≤1000000000000*(gateB+2)*(L+1) := by nlinarith
    convert Nat.mul_le_mul_left (n+1) h using 1 <;> ring
  | succ k ih =>
    let Q:=(gateB+2)*(L+1)
    let H:=(n+1)*Q*traceRGrowth^k
    have hQ : 1≤Q := by dsimp [Q];nlinarith
    have hH : 1≤H := by
      have hp:=Nat.one_le_pow k traceRGrowth (by norm_num [traceRGrowth])
      dsimp [H]
      simpa only [one_mul] using Nat.mul_le_mul (Nat.mul_le_mul (by omega : 1≤n+1) hQ) hp
    have h64 : traceSGrowth^k≤traceRGrowth^k :=
      Nat.pow_le_pow_left (by norm_num [traceSGrowth,traceRGrowth]) _
    have h24 : traceTGrowth^k≤traceRGrowth^k :=
      Nat.pow_le_pow_left (by norm_num [traceTGrowth,traceRGrowth]) _
    have h25 : (traceTGrowth*2)^k≤traceRGrowth^k :=
      Nat.pow_le_pow_left (by norm_num [traceTGrowth,traceRGrowth]) _
    have hS : pairTraceS n k≤1000000*H := by
      apply (pairTraceS_bound n k).trans
      simpa only [H,Nat.mul_assoc] using mul_extra_scale (1000000*(n+1)) _ _ Q h64 hQ
    have hT : pairTraceT n k≤2*H := by
      apply (pairTraceT_bound n k).trans
      simpa only [H,Nat.mul_assoc] using mul_extra_scale (2*(n+1)) _ _ Q h24 hQ
    have hTt : pairTraceT n k*numericalThreshold k≤88*H := by
      apply (traceT_threshold_bound n k).trans
      simpa only [H,Nat.mul_assoc] using mul_extra_scale (88*(n+1)) _ _ Q h25 hQ
    have hTX : pairTraceT n k*((gateB+2)*(L*25^k))≤2*H := by
      have h:=Nat.mul_le_mul_right ((gateB+2)*(L*25^k)) (pairTraceT_bound n k)
      have hp : (traceTGrowth*25)^k≤traceRGrowth^k :=
        Nat.pow_le_pow_left (by norm_num [traceTGrowth,traceRGrowth]) _
      calc
        _≤(2*(n+1)*traceTGrowth^k)*((gateB+2)*(L*25^k)) := h
        _=2*(n+1)*(gateB+2)*L*(traceTGrowth*25)^k := by rw [mul_pow];ring
        _≤2*(n+1)*(gateB+2)*L*traceRGrowth^k := Nat.mul_le_mul_left _ hp
        _≤2*(n+1)*(gateB+2)*(L+1)*traceRGrowth^k :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ L))
        _=2*H := by dsimp [H,Q];ring
    have hX : (gateB+2)*(L*25^k)≤H := by
      have hp : 25^k≤traceRGrowth^k := Nat.pow_le_pow_left (by norm_num [traceRGrowth]) _
      calc
        _=(gateB+2)*L*25^k := by ring
        _≤(gateB+2)*L*traceRGrowth^k := Nat.mul_le_mul_left _ hp
        _≤(gateB+2)*(L+1)*traceRGrowth^k :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ L))
        _≤(n+1)*((gateB+2)*(L+1)*traceRGrowth^k) := Nat.le_mul_of_pos_left _ (by omega)
        _=H := by dsimp [H,Q];ring
    have ht : numericalThreshold k≤44*H := by
      apply (numericalThreshold_pow_bound k).trans
      have hp : 2^k≤traceRGrowth^k := Nat.pow_le_pow_left (by norm_num [traceRGrowth]) _
      have h:=mul_extra_scale (n+1) _ _ Q hp hQ
      have hh : 2^k≤H := by
        apply (Nat.le_mul_of_pos_left _ (by omega : 0<n+1)).trans
        exact h
      exact Nat.mul_le_mul_left 44 hh
    have hR : pairTraceR n gateB L k≤1000000000000*H := by
      simpa only [H,Q,Nat.mul_assoc] using ih
    have h:=pairedTraceR_step _ _ _ gateB (L*25^k) _ H hH hS hT hTt hTX hX ht hR
    change correctionTraceR _ _ _ _ _ _≤_
    apply h.trans_eq
    dsimp [H,Q]
    rw [pow_succ]
    ring

theorem traceRGrowth_precision_bound (p : ℕ) :
    traceRGrowth^(Nat.clog 2 (p+1))≤traceRGrowth*(p+1)^128 := by
  have h:=pow_clog_two_le (p+1) (by omega)
  calc
    _=(2^Nat.clog 2 (p+1))^128 := by
      unfold traceRGrowth
      rw [← Nat.pow_mul,← Nat.pow_mul,Nat.mul_comm]
    _≤(2*(p+1))^128 := Nat.pow_le_pow_left h _
    _=_ := by rw [mul_pow];rfl

end CircuitRecursion
