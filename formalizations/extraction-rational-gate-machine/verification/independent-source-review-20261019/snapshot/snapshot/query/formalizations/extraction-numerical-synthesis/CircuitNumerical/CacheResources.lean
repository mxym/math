import CircuitNumerical.CachedNumericalSK

namespace CircuitRecursion

def cachePrecisionBudget (L p : ℕ) : ℕ := 51200000*(L+1)*(p+1)^9

theorem cachedNumericalRun_query_bounds {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (f : QuaternionOracle) :
    (cachedNumericalRun entry inverseLabel table L p f).gateRequests.length≤
      m*(cachePrecisionBudget L p+1) ∧
    (cachedNumericalRun entry inverseLabel table L p f).targetRequests.length≤
      cachePrecisionBudget L p+1 := by
  rw [cachedNumericalRun_gateRequests,cachedNumericalRun_targetRequests]
  have h := numericalDemand_precision_bound L p
  exact ⟨Nat.mul_le_mul_left m (Nat.add_le_add_right h 1),Nat.add_le_add_right h 1⟩

theorem cachedNumericalRun_precision_bounds {m n : ℕ} (entry : Fin m → QuaternionOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (f : QuaternionOracle) :
    (∀ x∈(cachedNumericalRun entry inverseLabel table L p f).gateRequests,
      x.2≤cachePrecisionBudget L p) ∧
    (∀ q∈(cachedNumericalRun entry inverseLabel table L p f).targetRequests,
      q≤cachePrecisionBudget L p) := by
  constructor
  · intro x hx
    exact (cachedNumericalRun_gatePrecision entry inverseLabel table L p f x hx).trans
      (numericalDemand_precision_bound L p)
  · intro q hq
    exact (cachedNumericalRun_targetPrecision entry inverseLabel table L p f q hq).trans
      (numericalDemand_precision_bound L p)

/-- One sign bit and the binary magnitude length of each supplied numerator.
The denominator is represented by the request precision, rather than expanded. -/
def dyadicPacketBits (f : DyadicQuaternionOracle) (q : ℕ) : ℕ :=
  ∑ i : Fin 4, (Nat.clog 2 (((f q).get i).natAbs+1)+1)

theorem dyadic_numerator_bits (f : DyadicQuaternionOracle) (U : SU2)
    (hf : DyadicQApproximates f U) (q : ℕ) (i : Fin 4) :
    Nat.clog 2 (((f q).get i).natAbs+1)+1≤q+3 := by
  have hr := dyadic_numerator_bound f U hf q i
  have hn : ((f q).get i).natAbs≤2^(q+1) := by
    have he : ((2:ℝ)^(q+1))=2*2^q := by rw [pow_succ]; ring
    rw [← he] at hr
    have hr' : ((((f q).get i).natAbs:ℕ):ℝ)≤(2:ℝ)^(q+1) := by
      simpa only [Nat.cast_natAbs,Int.cast_abs] using hr
    exact_mod_cast hr'
  have hs : Nat.clog 2 (((f q).get i).natAbs+1)≤q+2 := by
    apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr
    have hp : 1≤2^(q+1) := Nat.one_le_pow _ _ (by decide)
    have he : 2^(q+2)=2^(q+1)*2 := Nat.pow_succ _ _
    omega
  omega

theorem dyadicPacketBits_bound (f : DyadicQuaternionOracle) (U : SU2)
    (hf : DyadicQApproximates f U) (q : ℕ) : dyadicPacketBits f q≤4*(q+3) := by
  have h := Finset.sum_le_sum (s:=Finset.univ)
    (fun i (_ : i∈Finset.univ) => dyadic_numerator_bits f U hf q i)
  simpa [dyadicPacketBits] using h

/-- Exact total signed-numerator bits in the eager gate and target input
prefixes. This counts stored provider data, not intermediate arithmetic. -/
def cachedInputBits {m : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (f : DyadicQuaternionOracle) (P : ℕ) : ℕ :=
  (∑ q : Fin (P+1),dyadicPacketBits f q.val)+
    ∑ i : Fin m,∑ q : Fin (P+1),dyadicPacketBits (entry i) q.val

theorem cachedInputBits_bound {m : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (G : Fin m → SU2) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (f : DyadicQuaternionOracle) (U : SU2) (hf : DyadicQApproximates f U) (P : ℕ) :
    cachedInputBits entry f P≤4*(m+1)*(P+1)*(P+3) := by
  have one : ∀ (g : DyadicQuaternionOracle) (V : SU2),DyadicQApproximates g V →
      (∑ q : Fin (P+1),dyadicPacketBits g q.val)≤(P+1)*(4*(P+3)) := by
    intro g V hg
    have h := Finset.sum_le_sum (s:=Finset.univ) (fun (q : Fin (P+1)) (_ : q∈Finset.univ) =>
      (dyadicPacketBits_bound g V hg q.val).trans (Nat.mul_le_mul_left 4 (by omega : q.val+3≤P+3)))
    simpa using h
  have ht := one f U hf
  have he' := Finset.sum_le_sum (s:=Finset.univ)
    (fun i (_ : i∈Finset.univ) => one (entry i) (G i) (he i))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at he'
  unfold cachedInputBits
  nlinarith

theorem cachedInputBits_precision_bound {m : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (G : Fin m → SU2) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (f : DyadicQuaternionOracle) (U : SU2) (hf : DyadicQApproximates f U) (L p : ℕ) :
    cachedInputBits entry f (numericalDemand L (Nat.clog 2 (p+1)))≤
      4*(m+1)*(cachePrecisionBudget L p+1)*(cachePrecisionBudget L p+3) := by
  apply (cachedInputBits_bound entry G he f U hf _).trans
  have h := numericalDemand_precision_bound L p
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.add_le_add_right h 1))
    (Nat.add_le_add_right h 3)

end CircuitRecursion
