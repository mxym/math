import CircuitNumerical.CachedArithmeticSynthesis

namespace CircuitRecursion

/-- Four integer numerators with a shared positive denominator. This is an
explicit numerical representation; multiplication does not normalize four
unrelated rational denominators. -/
structure IntegerPacket where
  numerators : List.Vector ℤ 4
  denominator : ℕ
  denominator_pos : 0<denominator

def IntegerPacket.value (a : IntegerPacket) : List.Vector ℚ 4 :=
  a.numerators.map (fun x : ℤ => (x:ℚ)/(a.denominator:ℚ))

def IntegerPacket.one : IntegerPacket :=
  ⟨List.Vector.ofFn ![1,0,0,0],1,by decide⟩

def IntegerPacket.mul (a b : IntegerPacket) : IntegerPacket :=
  ⟨List.Vector.ofFn (quaternionProduct a.numerators.get b.numerators.get),
    a.denominator*b.denominator,Nat.mul_pos a.denominator_pos b.denominator_pos⟩

theorem IntegerPacket.mul_value (a b : IntegerPacket) :
    (a.mul b).value=List.Vector.ofFn (quaternionProduct a.value.get b.value.get) := by
  apply List.Vector.ext
  intro i
  have ha : (a.denominator:ℚ)≠0 := by exact_mod_cast a.denominator_pos.ne'
  have hb : (b.denominator:ℚ)≠0 := by exact_mod_cast b.denominator_pos.ne'
  simp only [mul,value,List.Vector.get_map,List.Vector.get_ofFn,quaternionProduct,Int.cast_sum,
    Int.cast_mul,Nat.cast_mul,Int.cast_id]
  simp only [Fin.sum_univ_four]
  field_simp
  <;> ring

def IntegerPacketHeight (a : IntegerPacket) (B : ℕ) : Prop :=
  a.denominator≤2^B ∧ ∀ i,(a.numerators.get i).natAbs≤2^B

theorem quaternionSign_natAbs (i j : Fin 4) : (quaternionSign i j).natAbs=1 := by
  fin_cases i <;> fin_cases j <;> norm_num [quaternionSign]

theorem integerQuaternionProduct_bound (a b : Fin 4 → ℤ) (A B : ℕ)
    (ha : ∀ i,(a i).natAbs≤A) (hb : ∀ i,(b i).natAbs≤B) (i : Fin 4) :
    (quaternionProduct a b i).natAbs≤4*A*B := by
  have ht : ∀ j,((quaternionSign i j)*a j*b (quaternionRight i j)).natAbs≤A*B := by
    intro j
    simp only [Int.natAbs_mul,quaternionSign_natAbs,one_mul]
    exact Nat.mul_le_mul (ha j) (hb _)
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j (_ : j∈Finset.univ) => ht j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hs
  exact (Int.natAbs_sum_le _ _).trans (hs.trans_eq (by ring))

theorem IntegerPacketHeight.mono (a : IntegerPacket) (A B : ℕ)
    (h : IntegerPacketHeight a A) (hAB : A≤B) : IntegerPacketHeight a B := by
  have hp := Nat.pow_le_pow_right (by decide : 1≤2) hAB
  exact ⟨h.1.trans hp,fun i => (h.2 i).trans hp⟩

theorem IntegerPacket.one_height : IntegerPacketHeight IntegerPacket.one 0 := by
  constructor
  · exact le_refl 1
  · intro i
    fin_cases i <;> norm_num [one]

theorem IntegerPacket.mul_height (a b : IntegerPacket) (A B : ℕ)
    (ha : IntegerPacketHeight a A) (hb : IntegerPacketHeight b B) :
    IntegerPacketHeight (a.mul b) (A+B+2) := by
  have he : 4*2^A*2^B=2^(A+B+2) := by rw [pow_add,pow_add]; norm_num;ring
  constructor
  · have h := Nat.mul_le_mul ha.1 hb.1
    change a.denominator*b.denominator≤_
    nlinarith
  · intro i
    have h := integerQuaternionProduct_bound a.numerators.get b.numerators.get (2^A) (2^B) ha.2 hb.2 i
    simpa only [mul,List.Vector.get_ofFn,he] using h

abbrev IntegerPacketOracle := ℕ → IntegerPacket
def integerPacketOracle (f : IntegerPacketOracle) : QuaternionOracle := fun p => (f p).value

def integerPacketWord {m : ℕ} (entry : Fin m → IntegerPacketOracle) :
    List (Fin m) → IntegerPacketOracle
  | [],_ => IntegerPacket.one
  | i::w,p => (integerPacketWord entry w (p+4)).mul (entry i (p+4))

theorem integerPacketWord_value {m : ℕ} (entry : Fin m → IntegerPacketOracle) (w : List (Fin m)) :
    integerPacketOracle (integerPacketWord entry w)=
      quaternionWordOracle (fun i => integerPacketOracle (entry i)) w := by
  induction w with
  | nil =>
    funext p
    apply List.Vector.ext
    intro i
    fin_cases i <;> simp [integerPacketOracle,integerPacketWord,IntegerPacket.one,IntegerPacket.value,quaternionWordOracle,quaternionOracleOne]
  | cons i w ih =>
    funext p
    simpa only [integerPacketOracle,integerPacketWord,quaternionWordOracle,quaternionOracleMul,
      IntegerPacket.mul_value] using congrArg (fun f =>
        List.Vector.ofFn (quaternionProduct (f (p+4)).get ((entry i (p+4)).value).get)) ih

theorem integerPacketWord_height {m : ℕ} (entry : Fin m → IntegerPacketOracle) (B : ℕ)
    (he : ∀ i p,IntegerPacketHeight (entry i p) B) (w : List (Fin m)) (p : ℕ) :
    IntegerPacketHeight (integerPacketWord entry w p) ((B+2)*w.length) := by
  induction w generalizing p with
  | nil => exact IntegerPacket.one_height
  | cons i w ih =>
    have h := IntegerPacket.mul_height _ _ _ _ (ih (p+4)) (he i (p+4))
    convert h using 1 <;> first | rfl | simp only [List.length_cons]; ring

def dyadicIntegerPacket (f : DyadicQuaternionOracle) (p : ℕ) : IntegerPacket :=
  ⟨f p,2^p,by positivity⟩

theorem dyadicIntegerPacket_value (f : DyadicQuaternionOracle) (p : ℕ) :
    (dyadicIntegerPacket f p).value=dyadicQuaternionOracle f p := by
  simp only [dyadicIntegerPacket,IntegerPacket.value,dyadicQuaternionOracle,Nat.cast_pow,Nat.cast_ofNat]

theorem dyadicIntegerPacket_height (f : DyadicQuaternionOracle) (U : SU2)
    (hf : DyadicQApproximates f U) (p : ℕ) : IntegerPacketHeight (dyadicIntegerPacket f p) (p+1) := by
  constructor
  · exact Nat.pow_le_pow_right (by decide) (Nat.le_succ p)
  · intro i
    have h := dyadic_numerator_bound f U hf p i
    have he : (2:ℝ)^(p+1)=2*2^p := by rw [pow_succ];ring
    rw [← he] at h
    have hn : ((((f p).get i).natAbs:ℕ):ℝ)≤2^(p+1) := by
      simpa only [Nat.cast_natAbs,Int.cast_abs] using h
    exact_mod_cast hn

def cachedIntegerPacket (f : DyadicQuaternionOracle) (P q : ℕ) : IntegerPacket :=
  if q≤P then dyadicIntegerPacket f q else IntegerPacket.one

theorem IntegerPacket.one_value (q : ℕ) : IntegerPacket.one.value=quaternionOracleOne q := by
  apply List.Vector.ext
  intro i
  fin_cases i <;> simp [one,value,quaternionOracleOne]

theorem cachedIntegerPacket_value (f : DyadicQuaternionOracle) (P q : ℕ) :
    (cachedIntegerPacket f P q).value=
      readPacketCache (buildPacketCache (dyadicQuaternionOracle f) P).1 q := by
  by_cases h : q≤P
  · simp [cachedIntegerPacket,h,dyadicIntegerPacket_value,readPacketCache,buildPacketCache]
  · simp only [cachedIntegerPacket,if_neg h,IntegerPacket.one_value q,readPacketCache,dif_neg h]

theorem cachedIntegerPacket_height (f : DyadicQuaternionOracle) (U : SU2)
    (hf : DyadicQApproximates f U) (P q : ℕ) : IntegerPacketHeight (cachedIntegerPacket f P q) (P+1) := by
  unfold cachedIntegerPacket
  split_ifs with h
  · exact IntegerPacketHeight.mono _ _ _ (dyadicIntegerPacket_height f U hf q) (by omega)
  · exact IntegerPacketHeight.mono _ _ _ IntegerPacket.one_height (by omega)

/-- Actual cached word multiplication has a common-denominator representation
whose numerator/denominator binary exponents grow linearly in word length. -/
theorem cachedIntegerPacketWord_height {m : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (G : Fin m → SU2) (he : ∀ i,DyadicQApproximates (entry i) (G i)) (P : ℕ)
    (w : List (Fin m)) (q : ℕ) :
    IntegerPacketHeight (integerPacketWord (fun i => cachedIntegerPacket (entry i) P) w q)
      ((P+3)*w.length) := by
  exact integerPacketWord_height _ (P+1)
    (fun i q => cachedIntegerPacket_height (entry i) (G i) (he i) P q) w q

theorem cachedIntegerPacketWord_value {m : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (P : ℕ) (w : List (Fin m)) :
    integerPacketOracle (integerPacketWord (fun i => cachedIntegerPacket (entry i) P) w)=
      quaternionWordOracle (fun i => readPacketCache
        (buildPacketCache (dyadicQuaternionOracle (entry i)) P).1) w := by
  rw [integerPacketWord_value]
  congr 1
  funext i q
  exact cachedIntegerPacket_value (entry i) P q

theorem commonDenominator_binary_bound (a B : ℕ) (h : a≤2^B) :
    Nat.clog 2 (a+1)+1≤B+2 := by
  have hc : Nat.clog 2 (a+1)≤B+1 := by
    apply (Nat.clog_le_iff_le_pow (by decide : 1<2)).mpr
    have hp : 1≤2^B := Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    omega
  omega

theorem IntegerPacketHeight.binary_bounds (a : IntegerPacket) (B : ℕ) (h : IntegerPacketHeight a B) :
    Nat.clog 2 (a.denominator+1)+1≤B+2 ∧
    ∀ i,Nat.clog 2 ((a.numerators.get i).natAbs+1)+1≤B+2 :=
  ⟨commonDenominator_binary_bound _ B h.1,fun i => commonDenominator_binary_bound _ B (h.2 i)⟩

/-- A polynomial operand-size endpoint for the actual synthesized word's
cached matrix-product evaluator, valid at every queried output precision.
Factor-normalization arithmetic is a separate remaining operand-size task. -/
theorem cachedSynthesisWord_integerHeight {m n : ℕ} (entry : Fin m → DyadicQuaternionOracle)
    (G : Fin m → SU2) (he : ∀ i,DyadicQApproximates (entry i) (G i))
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m)) (L p : ℕ)
    (hL : ∀ j,(table j).length≤L) (f : DyadicQuaternionOracle) (q : ℕ) :
    let P := numericalDemand L (Nat.clog 2 (p+1))
    let w := (cachedArithmeticRun (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table L p
      (dyadicQuaternionOracle f)).word
    IntegerPacketHeight (integerPacketWord (fun i => cachedIntegerPacket (entry i) P) w q)
      ((cachePrecisionBudget L p+3)*(32*L*(p+1)^5)) := by
  dsimp only
  let P := numericalDemand L (Nat.clog 2 (p+1))
  let w := (cachedArithmeticRun (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table L p
    (dyadicQuaternionOracle f)).word
  have hw : w.length≤32*L*(p+1)^5 := by
    dsimp only [w]
    rw [cachedArithmeticRun_word,cachedNumericalRun_word _ _ table L p hL]
    have h := numericalPairWord_length (fun i => dyadicQuaternionOracle (entry i)) inverseLabel table L hL
      (Nat.clog 2 (p+1)) (dyadicQuaternionOracle f)
    have hp := Nat.mul_le_mul_left L (precisionDepth_length p)
    exact h.trans (by simpa only [Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using hp)
  have hheight := cachedIntegerPacketWord_height entry G he P w q
  apply IntegerPacketHeight.mono _ _ _ hheight
  exact Nat.mul_le_mul (Nat.add_le_add_right (numericalDemand_precision_bound L p) 3) hw

end CircuitRecursion
