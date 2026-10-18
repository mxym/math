import CircuitNumerical.IntegerTuplePackets

namespace CircuitRecursion

def IntegerPacket.inverse (a : IntegerPacket) : IntegerPacket :=
  ⟨List.Vector.ofFn (fun i => if i=0 then a.numerators.get i else -a.numerators.get i),
    a.denominator,a.denominator_pos⟩

theorem IntegerPacket.inverse_value (a : IntegerPacket) :
    a.inverse.value=List.Vector.ofFn (fun i => if i=0 then a.value.get i else -a.value.get i) := by
  apply List.Vector.ext
  intro i
  simp only [inverse,value,List.Vector.get_map,List.Vector.get_ofFn]
  split_ifs <;> simp only [Int.cast_neg] <;> ring

theorem IntegerPacket.inverse_height (a : IntegerPacket) (B : ℕ) (ha : IntegerPacketHeight a B) :
    IntegerPacketHeight a.inverse B := by
  refine ⟨ha.1,fun i => ?_⟩
  simp only [inverse,List.Vector.get_ofFn]
  split_ifs <;> simpa only [Int.natAbs_neg] using ha.2 i

def IntegerPacket.distanceNumerator (a b : IntegerPacket) (i : Fin 4) : ℤ :=
  a.numerators.get i*(b.denominator:ℤ)-b.numerators.get i*(a.denominator:ℤ)

def IntegerPacket.distanceScalar (a b : IntegerPacket) : IntegerScalar :=
  ⟨∑ i,(distanceNumerator a b i)^2,(a.denominator*b.denominator)^2,
    pow_pos (Nat.mul_pos a.denominator_pos b.denominator_pos) _⟩

theorem IntegerPacket.distanceScalar_value (a b : IntegerPacket) :
    (a.distanceScalar b).value=rationalSquaredDistance a.value b.value := by
  have ha : (a.denominator:ℚ)≠0 := by exact_mod_cast a.denominator_pos.ne'
  have hb : (b.denominator:ℚ)≠0 := by exact_mod_cast b.denominator_pos.ne'
  simp only [distanceScalar,IntegerScalar.value,rationalSquaredDistance,value,List.Vector.get_map,
    distanceNumerator,Int.cast_sum,Int.cast_pow,Int.cast_sub,Int.cast_mul,Int.cast_natCast,
    Nat.cast_pow,Nat.cast_mul,Fin.sum_univ_four]
  push_cast
  field_simp
  <;> ring

theorem IntegerPacket.distanceNumerator_bound (a b : IntegerPacket) (A B : ℕ)
    (ha : IntegerPacketHeight a A) (hb : IntegerPacketHeight b B) (i : Fin 4) :
    (distanceNumerator a b i).natAbs≤2^(A+B+1) := by
  have h := Int.natAbs_add_le (a.numerators.get i*(b.denominator:ℤ))
    (-(b.numerators.get i*(a.denominator:ℤ)))
  simp only [Int.natAbs_neg,Int.natAbs_mul,Int.natAbs_natCast,← sub_eq_add_neg] at h
  have h1 := Nat.mul_le_mul (ha.2 i) hb.1
  have h2 := Nat.mul_le_mul (hb.2 i) ha.1
  have he : 2^(A+B+1)=2^A*2^B+2^A*2^B := by rw [pow_succ,pow_add];ring
  unfold distanceNumerator
  nlinarith

theorem IntegerPacket.distanceScalar_height (a b : IntegerPacket) (A B : ℕ)
    (ha : IntegerPacketHeight a A) (hb : IntegerPacketHeight b B) :
    IntegerScalarHeight (a.distanceScalar b) (2*A+2*B+4) := by
  have he : 4*(2^(A+B+1))^2=2^(2*A+2*B+4) := by
    rw [← pow_mul]
    have hp : 2*A+2*B+4=(A+B+1)*2+2 := by ring
    rw [hp,pow_add]
    norm_num
    ring
  constructor
  · have hd := Nat.mul_le_mul ha.1 hb.1
    have hsq := Nat.pow_le_pow_left hd 2
    change (a.denominator*b.denominator)^2≤_
    rw [← pow_add,← pow_mul] at hsq
    have hp : 2^((A+B)*2)≤2^(2*A+2*B+4) := Nat.pow_le_pow_right (by decide) (by omega)
    exact hsq.trans hp
  · have hs := Int.natAbs_sum_le Finset.univ (fun i : Fin 4 => (distanceNumerator a b i)^2)
    have ht : ∀ i,((distanceNumerator a b i)^2).natAbs≤(2^(A+B+1))^2 := by
      intro i
      simpa only [Int.natAbs_pow] using Nat.pow_le_pow_left (distanceNumerator_bound a b A B ha hb i) 2
    have h := Finset.sum_le_sum (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => ht i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,he] at h
    exact hs.trans h

end CircuitRecursion
