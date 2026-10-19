import CircuitNumerical.IntegerScalars

namespace CircuitRecursion

def IntegerScalar.ofRat (q : ℚ) : IntegerScalar := ⟨q.num,q.den,q.den_pos⟩

theorem IntegerScalar.ofRat_value (q : ℚ) : (ofRat q).value=q := Rat.num_div_den q

theorem IntegerScalar.canonical_height (a : IntegerScalar) (B : ℕ) (ha : IntegerScalarHeight a B) :
    IntegerScalarHeight (ofRat a.value) B := by
  have hden : (a.denominator:ℚ)≠0 := by exact_mod_cast a.denominator_pos.ne'
  have he : mkRat a.numerator a.denominator=a.value := by
    simpa only [Rat.cast_id,value] using Rat.cast_mkRat_of_ne_zero (α:=ℚ) a.numerator hden
  change (a.value).den≤2^B ∧ (a.value).num.natAbs≤2^B
  rw [← he]
  simp only [Rat.num_mkRat,Rat.den_mkRat,if_neg a.denominator_pos.ne']
  exact ⟨(Nat.div_le_self _ _).trans ha.1,(Int.natAbs_ediv_le_natAbs _ _).trans ha.2⟩

def IntegerPacket.coordinate (a : IntegerPacket) (i : Fin 4) : IntegerScalar :=
  ⟨a.numerators.get i,a.denominator,a.denominator_pos⟩

theorem IntegerPacket.coordinate_value (a : IntegerPacket) (i : Fin 4) :
    (a.coordinate i).value=a.value.get i := by
  simp only [coordinate,IntegerScalar.value,value,List.Vector.get_map]

theorem IntegerPacket.coordinate_height (a : IntegerPacket) (B : ℕ)
    (ha : IntegerPacketHeight a B) (i : Fin 4) : IntegerScalarHeight (a.coordinate i) B :=
  ⟨ha.1,ha.2 i⟩

def IntegerPacket.ofScalars (s : Fin 4 → IntegerScalar) : IntegerPacket :=
  ⟨List.Vector.ofFn (fun i => (s i).numerator*
      ((∏ j∈(Finset.univ.erase i),(s j).denominator:ℕ):ℤ)),
    ∏ j,(s j).denominator,Finset.prod_pos (fun i _ => (s i).denominator_pos)⟩

theorem IntegerPacket.ofScalars_value (s : Fin 4 → IntegerScalar) :
    (ofScalars s).value=List.Vector.ofFn (fun i => (s i).value) := by
  apply List.Vector.ext
  intro i
  have he := Finset.mul_prod_erase Finset.univ (fun j : Fin 4 => (s j).denominator) (Finset.mem_univ i)
  have hpos : (0:ℕ)<∏ j∈Finset.univ.erase i,(s j).denominator :=
    Finset.prod_pos (fun j _ => (s j).denominator_pos)
  have hp : ((∏ j∈Finset.univ.erase i,(s j).denominator:ℕ):ℚ)≠0 := by exact_mod_cast hpos.ne'
  have hd : ((s i).denominator:ℚ)≠0 := by exact_mod_cast (s i).denominator_pos.ne'
  simp only [ofScalars,value,List.Vector.get_map,List.Vector.get_ofFn,IntegerScalar.value,
    Int.cast_mul,Int.cast_natCast]
  rw [← he]
  push_cast
  push_cast at hp
  field_simp

theorem product_denominator_bound (s : Fin 4 → IntegerScalar) (B : Fin 4 → ℕ)
    (hs : ∀ i,IntegerScalarHeight (s i) (B i)) (t : Finset (Fin 4)) :
    (∏ i∈t,(s i).denominator)≤2^(∑ i∈t,B i) := by
  have h := Finset.prod_le_prod (s:=t) (fun i (_ : i∈t) => (hs i).1)
  simpa only [Finset.prod_pow_eq_pow_sum] using h

theorem IntegerPacket.ofScalars_height (s : Fin 4 → IntegerScalar) (B : Fin 4 → ℕ)
    (hs : ∀ i,IntegerScalarHeight (s i) (B i)) :
    IntegerPacketHeight (ofScalars s) (∑ i,B i) := by
  constructor
  · exact product_denominator_bound s B hs Finset.univ
  · intro i
    have hp := product_denominator_bound s B hs (Finset.univ.erase i)
    have hn := Nat.mul_le_mul (hs i).2 hp
    have he := Finset.add_sum_erase Finset.univ B (Finset.mem_univ i)
    simp only [ofScalars,List.Vector.get_ofFn]
    change ((s i).numerator*((∏ j∈Finset.univ.erase i,(s j).denominator:ℕ):ℤ)).natAbs≤_
    simpa only [Int.natAbs_mul,Int.natAbs_natCast,← pow_add,he] using hn

def IntegerPacket.ofVector (q : List.Vector ℚ 4) : IntegerPacket :=
  ofScalars (fun i => IntegerScalar.ofRat (q.get i))

theorem IntegerPacket.ofVector_value (q : List.Vector ℚ 4) : (ofVector q).value=q := by
  rw [ofVector,ofScalars_value]
  apply List.Vector.ext
  intro i
  simp only [List.Vector.get_ofFn,IntegerScalar.ofRat_value]

theorem IntegerPacket.ofVector_height (a : IntegerPacket) (B : ℕ) (ha : IntegerPacketHeight a B) :
    IntegerPacketHeight (ofVector a.value) (4*B) := by
  have hs : ∀ i,IntegerScalarHeight (IntegerScalar.ofRat (a.value.get i)) B := by
    intro i
    rw [← coordinate_value]
    exact IntegerScalar.canonical_height _ B (coordinate_height a B ha i)
  have h := ofScalars_height (fun i => IntegerScalar.ofRat (a.value.get i)) (fun _ => B) hs
  simpa only [ofVector,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using h

end CircuitRecursion
