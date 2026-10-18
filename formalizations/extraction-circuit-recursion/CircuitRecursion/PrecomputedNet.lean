import CircuitRecursion.NetOracle

namespace CircuitRecursion

/-- A finite offline table enumerated solely from the alphabet size and a
fixed maximum length. Duplicates are harmless; no matrix comparison occurs. -/
def boundedWords (m : ℕ) : ℕ → List (List (Fin m))
  | 0 => [[]]
  | L+1 => boundedWords m L++(List.finRange m).flatMap
      (fun i => (boundedWords m L).map (List.cons i))

theorem boundedWords_mem (m L : ℕ) (w : List (Fin m)) :
    w∈boundedWords m L ↔ w.length≤L := by
  induction L generalizing w with
  | zero => simp [boundedWords]
  | succ L ih =>
    constructor
    · intro h
      rcases List.mem_append.mp h with h|h
      · have ht := (ih w).mp h; omega
      · obtain ⟨i,hi,h⟩ := List.mem_flatMap.mp h
        obtain ⟨v,hv,rfl⟩ := List.mem_map.mp h
        have ht := (ih v).mp hv
        simpa only [List.length_cons] using Nat.succ_le_succ ht
    · intro h
      cases w with
      | nil =>
        exact List.mem_append_left _ ((ih []).mpr (by simp))
      | cons i v =>
        apply List.mem_append_right
        apply List.mem_flatMap.mpr
        refine ⟨i,by simp,?_⟩
        exact List.mem_map.mpr ⟨v,(ih v).mpr (by simpa only [List.length_cons] using Nat.le_of_succ_le_succ h),rfl⟩

theorem boundedWords_length (m L : ℕ) : (boundedWords m L).length=(m+1)^L := by
  induction L with
  | zero => rfl
  | succ L ih =>
    simp [boundedWords,List.length_flatMap,ih,pow_succ]
    ring

/-- The offline net is derived internally from universality and compactness.
The table contains only finitely many labels and may be fixed once per
library; its potentially large size is a library-dependent constant. -/
theorem precomputedNet_exists {m : ℕ} (G : Fin m → SU2)
    (hinv : ∀ i,∃ j,G j=(G i)⁻¹)
    (huniversal : Dense (Subgroup.closure (Set.range G) : Set SU2)) :
    ∃ (L n : ℕ) (table : Fin (n+1) → List (Fin m)),
      (∀ j,(table j).length≤L) ∧
      (∀ U : SU2,∃ j,unitaryDistance (su2AsUnitary U)
        (su2AsUnitary (instructionWordValue G (table j)))≤1/576) := by
  obtain ⟨L,hL⟩ := su2_uniform_instructionLength G hinv huniversal (1/576) (by norm_num)
  let words := boundedWords m L
  have hpos : 0<words.length := by
    rw [boundedWords_length]
    positivity
  let n := words.length-1
  have hn : n+1=words.length := by omega
  let table : Fin (n+1) → List (Fin m) := fun j => words.get (Fin.cast hn j)
  refine ⟨L,n,table,?_,?_⟩
  · intro j
    exact (boundedWords_mem m L _).mp (List.get_mem words (Fin.cast hn j))
  · intro U
    obtain ⟨w,hw,he⟩ := hL U
    obtain ⟨i,hi⟩ := List.get_of_mem ((boundedWords_mem m L w).mpr hw)
    refine ⟨Fin.cast hn.symm i,?_⟩
    have ht : table (Fin.cast hn.symm i)=w := by
      have hc : Fin.cast hn (Fin.cast hn.symm i)=i := Fin.ext rfl
      change words.get (Fin.cast hn (Fin.cast hn.symm i))=w
      rw [hc]
      exact hi
    rw [ht]
    exact he.le

/-- A complete numerical base selector from effective entry packets. The
only online semantic premises certify the input oracles. Coverage and the
word table are obtained from the proved universal-library theorem above. -/
theorem numericalBase_exists {m : ℕ} (G : Fin m → SU2)
    (hinv : ∀ i,∃ j,G j=(G i)⁻¹)
    (huniversal : Dense (Subgroup.closure (Set.range G) : Set SU2)) :
    ∃ (L n : ℕ) (table : Fin (n+1) → List (Fin m)),
      ∀ (entry : Fin m → QuaternionOracle), (∀ i,QApproximates (entry i) (G i)) →
      ∀ (U : SU2) (target : QuaternionOracle),QApproximates target U →
        (fixedNetWord entry table target).length≤L ∧
        unitaryDistance (su2AsUnitary U)
          (su2AsUnitary (instructionWordValue G (fixedNetWord entry table target)))≤1/288 := by
  obtain ⟨L,n,table,hL,hcover⟩ := precomputedNet_exists G hinv huniversal
  exact ⟨L,n,table,fun entry he U target ht =>
    ⟨fixedNetWord_length entry table L hL target,
      fixedNetWord_correct entry G he table hcover target U ht⟩⟩

/-- A concrete dyadic entry interface. A query returns four integer
numerators; the shared denominator is exactly 2^p. Provider bit costs are
an additional input-model assumption, not a theorem of this interface. -/
abbrev DyadicQuaternionOracle := ℕ → List.Vector ℤ 4

def dyadicQuaternionOracle (f : DyadicQuaternionOracle) : QuaternionOracle := fun p =>
  (f p).map (fun a : ℤ => (a:ℚ)/(2:ℚ)^p)

def DyadicQApproximates (f : DyadicQuaternionOracle) (U : SU2) : Prop :=
  QApproximates (dyadicQuaternionOracle f) U

theorem dyadic_numerator_bound (f : DyadicQuaternionOracle) (U : SU2)
    (hf : DyadicQApproximates f U) (p : ℕ) (i : Fin 4) :
    |((f p).get i:ℝ)|≤2*(2:ℝ)^p := by
  have he := hf p i
  simp only [dyadicQuaternionOracle,List.Vector.get_map,Rat.cast_div,Rat.cast_intCast,
    Rat.cast_pow,Rat.cast_ofNat] at he
  have hb := quaternionCoordinates_bound U i
  have he1 : (1/2:ℝ)^p≤1 := pow_le_one₀ (by norm_num) (by norm_num)
  have ha : |((f p).get i:ℝ)/(2:ℝ)^p|≤2 := by
    have ht := abs_add_le (((f p).get i:ℝ)/(2:ℝ)^p-quaternionCoordinates U i)
      (quaternionCoordinates U i)
    rw [sub_add_cancel] at ht
    linarith
  rw [abs_div,abs_of_pos (by positivity : (0:ℝ)<2^p)] at ha
  exact (div_le_iff₀ (by positivity : (0:ℝ)<2^p)).mp ha

end CircuitRecursion
