import CircuitNumerical.NativeBinaryPacketInput

namespace CircuitRecursion

def wordPacketOne : WordIntegerPacket :=
  ⟨List.Vector.ofFn (fun i : Fin 4 => if i=0 then ⟨false,[true]⟩ else ⟨false,[]⟩),[true],by
      intro i
      simp only [List.Vector.get_ofFn]
      split_ifs
      · exact ⟨.one,by intro _;rfl⟩
      · exact ⟨.nil,by intro _;rfl⟩,
    .one,by decide⟩

theorem wordPacketOne_decode : wordPacketOne.decode=IntegerPacket.one := by
  apply integerPacket_eq_components
  · apply List.Vector.ext
    intro i
    fin_cases i <;> rfl
  · rfl

abbrev NativePacketDataOracle := ℕ → WordIntegerPacket

/-- Eager binary-data cache. Each provider request supplies its actual Word
packet value once; no intermediate rational or host-integer payload is built. -/
def buildNativePacketCache (provider : NativePacketDataOracle) (P : ℕ) : List.Vector WordIntegerPacket (P+1) :=
  List.Vector.ofFn (fun q => provider q.val)

def readNativePacketCache {P : ℕ} (cache : List.Vector WordIntegerPacket (P+1)) (q : ℕ) : WordIntegerPacket :=
  if h : q≤P then cache.get ⟨q,by omega⟩ else wordPacketOne

theorem readNativePacketCache_build (provider : NativePacketDataOracle) (P q : ℕ) (h : q≤P) :
    readNativePacketCache (buildNativePacketCache provider P) q=provider q := by
  simp only [readNativePacketCache,dite_eq_left h,buildNativePacketCache,List.Vector.get_ofFn]

theorem readNativePacketCache_default {P : ℕ} (cache : List.Vector WordIntegerPacket (P+1)) (q : ℕ) (h : P<q) :
    readNativePacketCache cache q=wordPacketOne := by
  simp only [readNativePacketCache,dite_eq_right (by omega : ¬q≤P)]

def nativeCachedPacketOracle {P : ℕ} (cache : List.Vector WordIntegerPacket (P+1)) : NativePacketExpressionOracle :=
  fun q => .literal (readNativePacketCache cache q)

theorem nativeCachedPacketOracle_interpret {P : ℕ} (cache : List.Vector WordIntegerPacket (P+1)) :
    interpretNativePacketOracle (nativeCachedPacketOracle cache)=
      rawPacketExpressionOracle (fun q => (readNativePacketCache cache q).decode) := by rfl

theorem buildNativePacketCache_length (provider : NativePacketDataOracle) (P : ℕ) :
    (buildNativePacketCache provider P).toList.length=P+1 := (buildNativePacketCache provider P).2

end CircuitRecursion
