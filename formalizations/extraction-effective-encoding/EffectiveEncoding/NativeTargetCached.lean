import EffectiveEncoding.NativeTargetPackets
import CircuitNumerical.NativeCachedSynthesis

open CircuitCompletion CircuitRecursion Matrix
namespace EffectiveEncoding


theorem nativePreparedTargetOracle_eq (u : SingleCode) :
    nativePacketDataOracle (prepareNativeSingleInput u).packetDataOracle=u.quaternionOracle := by
  funext p
  change ((prepareNativeSingleInput u).packetProgram p).value.decode.value=_
  rw [prepareNativeSingleInput_packet_decode,SingleCode.rawPacket_value]

structure NativeTargetResult (m L q : ℕ) where
  prepared : NativeSingleInput
  cached : NativeCachedWordResult m (numericalDemand L (Nat.clog 2 (q+1)))

/-- Prepare each descriptor's dynamic Boolean literals once, then execute the
actual native Word-valued provider/cache/numerical recursion. No interpretation,
Rat construction, host IntegerPacket payload, or Nat.bits adapter is called. -/
def nativeTargetDescriptorRun {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (u : SingleCode) : NativeTargetResult m L q :=
  let prepared:=prepareNativeSingleInput u
  let compiled:=nativeCachedRun entry inverseLabel table L q prepared.packetDataOracle
  ⟨prepared,compiled⟩


theorem nativeTargetDescriptorRun_word {m n : ℕ} (entry : Fin m → NativePacketDataOracle)
    (inverseLabel : Fin m → Fin m) (table : Fin (n+1) → List (Fin m))
    (L q : ℕ) (hL : ∀ j,(table j).length≤L) (u : SingleCode) :
    (nativeTargetDescriptorRun entry inverseLabel table L q u).cached.program.word=
      descriptorSynthesis (fun i => nativePacketDataOracle (entry i)) inverseLabel table L q u := by
  simp only [nativeTargetDescriptorRun,nativeCachedRun_word entry inverseLabel table L q hL,
    nativePreparedTargetOracle_eq]
  exact ((cachedArithmeticRun_word _ inverseLabel table L q u.quaternionOracle).trans
    (cachedNumericalRun_word _ inverseLabel table L q hL u.quaternionOracle)).symm


def actualNativeTargetHeightCoefficient (k L : ℕ) : ℕ :=
  1000000*(k+3)^7*(51200000*(L+1)+5)

/-- This hypothesis-free actual-target height bound supplies the generic native
compiler's finite queried input envelope; no final runtime certificate occurs. -/
theorem nativePreparedTarget_cache_height {k : ℕ} {wire : Fin (originalWireCount k)}
    {u : SingleCode} (hu : GateCode.single wire u∈(preparedNativeDescriptorRun k).word)
    (L q r : ℕ) (hr : r≤numericalDemand L (Nat.clog 2 (q+1))) :
    IntegerPacketHeight ((prepareNativeSingleInput u).packetDataOracle r).decode
      (actualNativeTargetHeightCoefficient k L*(q+1)^9) := by
  apply IntegerPacketHeight.mono _ _ _ (prepareNativeSingleInput_packet_height hu r)
  have hp : 1≤(q+1)^9 := Nat.one_le_pow _ _ (by omega)
  have hr' : r≤51200000*(L+1)*(q+1)^9 := hr.trans (numericalDemand_precision_bound L q)
  have hm : r+5≤(51200000*(L+1)+5)*(q+1)^9 := by nlinarith
  have h:=Nat.mul_le_mul_left (1000000*(k+3)^7) hm
  simpa only [actualNativeTargetHeightCoefficient,Nat.mul_assoc] using h

end EffectiveEncoding
