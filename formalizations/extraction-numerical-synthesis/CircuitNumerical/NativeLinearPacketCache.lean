import CircuitNumerical.NativeListLookup

namespace CircuitRecursion

theorem nativeListLookup_vector_get {α : Type*} {n : ℕ} (values : List.Vector α n) (i : Fin n) :
    (nativeListLookup values.toList i.val).value=some (values.get i) := by
  rcases values with ⟨as,h⟩
  subst n
  exact nativeListLookup_get as i

structure NativePacketReadResult where
  packet : WordIntegerPacket
  trace : NativeListLookupTrace

/-- The cache miss is discovered by traversing the list spine. This value
program does not invoke Vector.get or compare q with the precision bound. -/
def nativeLinearReadPacketCache {P : ℕ} (cache : List.Vector WordIntegerPacket (P+1)) (q : ℕ) :
    NativePacketReadResult :=
  let lookup:=nativeListLookup cache.toList q
  ⟨lookup.value.getD wordPacketOne,lookup.trace⟩

theorem nativeLinearReadPacketCache_packet {P : ℕ} (cache : List.Vector WordIntegerPacket (P+1)) (q : ℕ) :
    (nativeLinearReadPacketCache cache q).packet=readNativePacketCache cache q := by
  by_cases hq : q≤P
  · have hi : q<P+1 := by omega
    have hlookup:=nativeListLookup_vector_get cache ⟨q,hi⟩
    simp only [nativeLinearReadPacketCache,hlookup,Option.getD_some,readNativePacketCache,dite_eq_left hq]
  · have hlen : cache.toList.length=P+1 := cache.2
    have hnone : (nativeListLookup cache.toList q).value=none := by
      rw [nativeListLookup_value,List.getElem?_eq_none (by omega)]
    simp only [nativeLinearReadPacketCache,hnone,Option.getD_none,readNativePacketCache,dite_eq_right hq]

def NativePacketReadResult.actions (read : NativePacketReadResult) : ℕ := read.trace.actions+4

theorem nativeLinearReadPacketCache_actions {P : ℕ} (cache : List.Vector WordIntegerPacket (P+1)) (q : ℕ) :
    (nativeLinearReadPacketCache cache q).actions≤4*(P+3) := by
  have h:=nativeListLookup_actions_length cache.toList q
  have hlen : cache.toList.length=P+1 := cache.2
  change (nativeListLookup cache.toList q).trace.actions+4≤_
  rw [hlen] at h
  omega

structure NativeGatePacketReadResult where
  packet : WordIntegerPacket
  gateTrace : NativeListLookupTrace
  precisionTrace : NativeListLookupTrace

/-- Both the gate-label lookup and precision lookup are actual retained
list-spine programs. The supplied fallback cache is a stored value; a valid
gate label always selects an existing gate cache. -/
def nativeLinearReadGatePacket {m P : ℕ} (caches : List.Vector (List.Vector WordIntegerPacket (P+1)) m)
    (fallback : List.Vector WordIntegerPacket (P+1)) (i : Fin m) (q : ℕ) : NativeGatePacketReadResult :=
  let gate:=nativeListLookup caches.toList i.val
  let precision:=nativeLinearReadPacketCache (gate.value.getD fallback) q
  ⟨precision.packet,gate.trace,precision.trace⟩

theorem nativeLinearReadGatePacket_packet {m P : ℕ} (caches : List.Vector (List.Vector WordIntegerPacket (P+1)) m)
    (fallback : List.Vector WordIntegerPacket (P+1)) (i : Fin m) (q : ℕ) :
    (nativeLinearReadGatePacket caches fallback i q).packet=readNativePacketCache (caches.get i) q := by
  simp only [nativeLinearReadGatePacket,nativeListLookup_vector_get,Option.getD_some,nativeLinearReadPacketCache_packet]

def NativeGatePacketReadResult.actions (read : NativeGatePacketReadResult) : ℕ :=
  read.gateTrace.actions+read.precisionTrace.actions+8

theorem nativeLinearReadGatePacket_actions {m P : ℕ} (caches : List.Vector (List.Vector WordIntegerPacket (P+1)) m)
    (fallback : List.Vector WordIntegerPacket (P+1)) (i : Fin m) (q : ℕ) :
    (nativeLinearReadGatePacket caches fallback i q).actions≤4*(m+P+5) := by
  have hgate:=nativeListLookup_actions_length caches.toList i.val
  have hlen : caches.toList.length=m := caches.2
  let gate:=nativeListLookup caches.toList i.val
  have hprecision:=nativeListLookup_actions_length (gate.value.getD fallback).toList q
  have hplen : (gate.value.getD fallback).toList.length=P+1 := (gate.value.getD fallback).2
  rw [hlen] at hgate
  rw [hplen] at hprecision
  change gate.trace.actions+(nativeListLookup (gate.value.getD fallback).toList q).trace.actions+8≤_
  change gate.trace.actions≤_ at hgate
  omega

def nativeLinearCachedPacketOracle {P : ℕ} (cache : List.Vector WordIntegerPacket (P+1)) : NativePacketExpressionOracle :=
  fun q => .literal (nativeLinearReadPacketCache cache q).packet

theorem nativeLinearCachedPacketOracle_eq {P : ℕ} (cache : List.Vector WordIntegerPacket (P+1)) :
    nativeLinearCachedPacketOracle cache=nativeCachedPacketOracle cache := by
  funext q
  exact congrArg NativePacketExpression.literal (nativeLinearReadPacketCache_packet cache q)

def nativeLinearGatePacketOracle {m P : ℕ} (caches : List.Vector (List.Vector WordIntegerPacket (P+1)) m)
    (fallback : List.Vector WordIntegerPacket (P+1)) (i : Fin m) : NativePacketExpressionOracle :=
  fun q => .literal (nativeLinearReadGatePacket caches fallback i q).packet

theorem nativeLinearGatePacketOracle_eq {m P : ℕ} (caches : List.Vector (List.Vector WordIntegerPacket (P+1)) m)
    (fallback : List.Vector WordIntegerPacket (P+1)) (i : Fin m) :
    nativeLinearGatePacketOracle caches fallback i=nativeCachedPacketOracle (caches.get i) := by
  funext q
  exact congrArg NativePacketExpression.literal (nativeLinearReadGatePacket_packet caches fallback i q)

end CircuitRecursion
