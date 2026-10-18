import CircuitNumerical.NativeLinearCachedSynthesis

namespace CircuitRecursion

inductive NativeCacheLabel (m : ℕ) where
  | target
  | gate : Fin m → NativeCacheLabel m

structure NativeCacheEnvironment (m P : ℕ) where
  gates : List.Vector (List.Vector WordIntegerPacket (P+1)) m
  target : List.Vector WordIntegerPacket (P+1)

inductive NativeCacheInputRead (m : ℕ) where
  | target : ℕ → NativePacketReadResult → NativeCacheInputRead m
  | gate : Fin m → ℕ → NativeGatePacketReadResult → NativeCacheInputRead m

def NativeCacheInputRead.packet {m : ℕ} : NativeCacheInputRead m → WordIntegerPacket
  | .target _ read => read.packet
  | .gate _ _ read => read.packet

def NativeCacheInputRead.actions {m : ℕ} : NativeCacheInputRead m → ℕ
  | .target _ read => read.actions
  | .gate _ _ read => read.actions

/-- This is an actual cache query program, returning its packet together
with the executed list-spine trace. No host indexed cache access is used. -/
def nativeCacheInputRead {m P : ℕ} (cache : NativeCacheEnvironment m P) : NativeCacheLabel m → ℕ → NativeCacheInputRead m
  | .target,q => .target q (nativeLinearReadPacketCache cache.target q)
  | .gate i,q => .gate i q (nativeLinearReadGatePacket cache.gates cache.target i q)

theorem nativeCacheInputRead_actions {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (label : NativeCacheLabel m) (q : ℕ) :
    (nativeCacheInputRead cache label q).actions≤4*(m+P+5) := by
  cases label with
  | target =>
    have h:=nativeLinearReadPacketCache_actions cache.target q
    change (nativeLinearReadPacketCache cache.target q).actions≤_
    omega
  | gate i => exact nativeLinearReadGatePacket_actions cache.gates cache.target i q

/- The input-reference AST delays cache reads until the actual evaluator
visits that leaf. Other literals are already supplied binary data. -/
mutual
inductive InputScalarExpression (m : ℕ) where
  | literal : WordIntegerScalar → InputScalarExpression m
  | stoppingThreshold : ℕ → InputScalarExpression m
  | add : InputScalarExpression m → InputScalarExpression m → InputScalarExpression m
  | neg : InputScalarExpression m → InputScalarExpression m
  | mul : InputScalarExpression m → InputScalarExpression m → InputScalarExpression m
  | inv : InputScalarExpression m → InputScalarExpression m
  | sqrt : InputScalarExpression m → ℕ → InputScalarExpression m
  | meanMinus : InputScalarExpression m → InputScalarExpression m
  | coordinate : InputPacketExpression m → Fin 4 → InputScalarExpression m
  | distance : InputPacketExpression m → InputPacketExpression m → InputScalarExpression m
inductive InputPacketExpression (m : ℕ) where
  | literal : WordIntegerPacket → InputPacketExpression m
  | input : NativeCacheLabel m → ℕ → InputPacketExpression m
  | tuple : (Fin 4 → InputScalarExpression m) → InputPacketExpression m
  | mul : InputPacketExpression m → InputPacketExpression m → InputPacketExpression m
  | inverse : InputPacketExpression m → InputPacketExpression m
  | selectMax : (Fin 4 → InputScalarExpression m) → (Fin 4 → InputPacketExpression m) → InputPacketExpression m
end

/- Resolution is proof semantics. The evaluator below performs the concrete
read at each visited input leaf and retains that one read record instead. -/
mutual
def InputScalarExpression.resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) :
    InputScalarExpression m → NativeScalarExpression
  | .literal a => .literal a
  | .stoppingThreshold t => .stoppingThreshold t
  | .add a b => .add (a.resolve cache) (b.resolve cache)
  | .neg a => .neg (a.resolve cache)
  | .mul a b => .mul (a.resolve cache) (b.resolve cache)
  | .inv a => .inv (a.resolve cache)
  | .sqrt a p => .sqrt (a.resolve cache) p
  | .meanMinus a => .meanMinus (a.resolve cache)
  | .coordinate a i => .coordinate (a.resolve cache) i
  | .distance a b => .distance (a.resolve cache) (b.resolve cache)
def InputPacketExpression.resolve {m P : ℕ} (cache : NativeCacheEnvironment m P) :
    InputPacketExpression m → NativePacketExpression
  | .literal a => .literal a
  | .input label q => .literal (nativeCacheInputRead cache label q).packet
  | .tuple a => .tuple (fun i => (a i).resolve cache)
  | .mul a b => .mul (a.resolve cache) (b.resolve cache)
  | .inverse a => .inverse (a.resolve cache)
  | .selectMax scores branches => .selectMax (fun i => (scores i).resolve cache) (fun i => (branches i).resolve cache)
end

end CircuitRecursion
