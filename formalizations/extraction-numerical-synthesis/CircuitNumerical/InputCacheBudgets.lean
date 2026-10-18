import CircuitNumerical.InputCacheEvaluation

namespace CircuitRecursion

set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def nativeCacheReadActions {m : ℕ} (reads : List (NativeCacheInputRead m)) : ℕ :=
  (reads.map NativeCacheInputRead.actions).sum

mutual
theorem InputScalarExpression.inputRun_readCount {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (e : InputScalarExpression m) : (e.inputRun cache).reads.length≤(e.inputRun cache).numerical.trace.nodes := by
  cases e with
  | literal a =>
    change (0:ℕ)≤_
    exact Nat.zero_le _
  | stoppingThreshold t =>
    change (0:ℕ)≤_
    exact Nat.zero_le _
  | add a b =>
    have ha:=InputScalarExpression.inputRun_readCount cache a
    have hb:=InputScalarExpression.inputRun_readCount cache b
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,List.length_append]
    omega
  | mul a b =>
    have ha:=InputScalarExpression.inputRun_readCount cache a
    have hb:=InputScalarExpression.inputRun_readCount cache b
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,List.length_append]
    omega
  | distance a b =>
    have ha:=InputPacketExpression.inputRun_readCount cache a
    have hb:=InputPacketExpression.inputRun_readCount cache b
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,List.length_append]
    omega
  | neg a =>
    have ha:=InputScalarExpression.inputRun_readCount cache a
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,List.length_append]
    omega
  | inv a =>
    have ha:=InputScalarExpression.inputRun_readCount cache a
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,List.length_append]
    omega
  | sqrt a p =>
    have ha:=InputScalarExpression.inputRun_readCount cache a
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,List.length_append]
    omega
  | meanMinus a =>
    have ha:=InputScalarExpression.inputRun_readCount cache a
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,List.length_append]
    omega
  | coordinate a i =>
    have ha:=InputPacketExpression.inputRun_readCount cache a
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,List.length_append]
    omega
theorem InputPacketExpression.inputRun_readCount {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (e : InputPacketExpression m) : (e.inputRun cache).reads.length≤(e.inputRun cache).numerical.trace.nodes := by
  cases e with
  | literal a =>
    change (0:ℕ)≤_
    exact Nat.zero_le _
  | input label q =>
    change (1:ℕ)≤1
    decide
  | tuple a =>
    have h0:=InputScalarExpression.inputRun_readCount cache (a 0)
    have h1:=InputScalarExpression.inputRun_readCount cache (a 1)
    have h2:=InputScalarExpression.inputRun_readCount cache (a 2)
    have h3:=InputScalarExpression.inputRun_readCount cache (a 3)
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,List.length_append]
    omega
  | mul a b =>
    have ha:=InputPacketExpression.inputRun_readCount cache a
    have hb:=InputPacketExpression.inputRun_readCount cache b
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,List.length_append]
    omega
  | inverse a =>
    have ha:=InputPacketExpression.inputRun_readCount cache a
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,List.length_append]
    omega
  | selectMax scores branches =>
    let stored:=List.Vector.ofFn (fun i => (scores i).inputRun cache)
    let selection:=wordMaximumProgram 3 (stored.map (fun x => x.numerical.value))
    have h0:=InputScalarExpression.inputRun_readCount cache (scores 0)
    have h1:=InputScalarExpression.inputRun_readCount cache (scores 1)
    have h2:=InputScalarExpression.inputRun_readCount cache (scores 2)
    have h3:=InputScalarExpression.inputRun_readCount cache (scores 3)
    have hsel:=InputPacketExpression.inputRun_readCount cache (branches selection.index)
    dsimp only [stored,selection] at hsel
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,List.length_append]
    omega
end

mutual
theorem InputScalarExpression.inputRun_readActions {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (e : InputScalarExpression m) : nativeCacheReadActions (e.inputRun cache).reads≤4*(m+P+5)*(e.inputRun cache).numerical.trace.nodes := by
  cases e with
  | literal a =>
    change (0:ℕ)≤_
    exact Nat.zero_le _
  | stoppingThreshold t =>
    change (0:ℕ)≤_
    exact Nat.zero_le _
  | add a b =>
    have ha:=InputScalarExpression.inputRun_readActions cache a
    have hb:=InputScalarExpression.inputRun_readActions cache b
    simp only [nativeCacheReadActions,Nat.mul_add,Nat.mul_one] at *
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,nativeCacheReadActions,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_add,Nat.mul_one]
    omega
  | mul a b =>
    have ha:=InputScalarExpression.inputRun_readActions cache a
    have hb:=InputScalarExpression.inputRun_readActions cache b
    simp only [nativeCacheReadActions,Nat.mul_add,Nat.mul_one] at *
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,nativeCacheReadActions,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_add,Nat.mul_one]
    omega
  | distance a b =>
    have ha:=InputPacketExpression.inputRun_readActions cache a
    have hb:=InputPacketExpression.inputRun_readActions cache b
    simp only [nativeCacheReadActions,Nat.mul_add,Nat.mul_one] at *
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,nativeCacheReadActions,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_add,Nat.mul_one]
    omega
  | neg a =>
    have ha:=InputScalarExpression.inputRun_readActions cache a
    simp only [nativeCacheReadActions,Nat.mul_add,Nat.mul_one] at *
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,nativeCacheReadActions,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_add,Nat.mul_one]
    omega
  | inv a =>
    have ha:=InputScalarExpression.inputRun_readActions cache a
    simp only [nativeCacheReadActions,Nat.mul_add,Nat.mul_one] at *
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,nativeCacheReadActions,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_add,Nat.mul_one]
    omega
  | sqrt a p =>
    have ha:=InputScalarExpression.inputRun_readActions cache a
    simp only [nativeCacheReadActions,Nat.mul_add,Nat.mul_one] at *
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,nativeCacheReadActions,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_add,Nat.mul_one]
    omega
  | meanMinus a =>
    have ha:=InputScalarExpression.inputRun_readActions cache a
    simp only [nativeCacheReadActions,Nat.mul_add,Nat.mul_one] at *
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,nativeCacheReadActions,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_add,Nat.mul_one]
    omega
  | coordinate a i =>
    have ha:=InputPacketExpression.inputRun_readActions cache a
    simp only [nativeCacheReadActions,Nat.mul_add,Nat.mul_one] at *
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,nativeCacheReadActions,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_add,Nat.mul_one]
    omega
theorem InputPacketExpression.inputRun_readActions {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (e : InputPacketExpression m) : nativeCacheReadActions (e.inputRun cache).reads≤4*(m+P+5)*(e.inputRun cache).numerical.trace.nodes := by
  cases e with
  | literal a =>
    change (0:ℕ)≤_
    exact Nat.zero_le _
  | input label q =>
    simpa only [InputPacketExpression.inputRun,nativeCacheReadActions,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,NativePacketExpression.wordRun,WordExpressionTrace.nodes,Nat.mul_one] using
      nativeCacheInputRead_actions cache label q
  | tuple a =>
    have h0:=InputScalarExpression.inputRun_readActions cache (a 0)
    have h1:=InputScalarExpression.inputRun_readActions cache (a 1)
    have h2:=InputScalarExpression.inputRun_readActions cache (a 2)
    have h3:=InputScalarExpression.inputRun_readActions cache (a 3)
    simp only [nativeCacheReadActions,Nat.mul_add,Nat.mul_one] at *
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,nativeCacheReadActions,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_add,Nat.mul_one]
    omega
  | mul a b =>
    have ha:=InputPacketExpression.inputRun_readActions cache a
    have hb:=InputPacketExpression.inputRun_readActions cache b
    simp only [nativeCacheReadActions,Nat.mul_add,Nat.mul_one] at *
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,nativeCacheReadActions,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_add,Nat.mul_one]
    omega
  | inverse a =>
    have ha:=InputPacketExpression.inputRun_readActions cache a
    simp only [nativeCacheReadActions,Nat.mul_add,Nat.mul_one] at *
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,nativeCacheReadActions,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_add,Nat.mul_one]
    omega
  | selectMax scores branches =>
    let stored:=List.Vector.ofFn (fun i => (scores i).inputRun cache)
    let selection:=wordMaximumProgram 3 (stored.map (fun x => x.numerical.value))
    have h0:=InputScalarExpression.inputRun_readActions cache (scores 0)
    have h1:=InputScalarExpression.inputRun_readActions cache (scores 1)
    have h2:=InputScalarExpression.inputRun_readActions cache (scores 2)
    have h3:=InputScalarExpression.inputRun_readActions cache (scores 3)
    have hsel:=InputPacketExpression.inputRun_readActions cache (branches selection.index)
    dsimp only [stored,selection] at hsel
    simp only [nativeCacheReadActions,Nat.mul_add,Nat.mul_one] at *
    simp only [InputScalarExpression.inputRun,InputPacketExpression.inputRun,inputFourReads,List.Vector.get_ofFn,WordExpressionTrace.nodes,nativeCacheReadActions,List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,Nat.mul_add,Nat.mul_one]
    omega
end

theorem InputScalarExpression.inputRun_reads_operations {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (e : InputScalarExpression m) : (e.inputRun cache).reads.length≤(e.resolve cache).interpret.operations := by
  have h:=InputScalarExpression.inputRun_readCount cache e
  rw [InputScalarExpression.inputRun_numerical] at h
  exact h.trans (NativeScalarExpression.wordRun_nodes _)

theorem InputScalarExpression.inputRun_readActions_operations {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (e : InputScalarExpression m) : nativeCacheReadActions (e.inputRun cache).reads≤
      4*(m+P+5)*(e.resolve cache).interpret.operations := by
  have h:=InputScalarExpression.inputRun_readActions cache e
  rw [InputScalarExpression.inputRun_numerical] at h
  exact h.trans (Nat.mul_le_mul_left _ (NativeScalarExpression.wordRun_nodes _))

theorem InputPacketExpression.inputRun_reads_operations {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (e : InputPacketExpression m) : (e.inputRun cache).reads.length≤(e.resolve cache).interpret.operations := by
  have h:=InputPacketExpression.inputRun_readCount cache e
  rw [InputPacketExpression.inputRun_numerical] at h
  exact h.trans (NativePacketExpression.wordRun_nodes _)

theorem InputPacketExpression.inputRun_readActions_operations {m P : ℕ} (cache : NativeCacheEnvironment m P)
    (e : InputPacketExpression m) : nativeCacheReadActions (e.inputRun cache).reads≤
      4*(m+P+5)*(e.resolve cache).interpret.operations := by
  have h:=InputPacketExpression.inputRun_readActions cache e
  rw [InputPacketExpression.inputRun_numerical] at h
  exact h.trans (Nat.mul_le_mul_left _ (NativePacketExpression.wordRun_nodes _))

end CircuitRecursion
