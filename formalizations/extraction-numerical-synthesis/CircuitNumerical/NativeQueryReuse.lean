import CircuitNumerical.NativeQuerySemantics

namespace CircuitRecursion.NativeQueryMachine

open Turing PacketFraming

/-- The three concrete Symbol work stacks. This is a proof-side volume,
not a computed length register or a charge substituted for an execution. -/
def symbolVolume (c : Configuration) : ℕ :=
  (c.stk (.inl inputStack)).length+(c.stk (.inl (.inl (.inl .right)))).length+
    (c.stk (.inl (.inl (.inl .work)))).length

theorem encodeCache_drop_length (ps : List WordIntegerPacket) (n : ℕ) :
    (encodeCache (ps.drop n)).length≤(encodeCache ps).length := by
  induction ps generalizing n with
  | nil => simp only [List.drop_nil,encodeCache,le_refl]
  | cons p ps ih =>
    cases n with
    | zero => exact le_rfl
    | succ n =>
      change (encodeCache (ps.drop n)).length≤(encodeCache (p::ps)).length
      have ht:=ih n
      simp only [encodeCache,List.length_append]
      omega

theorem terminal_symbolVolume (ps : List WordIntegerPacket) (i : BinaryIndex) (rest : List Symbol) (p : WordIntegerPacket) :
    symbolVolume (terminal ps i rest p)≤(encodeCache ps).length := by
  unfold symbolVolume
  rw [terminal_symbol_payload_consumed,terminal_symbol_scratch,terminal_cache_tail]
  simp only [List.length_nil,Nat.zero_add]
  exact encodeCache_drop_length ps (i.value+1)

/-- Data of the actual previous terminal, re-entered at the program's real
cleanup label. The next query was already retained in the actual input tail. -/
def reentry (ps : List WordIntegerPacket) (previous next : BinaryIndex) (rest : List Symbol)
    (previousPacket : WordIntegerPacket) : Configuration :=
  let old:=terminal ps previous (PacketQueryMachine.queryCode next.bits++rest) previousPacket
  initial ps next old.var (old.stk (.inl inputStack)) (old.stk (.inl (.inl (.inl .right))))
    (old.stk (.inl (.inl (.inl .work)))) rest (nativeWords old)

theorem reentry_memory (ps : List WordIntegerPacket) (previous next : BinaryIndex) (rest : List Symbol)
    (previousPacket : WordIntegerPacket) :
    (reentry ps previous next rest previousPacket).var=
      (terminal ps previous (PacketQueryMachine.queryCode next.bits++rest) previousPacket).var := rfl

theorem reentry_stacks (ps : List WordIntegerPacket) (previous next : BinaryIndex) (rest : List Symbol)
    (previousPacket : WordIntegerPacket) :
    (reentry ps previous next rest previousPacket).stk=
      (terminal ps previous (PacketQueryMachine.queryCode next.bits++rest) previousPacket).stk := by
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k with
      | inl k => cases k <;> rfl
      | inr k => cases k;exact (terminal_master ps previous _ previousPacket).symm
    | inr k => cases k;exact (terminal_queries ps previous _ previousPacket).symm
  | inr k => rfl

/-- A literal CPS return can select the cleanup entry. The equality proves
that the return preserves every bit, rather than using a free stack reset. -/
theorem returned_reentry {Δ : Type*} (embed : Label → Δ) (ret : Memory → Δ)
    (ps : List WordIntegerPacket) (previous next : BinaryIndex) (rest : List Symbol) (previousPacket : WordIntegerPacket)
    (hret : ret (terminal ps previous (PacketQueryMachine.queryCode next.bits++rest) previousPacket).var=
      embed (.inl .scratch)) :
    TM2Subroutine.liftConfiguration embed ret (terminal ps previous (PacketQueryMachine.queryCode next.bits++rest) previousPacket)=
      TM2Subroutine.liftConfiguration embed ret (reentry ps previous next rest previousPacket) := by
  have hl : (terminal ps previous (PacketQueryMachine.queryCode next.bits++rest) previousPacket).l=none := rfl
  unfold TM2Subroutine.liftConfiguration
  rw [hl,hret]
  change TM2.Cfg.mk (some (embed (.inl .scratch))) _ _=TM2.Cfg.mk (some (embed (.inl .scratch))) _ _
  rw [reentry_memory,reentry_stacks]

/-- Fully charged reusable query from the preceding real native terminal.
The uniform input packet-height invariant internally bounds both prior Bool
cleanup and the prior Symbol suffix, as well as the next frame extraction. -/
def reuseRun (ps : List WordIntegerPacket) (previous next : BinaryIndex) (rest : List Symbol)
    (previousPacket nextPacket : WordIntegerPacket) (hp : ps[next.value]?=some nextPacket)
    (B : ℕ) (h : ∀ p∈ps,IntegerPacketHeight p.decode B) (hprevious : ps[previous.value]?=some previousPacket) :
    StateTransition.EvalsToInTime (TM2.step program) (reentry ps previous next rest previousPacket)
      (some (terminal ps next rest nextPacket))
      (2*next.bits.length+(2*next.bits.length+25*B+73)*ps.length+15*B+45) :=
  let old:=terminal ps previous (PacketQueryMachine.queryCode next.bits++rest) previousPacket
  let run:=nativeQueryRun ps next old.var (old.stk (.inl inputStack)) (old.stk (.inl (.inl (.inl .right))))
    (old.stk (.inl (.inl (.inl .work)))) rest (nativeWords old) nextPacket hp
  ⟨run.toEvalsTo,by
    have ht:=nativeQueryRun_steps_height ps next old.var (old.stk (.inl inputStack))
      (old.stk (.inl (.inl (.inl .right)))) (old.stk (.inl (.inl (.inl .work)))) rest (nativeWords old) nextPacket hp B h
    have hv:=terminal_wordVolume_height ps previous (PacketQueryMachine.queryCode next.bits++rest) previousPacket B
      (h previousPacket (addressed_mem ps previous.value previousPacket hprevious))
    have hs:=terminal_symbolVolume ps previous (PacketQueryMachine.queryCode next.bits++rest) previousPacket
    have hc:=encodeCache_length_height ps B h
    change symbolVolume old≤_ at hs
    unfold symbolVolume at hs
    change run.steps≤_
    nlinarith⟩

instance alphabetFintype (k : Stack) : Fintype (Alphabet k) := by
  cases k <;> infer_instance

theorem alphabet_card_bound (k : Stack) : Fintype.card (Alphabet k)≤4 := by
  cases k <;> simp only [Alphabet,Fintype.card_bool,symbol_card] <;> decide

end CircuitRecursion.NativeQueryMachine
