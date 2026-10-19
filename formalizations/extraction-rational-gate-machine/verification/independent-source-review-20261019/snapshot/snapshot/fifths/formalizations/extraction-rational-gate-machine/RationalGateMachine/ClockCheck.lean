import RationalGateMachine.BinaryClock
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for name in [``RationalGateMachine.BinaryClock.step_zero,``RationalGateMachine.BinaryClock.step_positive,``RationalGateMachine.BinaryClock.step_emit,``RationalGateMachine.BinaryClock.counter_iterate,``RationalGateMachine.BinaryClock.clock_time_bound,``RationalGateMachine.BinaryClock.clock_iterate,``RationalGateMachine.BinaryClock.clockRun_steps,``RationalGateMachine.BinaryClock.clockRun_steps_width,``RationalGateMachine.BinaryClock.input_width_logarithmic,``RationalGateMachine.BinaryClock.clockRun_steps_logarithmic,``RationalGateMachine.BinaryClock.terminal_halts,``RationalGateMachine.BinaryClock.clock_mem_eval,``RationalGateMachine.BinaryClock.program_supports,``RationalGateMachine.BinaryClock.finite_running_control_card,``RationalGateMachine.BinaryClock.outer_statement_depth] do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Unexpected declaration kind {name}"
  for name in [``RationalGateMachine.BinaryClock.configuration,``RationalGateMachine.BinaryClock.outer,``RationalGateMachine.BinaryClock.program,``RationalGateMachine.BinaryClock.liftedStep,``RationalGateMachine.BinaryClock.counterInvocation,``RationalGateMachine.BinaryClock.clockTime,``RationalGateMachine.BinaryClock.clockRun] do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Unexpected declaration kind {name}"

#check RationalGateMachine.BinaryClock.step_zero
#print axioms RationalGateMachine.BinaryClock.step_zero

#check RationalGateMachine.BinaryClock.step_positive
#print axioms RationalGateMachine.BinaryClock.step_positive

#check RationalGateMachine.BinaryClock.step_emit
#print axioms RationalGateMachine.BinaryClock.step_emit

#check RationalGateMachine.BinaryClock.counter_iterate
#print axioms RationalGateMachine.BinaryClock.counter_iterate

#check RationalGateMachine.BinaryClock.clock_time_bound
#print axioms RationalGateMachine.BinaryClock.clock_time_bound

#check RationalGateMachine.BinaryClock.clock_iterate
#print axioms RationalGateMachine.BinaryClock.clock_iterate

#check RationalGateMachine.BinaryClock.clockRun_steps
#print axioms RationalGateMachine.BinaryClock.clockRun_steps

#check RationalGateMachine.BinaryClock.clockRun_steps_width
#print axioms RationalGateMachine.BinaryClock.clockRun_steps_width

#check RationalGateMachine.BinaryClock.input_width_logarithmic
#print axioms RationalGateMachine.BinaryClock.input_width_logarithmic

#check RationalGateMachine.BinaryClock.clockRun_steps_logarithmic
#print axioms RationalGateMachine.BinaryClock.clockRun_steps_logarithmic

#check RationalGateMachine.BinaryClock.terminal_halts
#print axioms RationalGateMachine.BinaryClock.terminal_halts

#check RationalGateMachine.BinaryClock.clock_mem_eval
#print axioms RationalGateMachine.BinaryClock.clock_mem_eval

#check RationalGateMachine.BinaryClock.program_supports
#print axioms RationalGateMachine.BinaryClock.program_supports

#check RationalGateMachine.BinaryClock.finite_running_control_card
#print axioms RationalGateMachine.BinaryClock.finite_running_control_card

#check RationalGateMachine.BinaryClock.outer_statement_depth
#print axioms RationalGateMachine.BinaryClock.outer_statement_depth

#check RationalGateMachine.BinaryClock.configuration
#print axioms RationalGateMachine.BinaryClock.configuration

#check RationalGateMachine.BinaryClock.outer
#print axioms RationalGateMachine.BinaryClock.outer

#check RationalGateMachine.BinaryClock.program
#print axioms RationalGateMachine.BinaryClock.program

#check RationalGateMachine.BinaryClock.liftedStep
#print axioms RationalGateMachine.BinaryClock.liftedStep

#check RationalGateMachine.BinaryClock.counterInvocation
#print axioms RationalGateMachine.BinaryClock.counterInvocation

#check RationalGateMachine.BinaryClock.clockTime
#print axioms RationalGateMachine.BinaryClock.clockTime

#check RationalGateMachine.BinaryClock.clockRun
#print axioms RationalGateMachine.BinaryClock.clockRun

open Turing CircuitRecursion
#eval do
  -- Nat/testBit occur only in this finite fixture generator, never the
  -- machine program. All assertions run official TM2.step transitions.
  let tails : List (List Bool) := [[],[true],[false,true]]
  for q in List.range 65 do
    let raw := List.ofFn (fun j : Fin 7 => Nat.testBit q j.val)
    let i : BinaryIndex := ⟨(binaryTrimProgram raw).bits,binaryTrimProgram_canonical raw⟩
    unless i.value == q do
      throw (IO.userError "BINARY_CLOCK_FIXTURE_INPUT_FAILED")
    for tail in tails do
      let time := RationalGateMachine.BinaryClock.clockTime q i
      let result := RationalGateMachine.BinaryClock.liftedStep^[time]
        (some (RationalGateMachine.BinaryClock.configuration (some (.inr .loop)) none i.bits [] tail))
      match result with
      | none => throw (IO.userError "BINARY_CLOCK_UNEXPECTED_NONE")
      | some cfg =>
          unless cfg.l.isNone && cfg.var.isNone && cfg.stk .left == [] &&
              cfg.stk .right == [] && cfg.stk .work == List.replicate q false ++ tail &&
              time ≤ (2*Nat.clog 2 (q+1)+6)*q+1 &&
              (TM2.step RationalGateMachine.BinaryClock.program cfg).isNone do
            throw (IO.userError "BINARY_CLOCK_ACTUAL_MACHINE_CHECK_FAILED")
  IO.println "FINITE_TM2_BINARY_CLOCK_195_ACTUAL_RUNS_PASS"
