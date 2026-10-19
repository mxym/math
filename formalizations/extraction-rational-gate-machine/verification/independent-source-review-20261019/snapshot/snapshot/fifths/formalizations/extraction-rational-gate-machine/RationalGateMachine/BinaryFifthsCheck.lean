import RationalGateMachine.BinaryFifths
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for name in [``RationalGateMachine.StateLift.stepAux,``RationalGateMachine.StateLift.step,``RationalGateMachine.StateLift.iterate,``RationalGateMachine.StateLift.run_steps,``RationalGateMachine.StateLift.statement_depth,``RationalGateMachine.BinaryFifths.clockCall_steps,``RationalGateMachine.BinaryFifths.clockCall_iterate,``RationalGateMachine.BinaryFifths.step_init,``RationalGateMachine.BinaryFifths.step_empty,``RationalGateMachine.BinaryFifths.step_cons,``RationalGateMachine.BinaryFifths.generation_steps,``RationalGateMachine.BinaryFifths.unary_generation_steps,``RationalGateMachine.BinaryFifths.binary_generation_steps,``RationalGateMachine.BinaryFifths.binaryFifthsRun_steps,``RationalGateMachine.BinaryFifths.binaryFifthsRun_steps_logarithmic,``RationalGateMachine.BinaryFifths.terminal_halts,``RationalGateMachine.BinaryFifths.binaryFifths_mem_eval,``RationalGateMachine.BinaryFifths.terminal_numerator,``RationalGateMachine.BinaryFifths.terminal_denominator,``RationalGateMachine.BinaryFifths.terminal_clock_empty,``RationalGateMachine.BinaryFifths.terminal_dyadic_error,``RationalGateMachine.BinaryFifths.program_supports,``RationalGateMachine.BinaryFifths.finite_running_control_card,``RationalGateMachine.BinaryFifths.label_card,``RationalGateMachine.BinaryFifths.stack_card,``RationalGateMachine.BinaryFifths.statement_depth] do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Unexpected declaration kind {name}"
  for name in [``RationalGateMachine.StateLift.compile,``RationalGateMachine.StateLift.configuration,``RationalGateMachine.StateLift.run,``RationalGateMachine.BinaryFifths.configuration,``RationalGateMachine.BinaryFifths.clockProgram,``RationalGateMachine.BinaryFifths.outer,``RationalGateMachine.BinaryFifths.program,``RationalGateMachine.BinaryFifths.advance,``RationalGateMachine.BinaryFifths.terminal,``RationalGateMachine.BinaryFifths.clockCall,``RationalGateMachine.BinaryFifths.binaryFifthsRun] do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Unexpected declaration kind {name}"

#check RationalGateMachine.StateLift.stepAux
#print axioms RationalGateMachine.StateLift.stepAux

#check RationalGateMachine.StateLift.step
#print axioms RationalGateMachine.StateLift.step

#check RationalGateMachine.StateLift.iterate
#print axioms RationalGateMachine.StateLift.iterate

#check RationalGateMachine.StateLift.run_steps
#print axioms RationalGateMachine.StateLift.run_steps

#check RationalGateMachine.StateLift.statement_depth
#print axioms RationalGateMachine.StateLift.statement_depth

#check RationalGateMachine.BinaryFifths.clockCall_steps
#print axioms RationalGateMachine.BinaryFifths.clockCall_steps

#check RationalGateMachine.BinaryFifths.clockCall_iterate
#print axioms RationalGateMachine.BinaryFifths.clockCall_iterate

#check RationalGateMachine.BinaryFifths.step_init
#print axioms RationalGateMachine.BinaryFifths.step_init

#check RationalGateMachine.BinaryFifths.step_empty
#print axioms RationalGateMachine.BinaryFifths.step_empty

#check RationalGateMachine.BinaryFifths.step_cons
#print axioms RationalGateMachine.BinaryFifths.step_cons

#check RationalGateMachine.BinaryFifths.generation_steps
#print axioms RationalGateMachine.BinaryFifths.generation_steps

#check RationalGateMachine.BinaryFifths.unary_generation_steps
#print axioms RationalGateMachine.BinaryFifths.unary_generation_steps

#check RationalGateMachine.BinaryFifths.binary_generation_steps
#print axioms RationalGateMachine.BinaryFifths.binary_generation_steps

#check RationalGateMachine.BinaryFifths.binaryFifthsRun_steps
#print axioms RationalGateMachine.BinaryFifths.binaryFifthsRun_steps

#check RationalGateMachine.BinaryFifths.binaryFifthsRun_steps_logarithmic
#print axioms RationalGateMachine.BinaryFifths.binaryFifthsRun_steps_logarithmic

#check RationalGateMachine.BinaryFifths.terminal_halts
#print axioms RationalGateMachine.BinaryFifths.terminal_halts

#check RationalGateMachine.BinaryFifths.binaryFifths_mem_eval
#print axioms RationalGateMachine.BinaryFifths.binaryFifths_mem_eval

#check RationalGateMachine.BinaryFifths.terminal_numerator
#print axioms RationalGateMachine.BinaryFifths.terminal_numerator

#check RationalGateMachine.BinaryFifths.terminal_denominator
#print axioms RationalGateMachine.BinaryFifths.terminal_denominator

#check RationalGateMachine.BinaryFifths.terminal_clock_empty
#print axioms RationalGateMachine.BinaryFifths.terminal_clock_empty

#check RationalGateMachine.BinaryFifths.terminal_dyadic_error
#print axioms RationalGateMachine.BinaryFifths.terminal_dyadic_error

#check RationalGateMachine.BinaryFifths.program_supports
#print axioms RationalGateMachine.BinaryFifths.program_supports

#check RationalGateMachine.BinaryFifths.finite_running_control_card
#print axioms RationalGateMachine.BinaryFifths.finite_running_control_card

#check RationalGateMachine.BinaryFifths.label_card
#print axioms RationalGateMachine.BinaryFifths.label_card

#check RationalGateMachine.BinaryFifths.stack_card
#print axioms RationalGateMachine.BinaryFifths.stack_card

#check RationalGateMachine.BinaryFifths.statement_depth
#print axioms RationalGateMachine.BinaryFifths.statement_depth

#check RationalGateMachine.StateLift.compile
#print axioms RationalGateMachine.StateLift.compile

#check RationalGateMachine.StateLift.configuration
#print axioms RationalGateMachine.StateLift.configuration

#check RationalGateMachine.StateLift.run
#print axioms RationalGateMachine.StateLift.run

#check RationalGateMachine.BinaryFifths.configuration
#print axioms RationalGateMachine.BinaryFifths.configuration

#check RationalGateMachine.BinaryFifths.clockProgram
#print axioms RationalGateMachine.BinaryFifths.clockProgram

#check RationalGateMachine.BinaryFifths.outer
#print axioms RationalGateMachine.BinaryFifths.outer

#check RationalGateMachine.BinaryFifths.program
#print axioms RationalGateMachine.BinaryFifths.program

#check RationalGateMachine.BinaryFifths.advance
#print axioms RationalGateMachine.BinaryFifths.advance

#check RationalGateMachine.BinaryFifths.terminal
#print axioms RationalGateMachine.BinaryFifths.terminal

#check RationalGateMachine.BinaryFifths.clockCall
#print axioms RationalGateMachine.BinaryFifths.clockCall

#check RationalGateMachine.BinaryFifths.binaryFifthsRun
#print axioms RationalGateMachine.BinaryFifths.binaryFifthsRun

open Turing CircuitRecursion RationalGateProvider
#eval do
  -- Binary fixture construction and semantic Nat observations live only here.
  let initials : List Remainder := [.r0,.r1,.r2,.r3,.r4]
  for initial in initials do
    for q in List.range 33 do
      let raw := List.ofFn (fun j : Fin 6 => Nat.testBit q j.val)
      let i : BinaryIndex := ⟨(binaryTrimProgram raw).bits,binaryTrimProgram_canonical raw⟩
      unless i.value == q do throw (IO.userError "BINARY_FIFTHS_FIXTURE_FAILED")
      let time:=RationalGateMachine.BinaryClock.clockTime q i+q+2
      let result:=RationalGateMachine.BinaryFifths.advance^[time]
        (some (RationalGateMachine.BinaryFifths.configuration
          (some (.inl (.inr .loop))) initial none i.bits [] []))
      match result with
      | none => throw (IO.userError "BINARY_FIFTHS_UNEXPECTED_NONE")
      | some cfg =>
          unless cfg.l.isNone && cfg.var.2.isNone && cfg.stk .work == [] &&
              bitValue (cfg.stk .left) == initial.value*2^q/5 &&
              bitValue (cfg.stk .right) == 2^q && cfg.var.1.value == initial.value*2^q%5 &&
              cfg.stk .left == (RationalGateProvider.run initial q).bits &&
              cfg.stk .right == denominatorBits q &&
              time ≤ (2*Nat.clog 2 (q+1)+7)*q+3 &&
              (TM2.step RationalGateMachine.BinaryFifths.program cfg).isNone do
            throw (IO.userError "BINARY_FIFTHS_ACTUAL_MACHINE_FAILED")
  IO.println "FINITE_TM2_BINARY_FIFTHS_165_ACTUAL_RUNS_PASS"
