import RationalGateMachine.Fifths
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for name in [``RationalGateMachine.stackData_zero,
    ``RationalGateMachine.stackData_one,
    ``RationalGateMachine.stackData_two,
    ``RationalGateMachine.update_zero,
    ``RationalGateMachine.update_one,
    ``RationalGateMachine.update_two,
    ``RationalGateMachine.step_empty,
    ``RationalGateMachine.step_cons,
    ``RationalGateMachine.terminal_stops,
    ``RationalGateMachine.program_supports,
    ``RationalGateMachine.program_statement_depth,
    ``RationalGateMachine.advance_iterate,
    ``RationalGateMachine.iterate_seed,
    ``RationalGateMachine.advance_seed,
    ``RationalGateMachine.machine_steps,
    ``RationalGateMachine.finite_state_card,
    ``RationalGateMachine.stack_card,
    ``RationalGateMachine.label_card,
    ``RationalGateMachine.fifthsRun_steps,
    ``RationalGateMachine.fifths_terminal_numerator,
    ``RationalGateMachine.fifths_terminal_denominator,
    ``RationalGateMachine.fifths_terminal_dyadic_error,
    ``RationalGateMachine.fifths_terminal_mem_eval] do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Unexpected declaration kind {name}"
  for name in [``RationalGateMachine.program,
    ``RationalGateMachine.stackData,
    ``RationalGateMachine.active,
    ``RationalGateMachine.terminal,
    ``RationalGateMachine.advance,
    ``RationalGateMachine.fifthsRun] do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Unexpected declaration kind {name}"

#check RationalGateMachine.stackData_zero
#print axioms RationalGateMachine.stackData_zero

#check RationalGateMachine.stackData_one
#print axioms RationalGateMachine.stackData_one

#check RationalGateMachine.stackData_two
#print axioms RationalGateMachine.stackData_two

#check RationalGateMachine.update_zero
#print axioms RationalGateMachine.update_zero

#check RationalGateMachine.update_one
#print axioms RationalGateMachine.update_one

#check RationalGateMachine.update_two
#print axioms RationalGateMachine.update_two

#check RationalGateMachine.step_empty
#print axioms RationalGateMachine.step_empty

#check RationalGateMachine.step_cons
#print axioms RationalGateMachine.step_cons

#check RationalGateMachine.terminal_stops
#print axioms RationalGateMachine.terminal_stops

#check RationalGateMachine.program_supports
#print axioms RationalGateMachine.program_supports

#check RationalGateMachine.program_statement_depth
#print axioms RationalGateMachine.program_statement_depth

#check RationalGateMachine.advance_iterate
#print axioms RationalGateMachine.advance_iterate

#check RationalGateMachine.iterate_seed
#print axioms RationalGateMachine.iterate_seed

#check RationalGateMachine.advance_seed
#print axioms RationalGateMachine.advance_seed

#check RationalGateMachine.machine_steps
#print axioms RationalGateMachine.machine_steps

#check RationalGateMachine.finite_state_card
#print axioms RationalGateMachine.finite_state_card

#check RationalGateMachine.stack_card
#print axioms RationalGateMachine.stack_card

#check RationalGateMachine.label_card
#print axioms RationalGateMachine.label_card

#check RationalGateMachine.fifthsRun_steps
#print axioms RationalGateMachine.fifthsRun_steps

#check RationalGateMachine.fifths_terminal_numerator
#print axioms RationalGateMachine.fifths_terminal_numerator

#check RationalGateMachine.fifths_terminal_denominator
#print axioms RationalGateMachine.fifths_terminal_denominator

#check RationalGateMachine.fifths_terminal_dyadic_error
#print axioms RationalGateMachine.fifths_terminal_dyadic_error

#check RationalGateMachine.fifths_terminal_mem_eval
#print axioms RationalGateMachine.fifths_terminal_mem_eval

#check RationalGateMachine.program
#print axioms RationalGateMachine.program

#check RationalGateMachine.stackData
#print axioms RationalGateMachine.stackData

#check RationalGateMachine.active
#print axioms RationalGateMachine.active

#check RationalGateMachine.terminal
#print axioms RationalGateMachine.terminal

#check RationalGateMachine.advance
#print axioms RationalGateMachine.advance

#check RationalGateMachine.fifthsRun
#print axioms RationalGateMachine.fifthsRun

open RationalGateMachine RationalGateProvider Turing
#eval do
  let initials : List Remainder := [.r0,.r1,.r2,.r3,.r4]
  for initial in initials do
    for p in List.range 17 do
      let result := (fun c : Option Configuration => c.bind (TM2.step program))^[p+1]
        (some (active (List.replicate p false) [] [true] initial))
      match result with
      | none => throw (IO.userError "FINITE_FIFTHS_UNEXPECTED_NONE")
      | some cfg =>
        unless cfg.l.isNone && bitValue (cfg.stk 1) == initial.value * 2^p / 5 &&
            bitValue (cfg.stk 2) == 2^p && cfg.var.1.value == initial.value * 2^p % 5 do
          throw (IO.userError "FINITE_FIFTHS_ACTUAL_MACHINE_CHECK_FAILED")
  IO.println "FINITE_TM2_FIFTHS_ACTUAL_TRANSITION_CHECK_PASS"
