import RationalGateMachine.NormalizedFifths
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for name in [``RationalGateMachine.BinaryTrim.stripZeros_length,``RationalGateMachine.BinaryTrim.stripZeros_append,``RationalGateMachine.BinaryTrim.canonicalBits_cons,``RationalGateMachine.BinaryTrim.canonicalBits_eq_trim,``RationalGateMachine.BinaryTrim.drain_nil,``RationalGateMachine.BinaryTrim.drain_cons,``RationalGateMachine.BinaryTrim.strip_nil,``RationalGateMachine.BinaryTrim.strip_false,``RationalGateMachine.BinaryTrim.strip_true,``RationalGateMachine.BinaryTrim.restore_nil,``RationalGateMachine.BinaryTrim.restore_cons,``RationalGateMachine.BinaryTrim.drain_iterate,``RationalGateMachine.BinaryTrim.restore_iterate,``RationalGateMachine.BinaryTrim.stripTime_bound,``RationalGateMachine.BinaryTrim.strip_iterate,``RationalGateMachine.BinaryTrim.trimRun_steps,``RationalGateMachine.BinaryTrim.terminal_halts,``RationalGateMachine.BinaryTrim.trim_mem_eval,``RationalGateMachine.BinaryTrim.output_canonical,``RationalGateMachine.BinaryTrim.output_value,``RationalGateMachine.BinaryTrim.output_denominator,``RationalGateMachine.BinaryTrim.program_supports,``RationalGateMachine.BinaryTrim.statement_depth,``RationalGateMachine.BinaryTrim.finite_running_control_card,``RationalGateMachine.LabelLift.stepAux,``RationalGateMachine.LabelLift.step,``RationalGateMachine.LabelLift.iterate,``RationalGateMachine.LabelLift.statement_depth,``RationalGateMachine.NormalizedFifths.normalizedRun_steps,``RationalGateMachine.NormalizedFifths.normalizedRun_steps_logarithmic,``RationalGateMachine.NormalizedFifths.terminal_halts,``RationalGateMachine.NormalizedFifths.normalized_mem_eval,``RationalGateMachine.NormalizedFifths.terminal_numerator_canonical,``RationalGateMachine.NormalizedFifths.terminal_numerator_value,``RationalGateMachine.NormalizedFifths.terminal_denominator,``RationalGateMachine.NormalizedFifths.terminal_scratch_empty,``RationalGateMachine.NormalizedFifths.wordValue_eq_providerValue,``RationalGateMachine.NormalizedFifths.terminal_dyadic_error,``RationalGateMachine.NormalizedFifths.program_supports,``RationalGateMachine.NormalizedFifths.finite_running_control_card,``RationalGateMachine.NormalizedFifths.statement_depth] do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Unexpected declaration kind {name}"
  for name in [``RationalGateMachine.BinaryTrim.stripZeros,``RationalGateMachine.BinaryTrim.canonicalBits,``RationalGateMachine.BinaryTrim.configuration,``RationalGateMachine.BinaryTrim.program,``RationalGateMachine.BinaryTrim.advance,``RationalGateMachine.BinaryTrim.stripTime,``RationalGateMachine.BinaryTrim.trimRun,``RationalGateMachine.LabelLift.compile,``RationalGateMachine.LabelLift.configuration,``RationalGateMachine.LabelLift.run,``RationalGateMachine.NormalizedFifths.configuration,``RationalGateMachine.NormalizedFifths.program,``RationalGateMachine.NormalizedFifths.start,``RationalGateMachine.NormalizedFifths.terminal,``RationalGateMachine.NormalizedFifths.fifthsCall,``RationalGateMachine.NormalizedFifths.trimCall,``RationalGateMachine.NormalizedFifths.normalizedRun] do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Unexpected declaration kind {name}"

#check RationalGateMachine.BinaryTrim.stripZeros_length
#print axioms RationalGateMachine.BinaryTrim.stripZeros_length

#check RationalGateMachine.BinaryTrim.stripZeros_append
#print axioms RationalGateMachine.BinaryTrim.stripZeros_append

#check RationalGateMachine.BinaryTrim.canonicalBits_cons
#print axioms RationalGateMachine.BinaryTrim.canonicalBits_cons

#check RationalGateMachine.BinaryTrim.canonicalBits_eq_trim
#print axioms RationalGateMachine.BinaryTrim.canonicalBits_eq_trim

#check RationalGateMachine.BinaryTrim.drain_nil
#print axioms RationalGateMachine.BinaryTrim.drain_nil

#check RationalGateMachine.BinaryTrim.drain_cons
#print axioms RationalGateMachine.BinaryTrim.drain_cons

#check RationalGateMachine.BinaryTrim.strip_nil
#print axioms RationalGateMachine.BinaryTrim.strip_nil

#check RationalGateMachine.BinaryTrim.strip_false
#print axioms RationalGateMachine.BinaryTrim.strip_false

#check RationalGateMachine.BinaryTrim.strip_true
#print axioms RationalGateMachine.BinaryTrim.strip_true

#check RationalGateMachine.BinaryTrim.restore_nil
#print axioms RationalGateMachine.BinaryTrim.restore_nil

#check RationalGateMachine.BinaryTrim.restore_cons
#print axioms RationalGateMachine.BinaryTrim.restore_cons

#check RationalGateMachine.BinaryTrim.drain_iterate
#print axioms RationalGateMachine.BinaryTrim.drain_iterate

#check RationalGateMachine.BinaryTrim.restore_iterate
#print axioms RationalGateMachine.BinaryTrim.restore_iterate

#check RationalGateMachine.BinaryTrim.stripTime_bound
#print axioms RationalGateMachine.BinaryTrim.stripTime_bound

#check RationalGateMachine.BinaryTrim.strip_iterate
#print axioms RationalGateMachine.BinaryTrim.strip_iterate

#check RationalGateMachine.BinaryTrim.trimRun_steps
#print axioms RationalGateMachine.BinaryTrim.trimRun_steps

#check RationalGateMachine.BinaryTrim.terminal_halts
#print axioms RationalGateMachine.BinaryTrim.terminal_halts

#check RationalGateMachine.BinaryTrim.trim_mem_eval
#print axioms RationalGateMachine.BinaryTrim.trim_mem_eval

#check RationalGateMachine.BinaryTrim.output_canonical
#print axioms RationalGateMachine.BinaryTrim.output_canonical

#check RationalGateMachine.BinaryTrim.output_value
#print axioms RationalGateMachine.BinaryTrim.output_value

#check RationalGateMachine.BinaryTrim.output_denominator
#print axioms RationalGateMachine.BinaryTrim.output_denominator

#check RationalGateMachine.BinaryTrim.program_supports
#print axioms RationalGateMachine.BinaryTrim.program_supports

#check RationalGateMachine.BinaryTrim.statement_depth
#print axioms RationalGateMachine.BinaryTrim.statement_depth

#check RationalGateMachine.BinaryTrim.finite_running_control_card
#print axioms RationalGateMachine.BinaryTrim.finite_running_control_card

#check RationalGateMachine.LabelLift.stepAux
#print axioms RationalGateMachine.LabelLift.stepAux

#check RationalGateMachine.LabelLift.step
#print axioms RationalGateMachine.LabelLift.step

#check RationalGateMachine.LabelLift.iterate
#print axioms RationalGateMachine.LabelLift.iterate

#check RationalGateMachine.LabelLift.statement_depth
#print axioms RationalGateMachine.LabelLift.statement_depth

#check RationalGateMachine.NormalizedFifths.normalizedRun_steps
#print axioms RationalGateMachine.NormalizedFifths.normalizedRun_steps

#check RationalGateMachine.NormalizedFifths.normalizedRun_steps_logarithmic
#print axioms RationalGateMachine.NormalizedFifths.normalizedRun_steps_logarithmic

#check RationalGateMachine.NormalizedFifths.terminal_halts
#print axioms RationalGateMachine.NormalizedFifths.terminal_halts

#check RationalGateMachine.NormalizedFifths.normalized_mem_eval
#print axioms RationalGateMachine.NormalizedFifths.normalized_mem_eval

#check RationalGateMachine.NormalizedFifths.terminal_numerator_canonical
#print axioms RationalGateMachine.NormalizedFifths.terminal_numerator_canonical

#check RationalGateMachine.NormalizedFifths.terminal_numerator_value
#print axioms RationalGateMachine.NormalizedFifths.terminal_numerator_value

#check RationalGateMachine.NormalizedFifths.terminal_denominator
#print axioms RationalGateMachine.NormalizedFifths.terminal_denominator

#check RationalGateMachine.NormalizedFifths.terminal_scratch_empty
#print axioms RationalGateMachine.NormalizedFifths.terminal_scratch_empty

#check RationalGateMachine.NormalizedFifths.wordValue_eq_providerValue
#print axioms RationalGateMachine.NormalizedFifths.wordValue_eq_providerValue

#check RationalGateMachine.NormalizedFifths.terminal_dyadic_error
#print axioms RationalGateMachine.NormalizedFifths.terminal_dyadic_error

#check RationalGateMachine.NormalizedFifths.program_supports
#print axioms RationalGateMachine.NormalizedFifths.program_supports

#check RationalGateMachine.NormalizedFifths.finite_running_control_card
#print axioms RationalGateMachine.NormalizedFifths.finite_running_control_card

#check RationalGateMachine.NormalizedFifths.statement_depth
#print axioms RationalGateMachine.NormalizedFifths.statement_depth

#check RationalGateMachine.BinaryTrim.stripZeros
#print axioms RationalGateMachine.BinaryTrim.stripZeros

#check RationalGateMachine.BinaryTrim.canonicalBits
#print axioms RationalGateMachine.BinaryTrim.canonicalBits

#check RationalGateMachine.BinaryTrim.configuration
#print axioms RationalGateMachine.BinaryTrim.configuration

#check RationalGateMachine.BinaryTrim.program
#print axioms RationalGateMachine.BinaryTrim.program

#check RationalGateMachine.BinaryTrim.advance
#print axioms RationalGateMachine.BinaryTrim.advance

#check RationalGateMachine.BinaryTrim.stripTime
#print axioms RationalGateMachine.BinaryTrim.stripTime

#check RationalGateMachine.BinaryTrim.trimRun
#print axioms RationalGateMachine.BinaryTrim.trimRun

#check RationalGateMachine.LabelLift.compile
#print axioms RationalGateMachine.LabelLift.compile

#check RationalGateMachine.LabelLift.configuration
#print axioms RationalGateMachine.LabelLift.configuration

#check RationalGateMachine.LabelLift.run
#print axioms RationalGateMachine.LabelLift.run

#check RationalGateMachine.NormalizedFifths.configuration
#print axioms RationalGateMachine.NormalizedFifths.configuration

#check RationalGateMachine.NormalizedFifths.program
#print axioms RationalGateMachine.NormalizedFifths.program

#check RationalGateMachine.NormalizedFifths.start
#print axioms RationalGateMachine.NormalizedFifths.start

#check RationalGateMachine.NormalizedFifths.terminal
#print axioms RationalGateMachine.NormalizedFifths.terminal

#check RationalGateMachine.NormalizedFifths.fifthsCall
#print axioms RationalGateMachine.NormalizedFifths.fifthsCall

#check RationalGateMachine.NormalizedFifths.trimCall
#print axioms RationalGateMachine.NormalizedFifths.trimCall

#check RationalGateMachine.NormalizedFifths.normalizedRun
#print axioms RationalGateMachine.NormalizedFifths.normalizedRun

open Turing CircuitRecursion RationalGateProvider
#eval do
  -- All 128 seven-bit raw words, including high zero padding and zero.
  -- These Nat/testBit fixture constructors never occur in machine code.
  let denoms : List (List Bool) := [[],[true],[false,true,false]]
  for q in List.range 128 do
    let raw:=List.ofFn (fun j : Fin 7 => Nat.testBit q j.val)
    for den in denoms do
      let count:=RationalGateMachine.BinaryTrim.stripTime raw.reverse+(raw.length+1)
      let result:=RationalGateMachine.BinaryTrim.advance^[count]
        (some (RationalGateMachine.BinaryTrim.configuration (some .drain) none raw den []))
      match result with
      | none => throw (IO.userError "TRIM_UNEXPECTED_NONE")
      | some cfg =>
          unless cfg.l.isNone && cfg.var.isNone && cfg.stk .left == (binaryTrimProgram raw).bits &&
              cfg.stk .right == den && cfg.stk .work == [] &&
              binaryWordValue (cfg.stk .left) == q && count ≤ 2*raw.length+3 &&
              (TM2.step RationalGateMachine.BinaryTrim.program cfg).isNone do
            throw (IO.userError "ACTUAL_FINITE_TRIM_FAILED")
  let initials : List Remainder := [.r0,.r1,.r2,.r3,.r4]
  for initial in initials do
    for q in List.range 33 do
      let raw:=List.ofFn (fun j : Fin 6 => Nat.testBit q j.val)
      let i : BinaryIndex:=⟨(binaryTrimProgram raw).bits,binaryTrimProgram_canonical raw⟩
      unless i.value == q do throw (IO.userError "NORMALIZED_INPUT_FIXTURE_FAILED")
      let count:=(RationalGateMachine.NormalizedFifths.normalizedRun initial i).steps
      let result:=(fun c : Option RationalGateMachine.NormalizedFifths.Configuration =>
        c.bind (TM2.step RationalGateMachine.NormalizedFifths.program))^[count]
        (some (RationalGateMachine.NormalizedFifths.start initial i))
      match result with
      | none => throw (IO.userError "NORMALIZED_FIFTHS_UNEXPECTED_NONE")
      | some cfg =>
          unless cfg.l.isNone && cfg.var.2.isNone && cfg.stk .work == [] &&
              cfg.stk .left == (binaryTrimProgram (RationalGateProvider.run initial q).bits).bits &&
              binaryWordValue (cfg.stk .left) == initial.value*2^q/5 &&
              cfg.stk .right == denominatorBits q && bitValue (cfg.stk .right) == 2^q &&
              cfg.var.1.value == initial.value*2^q%5 &&
              count ≤ (2*Nat.clog 2 (q+1)+9)*q+6 &&
              (TM2.step RationalGateMachine.NormalizedFifths.program cfg).isNone do
            throw (IO.userError "NORMALIZED_FIFTHS_ACTUAL_MACHINE_FAILED")
  IO.println "FINITE_TM2_TRIM384_AND_NORMALIZED_FIFTHS165_ACTUAL_RUNS_PASS"
