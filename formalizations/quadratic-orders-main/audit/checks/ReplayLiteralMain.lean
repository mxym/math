import ArithmeticSupplyWeakMain
import EmptyKernelReplay
open Lean Elab Command
example : Entry002.MainTarget := Entry002.arithmeticSupply_mainTarget_proved
run_cmd do
  let some ci := (← getEnv).find? `Entry002.arithmeticSupply_mainTarget_proved |
    throwError "Literal main missing"
  unless ci.isTheorem && ci.type == mkConst `Entry002.MainTarget do
    throwError "Main endpoint does not have the literal no-premise target type"
#print Entry002.arithmeticSupply_mainTarget_proved
#print axioms Entry002.arithmeticSupply_mainTarget_proved
run_cmd IndependentEmptyReplay.run #[`Entry002.arithmeticSupply_mainTarget_proved] "literal-main-empty-kernel.json"
