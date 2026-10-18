import RationalGateUniversality
open Lean Elab Command

run_cmd do
  let env ← getEnv
  for name in [``RationalGateUniversality.ext_first_row,
    ``RationalGateUniversality.zTorus_mul,
    ``RationalGateUniversality.xTorus_mul,
    ``RationalGateUniversality.continuous_zTorus,
    ``RationalGateUniversality.continuous_xTorus,
    ``RationalGateUniversality.su2_topologicalGroup,
    ``RationalGateUniversality.z_x_z_entry00,
    ``RationalGateUniversality.z_x_z_entry01,
    ``RationalGateUniversality.su2_euler,
    ``RationalGateUniversality.zTorus_phaseCircle,
    ``RationalGateUniversality.xTorus_phaseCircle,
    ``RationalGateUniversality.rationalGate_dense,
    ``RationalGateUniversality.rationalGate_precomputedNet] do
    match env.find? name with
    | some (.thmInfo _) => pure ()
    | _ => throwError "Expected theorem {name}"
  for name in [``RationalGateUniversality.zTorus,
    ``RationalGateUniversality.xTorus,
    ``RationalGateUniversality.zHom,
    ``RationalGateUniversality.xHom] do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Expected definition {name}"

#check RationalGateUniversality.ext_first_row
#print axioms RationalGateUniversality.ext_first_row
#check RationalGateUniversality.zTorus_mul
#print axioms RationalGateUniversality.zTorus_mul
#check RationalGateUniversality.xTorus_mul
#print axioms RationalGateUniversality.xTorus_mul
#check RationalGateUniversality.continuous_zTorus
#print axioms RationalGateUniversality.continuous_zTorus
#check RationalGateUniversality.continuous_xTorus
#print axioms RationalGateUniversality.continuous_xTorus
#check RationalGateUniversality.su2_topologicalGroup
#print axioms RationalGateUniversality.su2_topologicalGroup
#check RationalGateUniversality.z_x_z_entry00
#print axioms RationalGateUniversality.z_x_z_entry00
#check RationalGateUniversality.z_x_z_entry01
#print axioms RationalGateUniversality.z_x_z_entry01
#check RationalGateUniversality.su2_euler
#print axioms RationalGateUniversality.su2_euler
#check RationalGateUniversality.zTorus_phaseCircle
#print axioms RationalGateUniversality.zTorus_phaseCircle
#check RationalGateUniversality.xTorus_phaseCircle
#print axioms RationalGateUniversality.xTorus_phaseCircle
#check RationalGateUniversality.rationalGate_dense
#print axioms RationalGateUniversality.rationalGate_dense
#check RationalGateUniversality.rationalGate_precomputedNet
#print axioms RationalGateUniversality.rationalGate_precomputedNet
#check RationalGateUniversality.zTorus
#print axioms RationalGateUniversality.zTorus
#check RationalGateUniversality.xTorus
#print axioms RationalGateUniversality.xTorus
#check RationalGateUniversality.zHom
#print axioms RationalGateUniversality.zHom
#check RationalGateUniversality.xHom
#print axioms RationalGateUniversality.xHom
