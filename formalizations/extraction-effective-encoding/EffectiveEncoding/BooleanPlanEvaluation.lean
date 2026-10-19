import EffectiveEncoding.BooleanMaskContextProgram

open CircuitRecursion EffectiveEncoding

-- One actual complete small context covers both empty and nonempty plan branches.
#eval let r:=booleanMaskContextProgram (by decide : 0<2)
      (r.planTable.programs.map (fun p =>
        (p.built.plan.target.val,p.built.plan.parityWires.map Fin.val,
          p.built.plan.leading.length,p.built.plan.trailing.length,p.built.plan.negateOne,p.actions)),
        r.planActions,r.actions)
