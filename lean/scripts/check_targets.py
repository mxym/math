#!/usr/bin/env python3
"""Record exact unproved Prop targets, without counting them as theorem proofs."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent.parent
rows=json.loads((ROOT/'declaration-inventory.json').read_text())
byname={r['name']:r for r in rows}
targets=['sharpMainGoal','sharpLocalGoal','thresholdGateGoal','truncationSharpnessGoal','simplexMatrixVolumeInterfaceGoal']
result=[]
for short in targets:
 n='Entry005.'+short
 row=byname.get(n)
 if row is None or row['kind']!='definition' or row['type']!='Prop':
  raise RuntimeError('Target is not an unproved Prop definition: '+n)
 result.append(dict(name=n,status='defined, typechecked, unproved',counted_as_proved_export=False))
(ROOT/'target-status.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: five goal definitions typecheck; none is a proved theorem export.')
