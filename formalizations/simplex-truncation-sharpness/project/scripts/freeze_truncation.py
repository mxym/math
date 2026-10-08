#!/usr/bin/env python3
"""Freeze all actual truncation proof sources and diagnostic inventories."""
from pathlib import Path
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / 'formal'
SOURCES = ROOT / 'sources'

paths = sorted(p for p in (FORMAL / 'Entry005').glob('Truncation*.lean')
               if p.name != 'TruncationGeometryAudit.lean')
records, bymodule = [], {}
for path in paths:
    rel = path.relative_to(ROOT).as_posix()
    records.append({'path': rel, 'sha256': hashlib.sha256(path.read_bytes()).hexdigest()})
    namespace = 'OAI.ProjectionCounterexample' if path.stem == 'TruncationSimplexVolume' else 'Entry005'
    names = re.findall(r'^(?:@\[[^\n]+\]\s*)?(?:theorem|lemma)\s+(\S+)', path.read_text(), re.M)
    bymodule[rel] = [namespace + '.' + name for name in names]
newnames = sorted(name for names in bymodule.values() for name in names)
if len(newnames) != len(set(newnames)):
    raise RuntimeError('Duplicate new public proof name')
for filename, value in [('truncation-source-hashes.json', records),
                        ('truncation-public-theorems.json', newnames),
                        ('truncation-public-by-module.json', bymodule)]:
    (SOURCES / filename).write_text(json.dumps(value, indent=2) + '\n')
claims = {
    'literal_targets_unchanged': True,
    'actual_truncation_volume': True,
    'actual_intrinsic_facet_areas': True,
    'actual_projection_body_and_directional_volume': True,
    'actual_defect_exact_no_geometric_premise': True,
    'actual_global_maximum_inscribed_simplex': True,
    'actual_original_centroid_excess_exact': True,
    'literal_truncationSharpnessGoal_proved': True,
    'sharpness_exponent': '1/(d-1)',
    'upper_bound_Main_proved_here': False,
    'classification_of_all_maximizing_simplices_proved_here': False,
}
(SOURCES / 'truncation-final-claims.json').write_text(json.dumps(claims, indent=2) + '\n')
inherited = json.loads((SOURCES / 'all-public-theorems.json').read_text())
allnames = sorted(set(inherited) | set(newnames))
audit = FORMAL / 'audit'
audit.mkdir(exist_ok=True)
(audit / 'truncation-all-statements.lean').write_text(
    'import Entry005.TruncationFormalization\n\n' +
    'set_option format.width 120\n\n' +
    '#print Entry005.truncationSharpnessGoal\n#print Entry005.entryDefect\n' +
    '#print Entry005.maximumInscribed\n#print Entry005.centeredDilation\n' +
    '#print Entry005.excess\n\n' +
    ''.join(f'#check {name}\n#print axioms {name}\n' for name in allnames))
(audit / 'truncation-owned.lean').write_text('''import Entry005.TruncationFormalization
import Lean

/- Diagnostic only: enumerate actual declaring modules, including private and
generated declarations, using Lean's same collector as `#print axioms`.
No diagnostic evaluation supplies a theorem proof. -/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let mut names : Array Name := #[]
  for (name, _) in env.constants.toList do
    let owned := (env.getModuleIdxFor? name).any fun idx =>
      let owner := env.header.moduleNames[idx.toNat]!
      (`Entry005).isPrefixOf owner || (`Mxym).isPrefixOf owner || (`OAI).isPrefixOf owner
    if owned then names := names.push name
  for name in names.qsort (fun a b => a.toString < b.toString) do
    logInfo m!"OWNED_DECL {name}"
    let axioms ← collectAxioms name
    logInfo m!"OWNED_AXIOMS {name}: {axioms.toList}"
    if let some info := env.find? name then
      if info.isTheorem && !name.isInternal then
        if let some idx := env.getModuleIdxFor? name then
          logInfo m!"PUBLIC_THEOREM {env.header.moduleNames[idx.toNat]!} {name}"
''')
print(f'Frozen {len(paths)} new mathematical modules, {len(newnames)} new public proof names; {len(allnames)} total')
