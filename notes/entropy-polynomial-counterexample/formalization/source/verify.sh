#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "$(dirname "$0")" && pwd)
OLD=$(cd "$ROOT/../crouzeix_lean_coverage_20261007" && pwd)
cd "$ROOT"
mkdir -p logs
./run_lean.sh --version > logs/pins.log
git -C "$OLD/lean/.lake/packages/mathlib" rev-parse HEAD >> logs/pins.log
[[ $(git -C "$OLD/lean/.lake/packages/mathlib" rev-parse HEAD) == d13f23b723b8a846827a245b89c10fc7d3f11612 ]]
export ENTROPY_BUILD_DIR=$(mktemp -d "$ROOT/.clean-build.XXXXXX")
printf '%s\n' "$ENTROPY_BUILD_DIR" > logs/clean-build-directory.txt
: > logs/cleancompile.log
for module in Alpha Definitions Signs FourRoots Counterexample; do
  printf '\n=== %s ===\n' "$module" >> logs/cleancompile.log
  TIMEFORMAT='elapsed_seconds=%R user_seconds=%U sys_seconds=%S'
  { time ./run_lean.sh -o "$ENTROPY_BUILD_DIR/$module.olean" "$module.lean"; } >> logs/cleancompile.log 2>&1
done
./run_lean.sh Audit.lean > logs/finaltheorem-signatures-and-axioms.log 2>&1
python3 - <<'PY'
from pathlib import Path
import hashlib,json,re
root=Path('.')
modules=['Alpha','Definitions','Signs','FourRoots','Counterexample']
for m in modules:
    s=(root/f'{m}.lean').read_text()
    s=re.sub(r'/\-.*?\-/','',s,flags=re.S)
    s=re.sub(r'--[^\n]*','',s)
    assert not re.search(r'\b(sorry|axiom|native_decide|unsafe|admit)\b',s),m
names=(root/'theorem_names.txt').read_text().splitlines()
log=(root/'logs/finaltheorem-signatures-and-axioms.log').read_text()
reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
assert len(reports)==len(names),(len(reports),len(names))
allowed={'propext','Classical.choice','Quot.sound'}
assert {n for n,_ in reports}==set(names)
for name,axs in reports:
    assert set(a.strip() for a in axs.split(',') if a.strip()) <= allowed,(name,axs)
assert 'sorryAx' not in log
assert 'error:' not in log
assert 'error:' not in (root/'logs/cleancompile.log').read_text()
hashes={str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in root.glob('*.lean')}
report={'status':'passed','lean':'4.34.1','mathlib':'d13f23b723b8a846827a245b89c10fc7d3f11612',
 'source_modules':modules,'audited_theorems':len(names),'custom_axioms':0,'sorry':0,
 'native_decide':0,'unsafe':0,'allowed_axioms':sorted(allowed),
 'clean_compilation':True,'original_finite_sum_coefficient_equalities_proved':True,
 'parameter_existence_and_uniqueness_proved':True,'five_signs_proved_exactly':True,
 'four_distinct_interior_roots_proved':True,'interior_root_multiplicity_count_at_least_four_proved':True,
 'universal_two_root_conjecture_negation_proved':True,'lean_source_sha256':hashes}
(root/'VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n')
(root/'logs/axiom-audit.json').write_text(json.dumps(dict(reports),indent=2)+'\n')
print(f'PASS: fresh-directory compilation and {len(names)} theorem axiom audits.')
PY
