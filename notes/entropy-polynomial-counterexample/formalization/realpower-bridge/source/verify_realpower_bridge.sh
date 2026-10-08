#!/usr/bin/env bash
set -euo pipefail
ROOT=$(cd "$(dirname "$0")" && pwd)
cd "$ROOT"
LOG="$ROOT/logs/realpower_bridge"
mkdir -p "$LOG"
python3 - <<'PY'
from pathlib import Path
import json,hashlib
r=Path('.')
base=json.loads((r/'VERIFICATION.json').read_text())['lean_source_sha256']
new=json.loads((r/'REALPOWER_BRIDGE_SOURCE_SHA256.json').read_text())
for f,h in new.items():
    assert hashlib.sha256((r/f).read_bytes()).hexdigest()==h,f
for f in ['Alpha.lean','Definitions.lean','Signs.lean','FourRoots.lean','Counterexample.lean']:
    assert new[f]==base[f],f
PY
export ENTROPY_BUILD_DIR=$(mktemp -d "$ROOT/.realpower-clean.XXXXXX")
printf '%s\n' "$ENTROPY_BUILD_DIR" > "$LOG/clean-build-directory.txt"
./run_lean.sh --version > "$LOG/pins.log"
git -C "$ROOT/../crouzeix_lean_coverage_20261007/lean/.lake/packages/mathlib" rev-parse HEAD >> "$LOG/pins.log"
: > "$LOG/cleancompile.log"
for module in Alpha Definitions Signs FourRoots Counterexample RealPowerBridge; do
  printf '\n=== %s ===\n' "$module" >> "$LOG/cleancompile.log"
  TIMEFORMAT='elapsed_seconds=%R user_seconds=%U sys_seconds=%S'
  { time ./run_lean.sh -o "$ENTROPY_BUILD_DIR/$module.olean" "$module.lean"; } >> "$LOG/cleancompile.log" 2>&1
done
./run_lean.sh RealPowerBridgeAudit.lean > "$LOG/signatures-and-axioms.log" 2>&1
python3 - <<'PY'
from pathlib import Path
import hashlib,json,re
r=Path('.')
log=(r/'logs/realpower_bridge/signatures-and-axioms.log').read_text()
names=(r/'realpower_bridge_theorem_names.txt').read_text().splitlines()
reports=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",log)
assert len(reports)==6==len(names)
assert {n for n,_ in reports}==set(names)
allowed={'propext','Classical.choice','Quot.sound'}
for n,a in reports:
    assert {x.strip() for x in a.split(',')}<=allowed,(n,a)
s=(r/'RealPowerBridge.lean').read_text()
s=re.sub(r'/\-.*?\-/','',s,flags=re.S)
s=re.sub(r'--[^\n]*','',s)
assert not re.search(r'\b(sorry|axiom|native_decide|unsafe|admit)\b',s)
compilelog=(r/'logs/realpower_bridge/cleancompile.log').read_text()
for token in ['error:','warning:','sorryAx']:
    assert token not in compilelog+log,token
hashes=json.loads((r/'REALPOWER_BRIDGE_SOURCE_SHA256.json').read_text())
for f,h in hashes.items():
    assert hashlib.sha256((r/f).read_bytes()).hexdigest()==h,f
result={'status':'passed','extension':'real-power definition bridge','base_five_sources_unchanged':True,
'fresh_build_all_six_modules':True,'additional_theorems_audited':6,'axioms':sorted(allowed),
'original_real_power_equivalence_proved':True,'original_real_power_alpha_exists_unique_proved':True,
'original_real_power_counterexample_proved':True,'original_real_power_conjecture_negation_proved':True,
'proof_source_sha256':hashes,'theorem_axioms':dict(reports)}
(r/'REALPOWER_BRIDGE_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS: six-module fresh compilation; six added real-power theorems use only standard axioms; original five sources unchanged.')
PY
