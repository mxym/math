#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p logs
python3 scripts/check_pins.py > logs/pins.log
python3 scripts/generate_audit.py > logs/source-audit.log
python3 - <<'PY' > logs/clean-build.log
from pathlib import Path
from datetime import datetime, timezone
import shutil
root = Path.cwd()
build = root / '.lake/build'
print('Clean verification started:', datetime.now(timezone.utc).isoformat())
print('Removed project build directory:', build)
print('Dependency build/cache artifacts are retained; all project and vendored proof modules will be recompiled.')
if build.exists():
    shutil.rmtree(build)
PY
lean --version >> logs/clean-build.log
lake --version >> logs/clean-build.log
lake build >> logs/clean-build.log 2>&1
printf 'lake build exit status: 0\n' >> logs/clean-build.log
lake env lean Audit.lean > logs/axioms.log 2>&1
lake env lean Statements.lean > logs/statements.log 2>&1
python3 scripts/check_axioms.py > logs/axiom-check.log
python3 scripts/generate_coverage.py > logs/coverage-check.log
cat logs/axiom-check.log
cat logs/coverage-check.log
