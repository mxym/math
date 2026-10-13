#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export MATHLIB_NO_CACHE_ON_UPDATE=1
mapfile -t imports < <(python3 - <<'PY'
from pathlib import Path
import json
imports=set()
for module in json.loads(Path('MODULES.json').read_text()):
 for line in Path(module.replace('.','/')+'.lean').read_text().splitlines():
  if line.startswith('import Mathlib.'):
   imports.add(line.split()[1])
print('\n'.join(sorted(imports)))
PY
)
lake exe cache get "${imports[@]}"
