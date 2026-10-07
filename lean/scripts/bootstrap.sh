#!/usr/bin/env bash
# Official pinned Linux x86_64 installer. Uses only project-local tool/cache paths.
set -euo pipefail
task_project_root="$(cd "$(dirname "$0")/.." && pwd)"
cd "$task_project_root"
if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  printf 'This installer supports Linux x86_64. See README.md for the portable route.\n' >&2
  exit 1
fi
for task_required_command in curl git python3 tar sha256sum; do
  command -v "$task_required_command" >/dev/null
done
export ELAN_HOME="$task_project_root/.elan"
export MATHLIB_CACHE_DIR="$task_project_root/.cache/mathlib"
export PATH="$ELAN_HOME/bin:$PATH"
export MATHLIB_NO_CACHE_ON_UPDATE=1
mkdir -p .cache/elan-installer "$MATHLIB_CACHE_DIR" logs
task_elan_archive="$task_project_root/.cache/elan-4.2.4-linux-x86_64.tar.gz"
if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  curl -fLsS --retry 2 --max-time 180 \
    https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz \
    -o "$task_elan_archive"
  printf '42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63  %s\n' \
    "$task_elan_archive" | sha256sum --check
  tar -xzf "$task_elan_archive" -C .cache/elan-installer
  .cache/elan-installer/elan-init -y --no-modify-path --default-toolchain none
fi
elan toolchain install "$(cat lean-toolchain)"
# Lake fetches the exact revisions in lake-manifest.json. Do not run lake update.
mapfile -t task_cache_modules < scripts/mathlib-modules.txt
lake exe cache get "${task_cache_modules[@]}" > logs/bootstrap-cache.log 2>&1
python3 scripts/check_pins.py > logs/pins.log
bash scripts/verify.sh
printf 'Verification complete. See logs/clean-build.log and logs/axioms.log.\n'
