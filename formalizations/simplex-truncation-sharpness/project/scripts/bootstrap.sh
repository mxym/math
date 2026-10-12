#!/usr/bin/env bash
set -euo pipefail
# Local installation only. Preserve proxy, CA trust and every security setting.
task_root="$(cd "$(dirname "$0")/.." && pwd)"
lean_version=4.34.1
lean_archive_sha=47bf4bbd78f70c2e9670598ab7124d92b6efb7330ff33e5fbb4030f6fd72e4e4
if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  echo 'This bootstrap supports the verified official Linux x86_64 archive.' >&2
  exit 1
fi
lean_bin="${ENTRY005_LEAN_BIN:-$task_root/.toolchain/lean-$lean_version-linux/bin}"
if [[ ! -x "$lean_bin/lean" || ! -x "$lean_bin/lake" ]]; then
  if [[ -n "${ENTRY005_LEAN_BIN:-}" ]]; then
    echo 'ENTRY005_LEAN_BIN does not contain executable lean and lake.' >&2
    exit 1
  fi
  mkdir -p "$task_root/.toolchain" "$task_root/.downloads"
  archive="$task_root/.downloads/lean-$lean_version-linux.tar.zst"
  curl --fail --location --retry 3 --output "$archive" \
    "https://github.com/leanprover/lean4/releases/download/v$lean_version/lean-$lean_version-linux.tar.zst"
  printf '%s  %s\n' "$lean_archive_sha" "$archive" | sha256sum --check --status
  tar --zstd -xf "$archive" -C "$task_root/.toolchain"
fi
export PATH="$lean_bin:$PATH"
export MATHLIB_CACHE_DIR="$task_root/.cache/mathlib"
export MATHLIB_NO_CACHE_ON_UPDATE=1
lean --version | rg -F 'Lean (version 4.34.1,'
lean --version | rg -F 'commit 5045d0056413266e57c625dcd7c365b10e377c52'
cd "$task_root/formal"
# Reuse the complete pinned manifest. Do not run lake update.
lake env lean --version
mapfile -t modules < scripts/mathlib-modules.txt
lake exe cache get "${modules[@]}"
cd "$task_root"
python3 scripts/verify_truncation.py --lean-bin "$lean_bin"
