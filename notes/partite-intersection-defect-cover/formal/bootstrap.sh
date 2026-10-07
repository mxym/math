#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
export ELAN_HOME="${ELAN_HOME:-$PWD/.elan}"
export MATHLIB_CACHE_DIR="${MATHLIB_CACHE_DIR:-$PWD/.cache/mathlib}"
export MATHLIB_NO_CACHE_ON_UPDATE=1
export PATH="$ELAN_HOME/bin:$PATH"
if [[ ! -x "$ELAN_HOME/bin/elan" ]]; then
  if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
    echo 'Automatic elan bootstrap requires Linux x86_64.' >&2
    exit 1
  fi
  mkdir -p .cache/installer
  curl -fLsS --retry 2 --max-time 180 \
    https://github.com/leanprover/elan/releases/download/v4.2.4/elan-x86_64-unknown-linux-gnu.tar.gz \
    -o .cache/elan.tar.gz
  printf '42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63  .cache/elan.tar.gz\n' | sha256sum --check
  tar -xzf .cache/elan.tar.gz -C .cache/installer
  .cache/installer/elan-init -y --no-modify-path --default-toolchain none
fi
elan toolchain install "$(cat lean-toolchain)"
# Existing manifest pins every dependency; do not run lake update.
lake exe cache get Mathlib.Basic.Real.Basic Mathlib.Tactic.Linarith Mathlib.Tactic.Ring
lake env lean DefectCertificate.lean
