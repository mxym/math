#!/usr/bin/env bash
set -euo pipefail
HERE=$(cd -- "$(dirname -- "$0")" && pwd)
exec bash "$HERE/../avoidance-covering-provenance/build.sh" critical-covering-gauge
