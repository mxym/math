#!/bin/sh
set -eu
if [ "$#" -ne 1 ]; then
  echo 'Usage: sh build.sh NEW_OUTPUT_DIRECTORY_OUTSIDE_THIS_PACKAGE' >&2
  exit 2
fi
ROOT=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd -P)
exec python3 -B "$ROOT/verify.py" --build-output "$1"
