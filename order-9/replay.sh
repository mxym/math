#!/bin/sh
set -eu
cd "$(dirname "$0")"
if [ "$#" -eq 0 ]; then
    python3 verify_hadamard.py
else
    python3 verify_hadamard.py "$@"
fi
python3 verify_blocks.py
