#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
python3 -B verify_exact.py
python3 -B verify_direct.py
