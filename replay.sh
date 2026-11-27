#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 verify_exact.py
python3 verify_independent.py
