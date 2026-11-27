#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 verify_bits.py
python3 verify_direct.py
