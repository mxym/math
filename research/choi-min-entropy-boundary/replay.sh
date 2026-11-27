#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
python3 -B verify_rational.py
python3 -B verify_choi.py
