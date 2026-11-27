#!/bin/sh
set -eu
cd -- "$(dirname -- "$0")"
python3 -B verify_occupancy.py
python3 -B verify_phase.py
