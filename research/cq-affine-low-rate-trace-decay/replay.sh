#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 verify_probabilities.py
python3 verify_quantum.py
