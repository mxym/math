#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 verify_classical.py
python3 verify_quantum.py
