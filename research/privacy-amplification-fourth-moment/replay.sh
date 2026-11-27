#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 verify_occupancy.py
python3 verify_gram.py
