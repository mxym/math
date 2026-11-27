#!/bin/sh
set -eu
cd "$(dirname "$0")"
python3 verify_graph.py
python3 verify_n5.py
