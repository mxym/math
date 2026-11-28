#!/bin/sh
set -eu
python3 verify_center_crt.py
python3 verify_exponents.py
