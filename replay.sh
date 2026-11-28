#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
export PYTHONDONTWRITEBYTECODE=1
python3 verify_factor_erdos_gyarfas_four_orbits.py
python3 verify_factor_erdos_gyarfas_five_orbits.py
python3 verify_factor_erdos_gyarfas_six_orbit_barrier.py
python3 verify_eg_four_orbits_independent.py
python3 verify_eg_five_orbits_independent.py
python3 verify_eg_six_orbits_independent.py
