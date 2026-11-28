#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum -c SHA256SUMS
python3 verify_coherent_condorcet_maxima.py
python3 verify_coherent_condorcet_one_defect.py
python3 verify_coherent_condorcet_ten.py
python3 verify_condorcet_9_10_independent.py lower
python3 verify_condorcet_9_10_independent.py 9
python3 verify_condorcet_9_10_independent.py 10
python3 verify_condorcet_9_10_independent.py defect 0 84
