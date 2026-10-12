"""Finite numerical regressions. The universal inequalities are proved in the report."""
import json
import math
from pathlib import Path
rows = []
for d in list(range(3, 101)) + [200, 500, 1000, 10000]:
    m = d - 1
    R = d * math.sqrt(d + 2)
    M = 4 * d * R
    C = (d + 1)**2 * (d + 2)
    L = 2 * math.sqrt(m) * (R + 1)
    # log(a+b) = log(a) + log1p(b/a), avoiding overflow for large d.
    log_dominant = math.log(d * M) + (d - 1) * math.log(2)
    log_bracket = log_dominant + math.log1p((1 + M) * math.exp(-log_dominant))
    log_J = math.log(d / 2) + d * math.log(2 * R) + log_bracket
    log_G = math.log(8 * (R + 1) * d * L) + (log_J + math.log(C)) / m
    log_e0 = -log_J - math.log(C) - m * math.log(8 * d * L)
    assert log_G <= 20 * math.log(2) + 6 * math.log(d)
    assert log_J >= math.log(M)
    assert abs(log_G + log_e0 / m - math.log(R + 1)) < 1e-10
    assert math.sqrt(m) / (8 * d * L) <= 0.5
    rows.append({'d': d, 'log_G': log_G, 'G_over_d6': math.exp(log_G - 6 * math.log(d)), 'log_e0': log_e0})
result = {'scope': __doc__, 'cases': len(rows), 'rows': rows}
Path(__file__).with_name('constant_checks.json').write_text(json.dumps(result, indent=2) + '\n')
print(f'PASS: {len(rows)} numerical constant/gate checks; universal inequalities are proved analytically.')
