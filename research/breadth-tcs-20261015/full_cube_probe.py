from pathlib import Path
import json
from finite_decoder import solve

result = solve(6, list(range(64)), d=2, timeout_ms=120000)
result['scope'] = ('Only the full cube on six coordinates with size two. Its actual '
                   'VC dimension is six, so UNSAT would not refute SC0. SAT would '
                   'supply a verified decoder for every class on this domain. '
                   'No conclusion for arbitrary n at fixed VC dimension.')
Path(__file__).with_name('FULL_CUBE_SIX_PROBE.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k != 'decoder'},indent=2))
