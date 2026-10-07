#!/usr/bin/env python3
"""Replay exact and numerical controls without modifying the release package.

These finite checks are diagnostics, never a proof of the analytic theorem.
"""
import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
TASKS = [
    ('007-interpolation', 'sources/preprints/007-tail-brenier-stability/v1/verification/check_interpolation.py'),
    ('007-steep', 'sources/preprints/007-tail-brenier-stability/v2/verification/check_steep_example.py'),
    ('008-exact', 'sources/preprints/008-density-overlap-phase/v1/verification/check_exact.py'),
    ('root-overlap', 'verification/check_root_overlap.py'),
]

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output_directory', type=Path)
    args = parser.parse_args()
    out = args.output_directory.resolve()
    if out == ROOT or ROOT in out.parents:
        parser.error('Choose an output directory outside the immutable release package.')
    out.mkdir(parents=True, exist_ok=True)
    report = {'scope': 'finite exact regressions and numerical diagnostics, not analytic proofs', 'runs': []}
    env = {**os.environ, 'PYTHONDONTWRITEBYTECODE': '1', 'PYTHONHASHSEED': '0'}
    for name, relative in TASKS:
        outputs = []
        for optimized in (False, True):
            mode = 'optimized' if optimized else 'normal'
            with tempfile.TemporaryDirectory(prefix='transport-check-') as tmp:
                work = Path(tmp)
                script = work / 'check.py'
                shutil.copyfile(ROOT / relative, script)
                output = work / ('root-overlap-results.json' if name == 'root-overlap' else 'result.json')
                command = [sys.executable] + (['-O'] if optimized else []) + [str(script)]
                if name != 'root-overlap':
                    command += ['--output', str(output)]
                result = subprocess.run(command, cwd=work, env=env, text=True, capture_output=True)
                if result.returncode != 0:
                    raise RuntimeError(f'{name} ({mode}) failed:\n{result.stdout}\n{result.stderr}')
                if not output.is_file():
                    raise RuntimeError(f'{name} ({mode}) produced no result')
                data = output.read_bytes()
                parsed = json.loads(data)
                destination = out / f'{name}-{mode}.json'
                destination.write_bytes(data)
                (out / f'{name}-{mode}.txt').write_text(result.stdout)
                outputs.append(data)
                report['runs'].append({'name': name, 'mode': mode, 'status': 'PASS', 'result': destination.name})
                print(f'PASS: {name} ({mode})', flush=True)
        if outputs[0] != outputs[1]:
            raise RuntimeError(f'{name}: normal/-O result mismatch')
    report['normal_optimized_results_identical'] = True
    (out / 'CHECK_REPORT.json').write_text(json.dumps(report, indent=2) + '\n')
    print('PASS: all four suites, normal and -O; result bytes agree.')

if __name__ == '__main__':
    main()
