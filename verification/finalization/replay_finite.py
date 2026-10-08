#!/usr/bin/env python3
"""Replay manuscript arithmetic/checker obligations in disposable copies."""
import argparse
from datetime import datetime, timezone
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'manuscripts'))
from historical import HistoricalInputs

CHECKERS = {
    'fractional-cover-spectrum': [
        'notes/sharp-fractional-cover-frontier/check_exact.py',
        'notes/fractional-design-stability/check_exact.py',
        'notes/fractional-matching-spectrum/check_exact.py'],
    'complex-permanent-pencil': [
        'notes/complex-permanent-determinant/check.py',
        'notes/complex-permanent-determinant/check_lens.py',
        'notes/complex-permanent-determinant/check_full_norm.py',
        'notes/complex-permanent-determinant/check_matrix.py',
        'notes/complex-permanent-determinant/check_tensor.py',
        'notes/four-row-permanent-tradeoff/check.py',
        'notes/four-row-permanent-tradeoff/check_tensor.py'],
    'orbital-atom-stability': [
        'notes/sharp-robust-permanent/code/check_atom_modulus.py',
        'notes/sharp-robust-permanent/code/check_doubly_transitive.py',
        'notes/sharp-robust-permanent/code/check_edge_action_s5.py',
        'notes/sharp-robust-permanent/code/check_all_two_subset_actions.py',
        'notes/sharp-robust-permanent/code/check_three_subset_certificates.py',
        'notes/sharp-robust-permanent/code/check_three_subset_compressed_24_120.py',
        'notes/sharp-robust-permanent/code/check_three_subset_asymptotic_algebra.py',
        'notes/johnson-short-cycle-spectrum/transfer.py',
        'notes/johnson-short-cycle-spectrum/check_k4.py',
        'notes/johnson-short-cycle-spectrum/check_k4_26_50.py'],
}


def run(command, cwd, logfile):
    process = subprocess.run(command, cwd=cwd, capture_output=True)
    logfile.write_bytes(process.stdout + process.stderr)
    if process.returncode:
        raise RuntimeError(f'{command}: exit {process.returncode}; see {logfile}')
    return {'exit_code': process.returncode,
            'stdout_sha256': sha256(process.stdout).hexdigest(),
            'stderr_sha256': sha256(process.stderr).hexdigest(),
            'log': logfile.name}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    # All paths in the new papers and all historical payloads are pinned.
    historical=HistoricalInputs()
    historical.verify_all()
    pins=historical.pins
    rows = []
    with tempfile.TemporaryDirectory(prefix='math-manuscript-finite-') as temp:
        scratch = Path(temp)
        packages = {Path(p).parts[1] for paths in CHECKERS.values() for p in paths}
        packages |= {'quadratic-dimensional-simplex-stability',
                     'continuum-power-avoidance-unified'}
        for rel in pins['files']:
            parts=Path(rel).parts
            if len(parts)>1 and parts[0]=='notes' and parts[1] in packages:
                destination=scratch/rel
                destination.parent.mkdir(parents=True,exist_ok=True)
                destination.write_bytes(historical.read_bytes(rel))
        for family, paths in CHECKERS.items():
            for rel in paths:
                path = scratch/rel
                label = family+'-'+Path(rel).parts[1]+'-'+path.stem
                a = run([sys.executable, '-I', '-B', str(HERE/'strict_checker.py'), str(path)],
                        path.parent, output/(label+'.log'))
                b = run([sys.executable, '-I', '-O', '-B', str(HERE/'strict_checker.py'), str(path)],
                        path.parent, output/(label+'-optimized-launcher.log'))
                if a['stdout_sha256'] != b['stdout_sha256'] or a['stderr_sha256'] != b['stderr_sha256']:
                    raise RuntimeError('Launcher optimization changes exact output: '+rel)
                rows.append({'family':family,'source':rel,'replays':[a,b],
                    'assertions':'entrypoint optimize=0; optimized launcher restarts an unoptimized isolated child, preserving imported-helper assertions'})
                print('PASS '+rel, flush=True)
        for package in ('sharp-fractional-cover-frontier', 'fractional-design-stability',
                        'fractional-matching-spectrum'):
            path = scratch/'notes'/package/'verify.py'
            record = run([sys.executable, '-B', str(path)], path.parent,
                         output/(package+'-frozen-inventory.log'))
            rows.append({'family':'fractional-cover-spectrum','source':str(path.relative_to(scratch)),
                         'replays':[record],'scope':'historical inventory and exact-output comparison'})
        path = scratch/'notes/quadratic-dimensional-simplex-stability/verify.py'
        rows.append({'family':'sharp-simplex-stability', 'source':str(path.relative_to(scratch)),
            'replays':[run([sys.executable,'-B',str(path),'--extracted'],path.parent,
                          output/'simplex-five-checkers.log')],
            'scope':'historical hashes and five isolated assertion-enabled regressions; floating diagnostics are not proofs'})
        path = scratch/'notes/continuum-power-avoidance-unified/run_checks.py'
        rows.append({'family':'continuum-power-avoidance', 'source':str(path.relative_to(scratch)),
            'replays':[run([sys.executable,'-B',str(path),'--repository-root',str(ROOT)],path.parent,
                          output/'continuum-inventory-correspondence.log')],
            'scope':'historical inventory, revision chain, and formal correspondence; not a Lean replay'})
    report = {'schema':'manuscript-finite-replay-v1','status':'PASS',
        'timestamp_utc':datetime.now(timezone.utc).isoformat(),
        'python':sys.version,'source_snapshot':pins['commit'], 'checks':rows,
        'historical_git_blobs_used':sorted(historical.restored),
        'scope':'Finite identities/certificates and package integrity. Analytic/infinite theorems require the written proofs.'}
    (output/'report.json').write_text(json.dumps(report, indent=2)+'\n')
    print('PASS all finite manuscript obligations', flush=True)


if __name__ == '__main__':
    main()
