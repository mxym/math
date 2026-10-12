"""Explicit byte integrity checks; Python optimization does not disable them."""
from pathlib import Path
import argparse
import hashlib
import json
import sys

def check(root: Path) -> int:
    manifest = json.loads((root / 'MANIFEST.json').read_text())
    for name, expected in manifest.items():
        rel = Path(name)
        if rel.is_absolute() or '..' in rel.parts:
            raise RuntimeError('Invalid manifest path: ' + name)
        path = root / rel
        if not path.is_file():
            raise RuntimeError('Missing manifest file: ' + name)
        if hashlib.sha256(path.read_bytes()).hexdigest() != expected:
            raise RuntimeError('SHA256 mismatch: ' + name)
    report = json.loads((root / 'evidence' / 'VERIFICATION.json').read_text())
    sources = {
        'GaussianPartition.lean', 'GaussianPrices.lean', 'GaussianNoTies.lean',
        'GaussianFullSupport.lean', 'GaussianBalancedPrices.lean',
        'GaussianWinningPartition.lean', 'GaussianUniquePrices.lean',
        'GaussianPrimalDual.lean', 'GaussianFractionalEquality.lean',
    }
    if set(report['source_sha256']) != sources:
        raise RuntimeError('Recorded proof-source inventory is not exactly nine modules.')
    for name in sources:
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != report['source_sha256'][name]:
            raise RuntimeError('Recorded source SHA256 mismatch: ' + name)
    roots = (root / 'ROOTS.txt').read_text().splitlines()
    if roots != report['roots'] or len(roots) != 50 or len(set(roots)) != 50 or report['root_count'] != 50:
        raise RuntimeError('Recorded root list is inconsistent.')
    closure = (root / 'evidence' / 'replayed-closure.txt').read_text().splitlines()
    if len(closure) != 52742 or len(set(closure)) != 52742 or closure != sorted(closure):
        raise RuntimeError('Recorded closure is not sorted and unique with 52742 declarations.')
    if not set(roots).issubset(closure) or report['closure_count'] != 52742:
        raise RuntimeError('Recorded closure does not contain every root.')
    axioms = (root / 'evidence' / 'replayed-axioms.txt').read_text().splitlines()
    if axioms != ['Classical.choice', 'Quot.sound', 'propext'] or axioms != report['axioms']:
        raise RuntimeError('Recorded axiom lists are inconsistent or contain unexpected axioms.')
    checker = json.loads((root / 'evidence' / 'VERIFICATION_CHECKER.json').read_text())
    if checker != report['checker']:
        raise RuntimeError('Recorded checker metadata is inconsistent.')
    if hashlib.sha256((root / 'Replay.lean').read_bytes()).hexdigest() != checker['augmented_replay_sha256']:
        raise RuntimeError('The recorded replay checker hash is inconsistent.')
    pins = json.loads((root / 'DEPENDENCY_PINS.json').read_text())
    if pins != report['package_pins'] or pins.get('mathlib') != 'd13f23b723b8a846827a245b89c10fc7d3f11612':
        raise RuntimeError('Recorded dependency pins are inconsistent.')
    expected = 'EMPTY_KERNEL_REPLAY_PASS 52742 declarations; 50 roots; trust level zero'
    if report['kernel_trust_level'] != 0 or expected not in (root / 'evidence' / 'logs' / 'Replay.log').read_text():
        raise RuntimeError('Recorded successful trust-zero replay evidence is missing.')
    preflight_path = root / 'evidence' / 'FINAL_PREFLIGHT.json'
    preflight = json.loads(preflight_path.read_text())
    runner_sha = hashlib.sha256((root / 'reproduce.py').read_bytes()).hexdigest()
    if preflight['runner_sha256'] != runner_sha:
        raise RuntimeError('Final preflight does not identify the actual final runner bytes.')
    actual_sources = {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
                      for name in sources | {'Replay.lean'}}
    if preflight['source_sha256'] != actual_sources or preflight['package_pins'] != pins:
        raise RuntimeError('Final preflight sources or dependency pins are inconsistent.')
    if preflight['lean_git_commit'] != '5045d0056413266e57c625dcd7c365b10e377c52':
        raise RuntimeError('Final preflight identifies the wrong Lean Git commit.')
    public = json.loads((root / 'evidence' / 'PUBLIC_REPRODUCTION.json').read_text())
    raw_path = root / 'evidence' / 'PUBLIC_REPRODUCTION_RAW.json'
    raw = json.loads(raw_path.read_text())
    if public['final_runner_sha256'] != runner_sha or public['final_preflight_sha256'] != hashlib.sha256(preflight_path.read_bytes()).hexdigest():
        raise RuntimeError('Public replay and final preflight metadata are inconsistent.')
    if public['raw_reproduction_record_sha256'] != hashlib.sha256(raw_path.read_bytes()).hexdigest():
        raise RuntimeError('Public replay raw-record hash is inconsistent.')
    for record in [public, raw]:
        if record['source_sha256'] != actual_sources or record['package_pins'] != pins or record['axioms'] != axioms:
            raise RuntimeError('Public replay source, dependency, or axiom record is inconsistent.')
        if record['root_count'] != 50 or record['closure_count'] != 52742 or record['kernel_trust_level'] != 0:
            raise RuntimeError('Public replay proof-closure scope is inconsistent.')
    if expected not in (root / 'evidence' / 'PUBLIC_REPLAY.log').read_text():
        raise RuntimeError('Public replay kernel PASS evidence is missing.')
    if 'REPRODUCTION_PASS' not in (root / 'evidence' / 'PUBLIC_REPRODUCTION.log').read_text():
        raise RuntimeError('Public runner PASS evidence is missing.')
    return len(manifest)

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--root', type=Path, default=Path(__file__).resolve().parent)
    args = parser.parse_args()
    try:
        print('INTEGRITY_PASS', check(args.root.resolve()), 'files')
    except (OSError, ValueError, KeyError, TypeError, RuntimeError) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(1)
