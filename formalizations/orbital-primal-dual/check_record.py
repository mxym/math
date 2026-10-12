#!/usr/bin/env python3
"""Recorded-evidence integrity only; use replay.py for independent proof checking."""
from hashlib import sha256
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    record = HERE / 'verification'
    report = json.loads((record / 'report.json').read_text())
    need(report['status'] == 'PASS', 'Report did not pass.')
    modules = json.loads((HERE / 'MODULES.json').read_text())
    need(len(modules) == len(set(modules)), 'Duplicate module.')
    roots = []
    imports, bodies = [], []
    for module in modules:
        source = HERE / (module + '.lean')
        data = source.read_text()
        roots.extend('OrbitalMarginals.' + name for name in
                     re.findall(r'^theorem\s+([A-Za-z0-9_]+)', data, flags=re.M))
        body = []
        for line in data.splitlines():
            match = re.fullmatch(r'import (\S+)', line)
            if match:
                if match[1] not in modules and match[1] not in imports:
                    imports.append(match[1])
            else:
                body.append(line)
        bodies.append('-- Source: ' + source.name + '\n' + '\n'.join(body))
    bundle = '\n'.join('import ' + name for name in imports) + '\n\n' + '\n\n'.join(bodies) + '\n'
    need(bundle.encode() == (record / 'ProofBundle.lean').read_bytes(),
         'Recorded compilation bundle does not match the owned source.')
    need(roots == report['roots'] and len(roots) == report['positive_theorems'], 'Theorem inventory mismatch.')
    need(set(report['owned_source_sha256']) == {module + '.lean' for module in modules} | {'FalseJordan.lean'},
         'Source hash coverage mismatch.')
    for name, expected in report['owned_source_sha256'].items():
        need(digest(HERE / name) == expected, 'Owned source changed: ' + name)
    need(digest(HERE / 'replay.py') == report['replay_driver_sha256'], 'Replay driver changed.')
    need(digest(HERE / 'ReplayTemplate.lean') == report['replay_template_sha256'], 'Replay template changed.')
    for field in ['generated_source_sha256', 'log_sha256']:
        for name, expected in report[field].items():
            need(digest(record / name) == expected, 'Recorded payload changed: ' + name)
    manifest = json.loads((HERE / 'lake-manifest.json').read_text())
    need({p['name']: p['rev'] for p in manifest['packages']} == report['package_revisions'], 'Pins changed.')
    need(set(report['allowed_axioms']) == {'propext', 'Classical.choice', 'Quot.sound'}, 'Unexpected axiom policy.')
    need(report['negative_controls_rejected'] == 1 and report['positive_controls'] == 3, 'Control count mismatch.')
    print(json.dumps({'status': 'PASS', 'scope': 'integrity of recorded evidence; not a new Lean replay',
                      'positive_theorems': len(roots),
                      'empty_kernel_declarations': report['empty_kernel_declarations']}, indent=2))


if __name__ == '__main__':
    main()
