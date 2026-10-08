"""Check logs produced by verify.sh; never label this independent kernel replay."""
import hashlib
import json
import re
import sys
from pathlib import Path
from check_sources import ROOT, MODULES, check, require


def audit(run):
    names = check()
    require((run / 'completed-modules.txt').read_text().splitlines() == MODULES,
            'Incomplete fresh compilation')
    for module in MODULES:
        path = run / 'olean' / (module + '.olean')
        require(path.is_file() and path.stat().st_size > 0,
                'Missing compiled module: ' + module)
    pins = (run / 'pins.log').read_text().splitlines()
    require(len(pins) == 2 and re.search(r'version 4\.34\.1([, ]|$)', pins[0]),
            'Unexpected Lean version')
    require(pins[1] == 'd13f23b723b8a846827a245b89c10fc7d3f11612',
            'Unexpected Mathlib commit')
    for filename in ('cleancompile.log', 'finaltheorem-signatures-and-axioms.log',
                     'basic-properties-audit.log', 'prime-exclusion-audit.log'):
        text = (run / filename).read_text()
        require('error:' not in text and 'sorryAx' not in text,
                'Error or sorry axiom in ' + filename)
    log = (run / 'finaltheorem-signatures-and-axioms.log').read_text()
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", log)
    reports += [(name, '') for name in re.findall(
        r"'([^']+)' does not depend on any axioms", log)]
    require(len(reports) == len(names) and {n for n, _ in reports} == set(names),
            'Missing, duplicate, or unexpected axiom reports')
    allowed = {'propext', 'Classical.choice', 'Quot.sound'}
    for name, axioms in reports:
        require({a.strip() for a in axioms.split(',') if a.strip()} <= allowed,
                'Unexpected axiom for ' + name)
    report = {
        'status': 'fresh_directory_compilation_and_axiom_audit_passed',
        'lean_version_output': pins[0], 'mathlib_commit': pins[1],
        'source_modules': MODULES, 'audited_declarations': len(names),
        'allowed_axioms': sorted(allowed),
        'independent_empty_kernel_verification': 'pending',
        'independent_semantic_review': 'pending',
        'dependency_binary_authentication': 'not_performed_by_this_script',
        'lean_source_sha256': {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                               for p in sorted(ROOT.glob('*.lean'))}}
    (run / 'VERIFICATION_REPLAY.json').write_text(json.dumps(report, indent=2) + '\n')
    (run / 'axiom-audit.json').write_text(json.dumps(dict(reports), indent=2) + '\n')
    print('PASS: fresh-directory compilation and 73 declaration axiom reports.')
    print('Independent empty-kernel verification and semantic review remain pending.')
    print('Report: ' + str(run / 'VERIFICATION_REPLAY.json'))


if __name__ == '__main__':
    require(len(sys.argv) == 2, 'Usage: python3 audit_sources.py RUN_DIRECTORY')
    audit(Path(sys.argv[1]).resolve())
