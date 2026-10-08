"""Verify published bytes and simple source guards; this is not kernel checking."""
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
MODULES = ['CoefficientList', 'CyclotomicFormulas', 'PrimeExclusion',
           'BasicProperties', 'Expansion', 'DataProperties', 'Counterexample',
           'CenteredCertificate']


def require(ok, message):
    if not ok:
        raise SystemExit('FAIL: ' + message)


def check():
    package = json.loads((ROOT / 'PACKAGE_MANIFEST.json').read_text())
    recovery = json.loads((ROOT / 'RECOVERY_MANIFEST.json').read_text())
    for name, entry in package['files'].items():
        require(Path(name).name == name, 'Nonlocal manifest filename: ' + name)
        data = (ROOT / name).read_bytes()
        require(len(data) == entry['bytes'], 'Size mismatch: ' + name)
        require(hashlib.sha256(data).hexdigest() == entry['sha256'],
                'Package hash mismatch: ' + name)
    expected = {m + '.lean' for m in MODULES} | {
        'Audit.lean', 'BasicPropertiesAudit.lean', 'PrimeExclusionAudit.lean'}
    require(set(recovery['files']) == expected, 'Unexpected recovery source inventory')
    require({p.name for p in ROOT.glob('*.lean')} == expected,
            'Unexpected Lean source inventory')
    for name, entry in recovery['files'].items():
        data = (ROOT / name).read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        require(digest == entry['original_pre_reset_sha256'] == entry['recovered_sha256'],
                'Recovery hash mismatch: ' + name)
        require(len(data) == entry['bytes'], 'Recovery size mismatch: ' + name)
        text = re.sub(r'/\-.*?\-/', '', data.decode(), flags=re.S)
        text = re.sub(r'--[^\n]*', '', text)
        require(not re.search(r'\b(sorry|axiom|native_decide|unsafe|admit)\b', text),
                'Forbidden source token: ' + name)
    names = (ROOT / 'theorem_names.txt').read_text().splitlines()
    declared = []
    for module in MODULES:
        declared += ['CyclotomicCounterexample.' + name for name in re.findall(
            r'^(?:noncomputable )?(?:def|theorem) (\w+)',
            (ROOT / (module + '.lean')).read_text(), re.M)]
    require(names == declared and len(names) == len(set(names)) == 73,
            'Declaration inventory mismatch')
    audit = (ROOT / 'Audit.lean').read_text()
    require(re.findall(r'^#check (\S+)$', audit, re.M) == names,
            'Signature audit inventory mismatch')
    require(re.findall(r'^#print axioms (\S+)$', audit, re.M) == names,
            'Axiom audit inventory mismatch')
    return names


if __name__ == '__main__':
    check()
    print('PASS: package hashes, 11 recovered sources, and 73 audit declarations.')
    print('Independent compilation and empty-kernel verification remain pending.')
