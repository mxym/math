"""Read-only local v3 receipt verification; never invokes Lean or kernel."""
from pathlib import Path
import argparse, sys

SEAL = Path(__file__).resolve().parent
sys.path.insert(0, str(SEAL.parents[1]))
import common as c
import evidence


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--artifact', type=Path)
    parser.add_argument('--check-owned-cache', action='store_true')
    args = parser.parse_args()
    files = {p.relative_to(SEAL).as_posix(): c.sha(p)
             for p in sorted(SEAL.rglob('*'))
             if p.is_file() and p != SEAL / 'SEALED_FILES.json'}
    if files != c.readj(SEAL / 'SEALED_FILES.json'):
        raise ValueError('Sealed snapshot changed')
    report = c.readj(SEAL / 'REPORT.json')
    snapshot = SEAL / 'snapshot'
    raw_manifest = c.readj(snapshot / 'EVIDENCE_HASHES.json')
    if set(report['snapshot_omissions']) != {'native/audit-driver'}:
        raise ValueError('Changed artifact omission boundary')
    expected = {n: h for n, h in raw_manifest.items() if n != 'native/audit-driver'}
    if c.file_manifest(snapshot) != expected:
        raise ValueError('Snapshot differs from original raw artifact manifest')
    if c.sha(snapshot / 'EVIDENCE_HASHES.json') != report['raw_evidence_manifest_sha256']:
        raise ValueError('Original raw artifact manifest changed')
    c.binding()
    for name in list(c.readj(c.ROOT / 'SOURCE_HASHES.json')) + [c.PREFIX + '/SOURCE_HASHES.json', c.PREFIX + '/BINDING.json']:
        if c.path_at(c.REPO, name).read_bytes() != c.git('show', report['recipe_commit'] + ':' + name):
            raise ValueError('Recipe Git object differs: ' + name)
    artifact = args.artifact if args.artifact is not None else Path(report['raw_evidence_directory'])
    if c.sha(artifact / 'EVIDENCE_HASHES.json') != report['raw_evidence_manifest_sha256']:
        raise ValueError('Wrong complete artifact')
    result = evidence.verify(artifact)
    checked_cache = 0
    if args.check_owned_cache:
        original_repo = Path(report['raw_evidence_directory']).parents[3]
        old = c.readj(snapshot / 'PRE_AUDIT.json')['reused_r2_oleans']
        if type(old) is not dict or len(old) != 430:
            raise ValueError('Wrong independent fresh cache receipt')
        for name, sha in old.items():
            if c.sha(c.path_at(original_repo, name)) != sha:
                raise ValueError('Independent r2 cache drift: ' + name)
        checked_cache = len(old)
    print({'status': 'LOCAL_V3_SEAL_RECHECK_PASS', 'full_artifact': result,
           'checked_owned_cache': checked_cache, 'lean_started': False,
           'kernel_started': False})


if __name__ == '__main__':
    main()
