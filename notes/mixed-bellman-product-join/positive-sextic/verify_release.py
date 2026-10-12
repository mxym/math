#!/usr/bin/env python3
"""Integrity verification and isolated replay of the positive-sextic release.

Default: integrity only. --quick omits complete tail replay. --full reruns all
submitted and independent components normally and with optimization. Frozen
inputs stay untouched. No download, discovery search, or external mutation.
"""
from pathlib import Path, PurePosixPath
from fractions import Fraction
import argparse, hashlib, json, os, shutil, subprocess, sys, time, zipfile

ROOT = Path(__file__).resolve().parent
ARCHIVE = 'certificates-and-independent-audit.zip'
ARCHIVE_SHA = 'b069821e04e84b4d55c97bafd0820969bacedae0dcc84652f6f3075e4af1b533'
ORIGINAL_ARCHIVE_SHA = 'a8a6a21ec3d512b2d2bcb60eca8b8c9f9cc780267324680b5ceafde7eb18c112'
CANDIDATE = 'nonquartic_envelope_20261007'
AUDIT = 'sextic_bellman_independent_audit_20261007'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def digest(data):
    return hashlib.sha256(data).hexdigest()

def integrity():
    manifest = json.loads((ROOT/'MANIFEST.json').read_text())
    require(manifest['schema'] == 'positive-sextic-reader-release-1', 'release schema')
    records = manifest['files']
    require(len({r['path'] for r in records}) == len(records), 'duplicate manifest path')
    for record in records:
        p = PurePosixPath(record['path'])
        require(not p.is_absolute() and '..' not in p.parts, 'unsafe manifest path')
        raw = (ROOT/str(p)).read_bytes()
        require(len(raw) == record['bytes'] and digest(raw) == record['sha256'], 'release hash mismatch: '+str(p))
    raw_archive = (ROOT/ARCHIVE).read_bytes()
    require(digest(raw_archive) == ARCHIVE_SHA, 'corrected public archive hash mismatch')
    with zipfile.ZipFile(ROOT/ARCHIVE) as z:
        entries = z.infolist()
        names = [entry.filename for entry in entries]
        require(len(set(names)) == len(names), 'duplicate archive path')
        for entry in entries:
            p = PurePosixPath(entry.filename)
            require(not p.is_absolute() and '..' not in p.parts and p.parts[0] in (CANDIDATE,AUDIT), 'unsafe archive path')
            require((entry.external_attr >> 16) & 0o170000 != 0o120000, 'archive symlink')
        inventory = json.loads((ROOT/'ARCHIVE_INVENTORY.json').read_text())
        require(inventory['schema'] == 'positive-sextic-complete-archive-inventory-1', 'archive inventory schema')
        require(inventory['archive_sha256'] == ARCHIVE_SHA and inventory['original_supplied_archive_sha256'] == ORIGINAL_ARCHIVE_SHA, 'archive provenance pins')
        records = inventory['entries']
        require(len(records) == 145 and len(names) == 145 and {r['path'] for r in records} == set(names), 'complete archive inventory coverage')
        require(len({r['path'] for r in records}) == 145, 'duplicate archive inventory path')
        for record in records:
            raw = z.read(record['path'])
            require(len(raw) == record['bytes'] and digest(raw) == record['sha256'], 'complete inventory mismatch: '+record['path'])
        additions = {r['path']:r for r in inventory['exact_added_files']}
        expected_additions = {
          CANDIDATE+'/source/notes/mixed-bellman-product-join/obstruction/MANIFEST.json': (2310,'a62e4d76d6c9eb7bba53d1f2f897231599d0af9aea273f296feb02dfc0022248'),
          CANDIDATE+'/source/notes/mixed-bellman-product-join/sharpened/MANIFEST.json': (7091,'dd6184d75d418e931f1574b5acb3c2b282fdc2266446883e760bbae5d1fe3556'),
        }
        require(set(additions) == set(expected_additions), 'exact archive additions')
        for name,(size,sha) in expected_additions.items():
            raw = z.read(name)
            require(len(raw) == size and digest(raw) == sha, 'recovered manifest pin: '+name)
        ancestor = json.loads(z.read(CANDIDATE+'/SOURCE_INTEGRITY.json'))
        require(ancestor['files'] == 63 and len(ancestor['entries']) == 63, 'ancestor integrity record')
        require(len([name for name in names if name.startswith(CANDIDATE+'/source/')]) == 63, 'complete ancestor-source count')
        for record in ancestor['entries']:
            raw = z.read(CANDIDATE+'/'+record['path'])
            require(len(raw) == record['bytes'] and digest(raw) == record['sha256'], 'ancestor-source integrity: '+record['path'])
        for directory in (CANDIDATE,AUDIT):
            m = json.loads(z.read(directory+'/MANIFEST.json'))
            for record in m['files']:
                raw = z.read(directory+'/'+record['path'])
                require(len(raw) == record['bytes'] and digest(raw) == record['sha256'], 'archived manifest mismatch: '+record['path'])
        points = json.loads(z.read(CANDIDATE+'/sextic_finite_points.json'))
        tails = json.loads(z.read(CANDIDATE+'/sextic_tail_certificate.json'))
        require(points['coefficients'] == [[431,10000],[9,2500],[197,100000]] and points['T'] == [4867,100000], 'finite parameters')
        require(len(points['points']) == 19900, 'finite count')
        require((tails['alpha'],tails['beta'],tails['gamma']) == ('431/10000','9/2500','197/100000'), 'tail parameters')
        require(tails['cutoff'] == 200 and tails['point_denominator'] == 10**8, 'tail scales')
        require(len(tails['cells']) == 157872 and max(r[2] for r in tails['cells']) == 11, 'tail count/depth')
        ranges = {r: [] for r in range(1,200)}
        for row in tails['cells']:
            require(type(row) is list and len(row) == 5 and all(type(v) is int for v in row), 'tail row shape')
            r,i,d,h,u = row
            require(r in ranges and 0 <= d <= 11 and 0 <= i < 2**d, 'tail cell coordinates')
            require(2 <= Fraction(h,10**8) <= r+1 and 0 <= Fraction(u,10**8) <= 1, 'tail membership')
            # Integer grid at maximum dyadic depth independently checks coverage.
            ranges[r].append((i*2**(11-d),(i+1)*2**(11-d)))
        for r,cells in ranges.items():
            cursor = 0
            for a,b in sorted(cells):
                require(a == cursor, 'tail coverage gap/overlap in r='+str(r))
                cursor = b
            require(cursor == 2**11, 'tail coverage endpoint')
        signoff = json.loads(z.read(AUDIT+'/SIGNOFF.json'))
        require(signoff['status'] == 'PASS' and signoff['mathematical_corrections_required'] == [], 'archived audit status')
        require(signoff['finite_rectangles'] == 19900 and signoff['tail_cells'] == 157872 and signoff['corrupt_fixture_rejections'] == 28, 'audit counts')
    return {'status':'PASS: frozen release integrity and integer coverage',
            'release_files':len(manifest['files']), 'archived_files':len(entries),
            'complete_ancestor_source_files':63, 'original_archive_entries':143, 'added_ancestor_manifests':2,
            'finite_rectangles':19900, 'tail_cells':157872, 'maximum_tail_depth':11,
            'archive_sha256':ARCHIVE_SHA, 'original_supplied_archive_sha256':ORIGINAL_ARCHIVE_SHA,
            'fresh_full_arithmetic_replay':False}

def normalized(data):
    if isinstance(data,dict):
        return {k:normalized(v) for k,v in data.items() if k != 'elapsed_seconds'}
    if isinstance(data,list):
        return [normalized(v) for v in data]
    return data

def replay(output, full):
    output = output.resolve()
    require(output != ROOT and ROOT not in output.parents, 'replay output must be outside the frozen release directory')
    require(not output.exists() or not any(output.iterdir()), 'replay output must be absent or empty')
    output.mkdir(parents=True,exist_ok=True)
    extracted = output/'extracted'
    extracted.mkdir()
    with zipfile.ZipFile(ROOT/ARCHIVE) as z:
        z.extractall(extracted) # All names and symlink flags were validated above.
    source = extracted/CANDIDATE
    audit = extracted/AUDIT
    # The inherited lower input is a separate byte-preserved pinned dependency.
    lower = output/'dependencies/v2'
    shutil.copytree(ROOT/'dependencies/v2',lower)
    env = dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
    records = []
    for optimized in (False,True):
        mode = 'optimized' if optimized else 'normal'
        destination = output/mode
        destination.mkdir()
        flags = ['-O'] if optimized else []
        commands = [
          ('submitted_finite',[str(source/'check_sextic_finite.py'),str(source/'sextic_finite_points.json'),'--report',str(destination/'submitted_finite.json'),'--quiet']),
          ('submitted_large',[str(source/'check_sextic_large.py'),'--output',str(destination/'submitted_large.json')]),
          ('sextic_necessity',[str(source/'check_negative_controls.py')]),
          ('independent_finite',[str(audit/'independent_check.py'),'finite','--output',str(destination/'independent_finite.json')]),
          ('independent_large',[str(audit/'independent_check.py'),'large','--output',str(destination/'independent_large.json')]),
          ('symbolic',[str(audit/'independent_check.py'),'symbolic','--output',str(destination/'symbolic.json')]),
          ('adversarial',[str(audit/'adversarial_tests.py'),'--output',str(destination/'adversarial.json')]),
          ('inherited_lower',[str(lower/'code/check.py'),str(lower/'certificates/exact.json'),'--report',str(destination/'inherited_lower.json'),'--self-test']),
        ]
        if full:
            commands.extend([
              ('submitted_tail',[str(source/'check_sextic_tail.py')]),
              ('independent_tail',[str(audit/'independent_check.py'),'tail','--output',str(destination/'independent_tail.json')]),
            ])
        for name,args in commands:
            print(mode+': '+name,flush=True)
            start = time.monotonic()
            log = destination/(name+'.log')
            with log.open('w') as stream:
                run = subprocess.run([sys.executable,*flags,*args],cwd=source,env=env,stdout=stream,stderr=subprocess.STDOUT)
            require(run.returncode == 0, 'replay failed: '+mode+'/'+name+'; see '+str(log))
            if name in ('submitted_tail','sextic_necessity'):
                (destination/(name+'.json')).write_text(log.read_text())
            records.append({'mode':mode,'component':name,'status':'PASS','elapsed_seconds':round(time.monotonic()-start,3)})
    for p in (output/'normal').glob('*.json'):
        other = output/'optimized'/p.name
        require(other.exists() and normalized(json.loads(p.read_text())) == normalized(json.loads(other.read_text())), 'normal/-O report mismatch: '+p.name)
    corruption = json.loads((output/'normal/adversarial.json').read_text())
    require(len(corruption['corrupted_fixtures_rejected']) == 28, 'corruption rejection total')
    # Confirm every frozen mathematical source and certificate stayed unchanged.
    with zipfile.ZipFile(ROOT/ARCHIVE) as z:
        for entry in z.infolist():
            if entry.is_dir():
                continue
            if entry.filename.endswith(('.py','.md','.tex')) or 'certificate' in entry.filename or 'points' in entry.filename:
                require((extracted/entry.filename).read_bytes() == z.read(entry.filename), 'replay changed a frozen input: '+entry.filename)
    return {'status':'PASS: full fresh replay' if full else 'PASS: quick replay; full tails not rerun',
            'fresh_full_arithmetic_replay':full, 'normal_optimized_reports_match':True,
            'corrupt_cases_rejected':28,'components':records}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('--quick',action='store_true')
    group.add_argument('--full',action='store_true')
    parser.add_argument('--output',type=Path,help='fresh replay directory outside this release; required with --quick/--full')
    args = parser.parse_args()
    result = {'integrity':integrity()}
    if args.quick or args.full:
        require(args.output is not None, '--output is required for isolated replay')
        result['replay'] = replay(args.output,args.full)
        (args.output/'release_replay.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__ == '__main__':
    main()
