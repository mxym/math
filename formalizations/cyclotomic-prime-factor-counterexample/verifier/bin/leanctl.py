#!/usr/bin/env python3
"""Single local entry point: doctor | status | smoke | verify CONFIG.json.
No downloads, installation, dependency builds, or repository mutations.
"""
import argparse
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import uuid

BASE = Path(__file__).resolve().parents[1]
CONFIG = BASE / 'config/environment.json'
NAME = re.compile(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*")

def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()

def digest(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for chunk in iter(lambda: f.read(1 << 20), b''):
            h.update(chunk)
    return h.hexdigest()

def save(path, data):
    Path(path).write_text(json.dumps(data, indent=2, ensure_ascii=False) + '\n')

def output(args):
    return subprocess.check_output(args, text=True, stderr=subprocess.STDOUT).strip()

def shared_metadata(root):
    """Detect changes during a verification without modifying shared artifacts."""
    h = hashlib.sha256()
    for directory, dirs, files in os.walk(root):
        dirs[:] = sorted(d for d in dirs if d != '.git')
        for name in sorted(files):
            p = Path(directory) / name
            s = p.stat()
            h.update(f'{p.relative_to(root)}\0{s.st_size}\0{s.st_mtime_ns}\n'.encode())
    return h.hexdigest()

def doctor():
    c = json.loads(CONFIG.read_text())
    lean = Path(c['toolchain_path']) / 'bin/lean'
    if not lean.is_file():
        raise RuntimeError('PINNED_TOOLCHAIN_MISSING: consult RECOVERY.txt; do not reinstall blindly')
    actual = output([str(lean), '--githash'])
    if actual != c['lean_commit']:
        raise RuntimeError('LEAN_COMMIT_MISMATCH')
    packages = []
    for pkg in c['packages']:
        p = Path(c['packages_root']) / pkg['name']
        rev = output(['git', '-C', str(p), 'rev-parse', 'HEAD'])
        dirty = output(['git', '-C', str(p), 'status', '--porcelain=v1', '-uno'])
        if rev != pkg['rev'] or dirty:
            raise RuntimeError(f'PINNED_PACKAGE_MISMATCH {pkg["name"]}: {rev}, {dirty}')
        packages.append({'name': pkg['name'], 'path': str(p), 'commit': rev})
    free = shutil.disk_usage(BASE).free
    return {'time_utc': now(), 'status': 'READY', 'root': str(BASE),
            'lean_version': output([str(lean), '--version']),
            'lean_commit': actual, 'lean_binary_sha256': digest(lean),
            'lean_runtime_sha256': digest(Path(c['toolchain_path']) / 'lib/lean/libleanshared.so'),
            'packages': packages, 'free_bytes': free,
            'can_start_new_run': free >= c['min_free_bytes'],
            'shared_cache_policy': c['read_only_use']}

def scrub_comments_strings(text):
    """Conservative lexical check only; kernel dependency audit remains authoritative."""
    result = []; i = 0; block = 0; string = False
    while i < len(text):
        pair = text[i:i+2]; ch = text[i]
        if block:
            if pair == '/-': block += 1; result.extend('  '); i += 2; continue
            if pair == '-/': block -= 1; result.extend('  '); i += 2; continue
            result.append('\n' if ch == '\n' else ' '); i += 1; continue
        if string:
            if ch == '\\': result.extend('  '); i += 2; continue
            if ch == '"': string = False
            result.append('\n' if ch == '\n' else ' '); i += 1; continue
        if pair == '/-': block = 1; result.extend('  '); i += 2; continue
        if pair == '--':
            end = text.find('\n', i)
            if end < 0: end = len(text)
            result.extend(' ' * (end-i)); i = end; continue
        if ch == '"': string = True; result.append(' '); i += 1; continue
        result.append(ch); i += 1
    return ''.join(result)

def verify(case_path):
    c = json.loads(CONFIG.read_text())
    case = json.loads(Path(case_path).read_text())
    task = case['task']
    if not re.fullmatch(r'[a-z0-9][a-z0-9_-]{0,79}', task):
        raise ValueError('Invalid task identifier')
    modules = case['modules']; order = case['module_order']
    audited = case.get('audit_modules', list(modules)); roots = case['roots']
    if not modules or set(order) != set(modules) or len(order) != len(modules):
        raise ValueError('module_order must list every source module exactly once in import order')
    if not audited or not set(audited) <= set(modules) or not roots:
        raise ValueError('Invalid audit module/root list')
    if not all(NAME.fullmatch(x) for x in list(modules)+roots):
        raise ValueError('Use explicit simple Lean names')
    source_root = Path(case['source_dir']).resolve(strict=True)
    snapshots = {}; supplied_paths = set()
    for module, info in modules.items():
        p = (source_root / info['path']).resolve(strict=True)
        if not p.is_relative_to(source_root) or p.suffix != '.lean':
            raise ValueError('Source path outside source directory')
        if digest(p) != info['sha256']:
            raise ValueError('SOURCE_HASH_MISMATCH ' + module)
        supplied_paths.add(p); snapshots[module] = p.read_bytes()
    actual_paths = {p.resolve() for p in source_root.rglob('*.lean') if '.lake' not in p.parts}
    if actual_paths != supplied_paths:
        raise ValueError('UNLISTED_OR_DUPLICATE_SOURCE: use a complete reviewed source directory')
    with (BASE / 'locks/verifier.lock').open('a') as lock:
        try: fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError: raise RuntimeError('VERIFIER_BUSY; keep tasks serial')
        health = doctor()
        if not health['can_start_new_run']:
            raise RuntimeError('LOW_DISK; preserve all research data and report before cleanup')
        rid = dt.datetime.now(dt.timezone.utc).strftime('%Y%m%dT%H%M%SZ')+'-'+uuid.uuid4().hex[:8]
        run = BASE / 'tasks' / task / rid
        for name in ['sources', 'build', 'logs', 'manifest', 'checks', 'tmp']:
            (run / name).mkdir(parents=True, exist_ok=False)
        save(run/'manifest/input.json', case)
        save(run/'manifest/environment.json', health)
        save(run/'manifest/environment-config.json', c)
        save(run/'manifest/control-source-sha256.json', {
            str(p.relative_to(BASE)): digest(p) for p in
            [Path(__file__), BASE/'checks/OwnedAudit.template.lean', BASE/'checks/RejectInvalidProof.lean']})
        state = {'status': 'RUNNING', 'pid': os.getpid(), 'task': task, 'run': str(run),
                 'started_utc': now(), 'stage': 'snapshot', 'author_claim_verified': False}
        state_path = run/'manifest/status.json'
        save(state_path, state)
        print(str(run), flush=True)
        records = []
        shared_before = shared_metadata(Path(c['packages_root']))
        for module, data in snapshots.items():
            p = run/'sources'/Path(*module.split('.')).with_suffix('.lean')
            p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(data)
        env = os.environ.copy()
        for key in ['LEAN_PATH', 'LEAN_SRC_PATH']: env.pop(key, None)
        libs = [str(run/'build')]
        libs += [str(Path(c['packages_root'])/p['name']/'.lake/build/lib/lean') for p in c['packages']]
        libs += [str(Path(c['toolchain_path'])/'lib/lean')]
        env['LEAN_PATH'] = os.pathsep.join(libs)
        env['TMPDIR'] = str(run/'tmp')
        env['INDEPENDENT_AUDIT_OUTPUT'] = str(run/'manifest')
        lean = str(Path(c['toolchain_path'])/'bin/lean')
        common = [lean, '-j'+str(c['threads']), '-M'+str(c['memory_limit_mb'])]
        save(run/'manifest/search-path.json', libs)
        def command(args, log, stage):
            state.update(stage=stage, updated_utc=now()); save(state_path, state)
            print(stage, flush=True)
            started = now()
            with (run/'logs'/log).open('w') as f:
                r = subprocess.run(args, cwd=run/'sources', env=env, stdout=f,
                                   stderr=subprocess.STDOUT, timeout=c['step_timeout_seconds'])
            records.append({'argv':args,'log':log,'started_utc':started,'ended_utc':now(),'exit_code':r.returncode})
            save(run/'manifest/commands.json',records)
            if r.returncode: raise RuntimeError(f'{stage} failed; see logs/{log}')
        try:
            scan = []
            for module in audited:
                cleaned = scrub_comments_strings(snapshots[module].decode('utf-8'))
                for m in re.finditer(r'\b(?:sorry|admit|axiom|unsafe|native_decide)\b', cleaned):
                    scan.append({'module':module,'line':cleaned.count('\n',0,m.start())+1,'token':m.group()})
            save(run/'manifest/source-token-scan.json',scan)
            if scan: raise RuntimeError('PROHIBITED_SOURCE_TOKEN_REQUIRES_REVIEW')
            for i,module in enumerate(order):
                rel=Path(*module.split('.'))
                src=(run/'sources'/rel).with_suffix('.lean')
                out=(run/'build'/rel).with_suffix('.olean')
                out.parent.mkdir(parents=True,exist_ok=True)
                command(common+['-R',str(run/'sources'),'-o',str(out),'-i',str(out.with_suffix('.ilean')),str(src)],
                        f'{i:03d}-{module}.compile.log','compile '+module)
                command([lean,'--deps',str(src)],f'{i:03d}-{module}.dependencies.log','dependencies '+module)
            template=(BASE/'checks/OwnedAudit.template.lean').read_text()
            audit=template.replace('@@IMPORTS@@','\n'.join('import '+m for m in audited))
            audit=audit.replace('@@MODULES@@','#[ '+', '.join(json.dumps(m) for m in audited)+' ]')
            audit=audit.replace('@@ROOTS@@','#[ '+', '.join('``'+r for r in roots)+' ]')
            (run/'checks/OwnedAudit.lean').write_text(audit)
            command(common+[str(run/'checks/OwnedAudit.lean')], 'owned-audit-replay.log','all-owned audit and empty trust-zero replay')
            negative=run/'checks/RejectInvalidProof.lean'
            negative.write_bytes((BASE/'checks/RejectInvalidProof.lean').read_bytes())
            command([lean,str(negative)],'negative-kernel.log','invalid-proof rejection')
            for module,data in snapshots.items():
                p=(run/'sources'/Path(*module.split('.'))).with_suffix('.lean')
                if p.read_bytes()!=data: raise RuntimeError('SOURCE_CHANGED_DURING_RUN')
            shared_after=shared_metadata(Path(c['packages_root']))
            save(run/'manifest/shared-cache-check.json',{'before':shared_before,'after':shared_after,'unchanged':shared_before==shared_after})
            if shared_before!=shared_after: raise RuntimeError('SHARED_CACHE_CHANGED_DURING_RUN')
            state.update(status='MECHANICAL_PASS', stage='complete', ended_utc=now(),
                         semantic_review='REQUIRED_SEPARATELY',
                         excluded_from_declaration_audit=sorted(set(modules)-set(audited)))
        except Exception as e:
            state.update(status='FAILED',error=str(e),ended_utc=now())
            raise
        finally:
            save(state_path,state)
            files=sorted(p for p in run.rglob('*') if p.is_file() and p.name!='SHA256SUMS')
            (run/'manifest/SHA256SUMS').write_text(''.join(digest(p)+'  '+str(p.relative_to(run))+'\n' for p in files))
        print('MECHANICAL_PASS; semantic correspondence review is separate',flush=True)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('action',choices=['doctor','status','smoke','verify'])
    ap.add_argument('case',nargs='?')
    args=ap.parse_args()
    if args.action=='doctor': print(json.dumps(doctor(),indent=2))
    elif args.action=='status':
        states=[json.loads(p.read_text()) for p in (BASE/'tasks').glob('*/*/manifest/status.json')]
        print(json.dumps(states,indent=2))
    elif args.action=='smoke': verify(BASE/'config/smoke.json')
    elif not args.case: ap.error('verify requires CONFIG.json')
    else: verify(args.case)

if __name__=='__main__':
    main()
