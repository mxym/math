#!/usr/bin/env python3
"""Separate combined scope. Rebuild new owned libraries; replay at kernel trust zero."""
from pathlib import Path
import argparse, datetime, hashlib, json, os, re, shutil, signal, subprocess, time

ROOT = Path(__file__).resolve().parent
REPO = ROOT.parent.parent
PIN = 'd13f23b723b8a846827a245b89c10fc7d3f11612'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
NEW_PACKAGES = [
    'extraction-matrix-projector', 'extraction-symmetric-support',
    'extraction-symmetric-support/general-rank-foundation',
    'extraction-information-spectrum', 'extraction-spectral-protocol',
    'extraction-universal-orbit', 'extraction-minimax-profile', 'extraction-connections']
ALL_PACKAGES = NEW_PACKAGES + ['spectral-extraction-core', 'spectral-extraction-local-cap',
    'appt-qutrit-purity', 'appt-high-dimensional-review']

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def without_comments(txt):
    out, depth, i = [], 0, 0
    while i < len(txt):
        if txt[i:i+2] == '/-': depth += 1; i += 2
        elif depth and txt[i:i+2] == '-/': depth -= 1; i += 2
        elif depth:
            if txt[i] == '\n': out.append('\n')
            i += 1
        elif txt[i:i+2] == '--':
            end = txt.find('\n', i)
            i = len(txt) if end < 0 else end
        else: out.append(txt[i]); i += 1
    if depth: raise RuntimeError('Unclosed Lean comment')
    return ''.join(out)

def math_files():
    groups = json.loads((ROOT/'ROOT_GROUPS.json').read_text())
    return [(REPO/n, g['namespace']) for g in groups for n in g['files']]

def math_roots():
    result = []
    for p, ns in math_files():
        result += [ns+'.'+n for n in re.findall(r'^theorem\s+([^\s(:]+)',
            without_comments(p.read_text()), flags=re.M)]
    return result

def inventory():
    own = ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json', '.gitignore',
        'Connections.lean', 'ConnectionsVerification.lean',
        'ConnectionsVerification/ReplaySupport.lean', 'reproduce.py', 'README.md',
        'REVIEW.md', 'ROOTS.txt', 'ROOT_GROUPS.json', 'CONTROLS.txt',
        'FROZEN_OLD_INPUTS.json', 'STANDARD_CACHE.json', 'Audit.lean', 'Check.lean']
    selected = {ROOT/n for n in own} | {p for p,_ in math_files()}
    pending = [p for p in selected if p.suffix == '.lean']
    seen = set()
    while pending:
        p = pending.pop()
        if p in seen: continue
        seen.add(p)
        for raw in re.findall(r'^import\s+([^\n]+)', without_comments(p.read_text()), flags=re.M):
            for mod in raw.split():
                if mod.startswith(('Mathlib.', 'Lean.')) or mod == 'Lean': continue
                found = [ROOT.parent/pkg/(mod.replace('.','/')+'.lean') for pkg in ALL_PACKAGES]
                found = [f for f in found if f.is_file()]
                if len(found) != 1: raise RuntimeError('Missing/nonunique local import '+mod)
                f = found[0]
                if f not in selected: selected.add(f); pending.append(f)
    for pkg in ALL_PACKAGES:
        for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']:
            p = ROOT.parent/pkg/name
            if p.is_file(): selected.add(p)
    for pkg in NEW_PACKAGES[:-1]:
        for name in ['README.md', 'ROOTS.txt']:
            p = ROOT.parent/pkg/name
            if p.is_file(): selected.add(p)
    return {p.relative_to(REPO).as_posix():sha(p) for p in sorted(selected)}

def check_standard_cache():
    lib = ROOT/'.lake/packages/mathlib'
    expected = json.loads((ROOT/'STANDARD_CACHE.json').read_text())
    for name, digest in expected.items():
        p = lib/'.lake/build'/name
        if p.exists() and sha(p) != digest:
            raise RuntimeError('Nonstandard Multinomial cache artifact: '+name)

def check():
    if inventory() != json.loads((ROOT/'SOURCE_HASHES.json').read_text()):
        raise RuntimeError('Source binding changed')
    for name,digest in json.loads((ROOT/'FROZEN_OLD_INPUTS.json').read_text()).items():
        if sha(REPO/name) != digest: raise RuntimeError('Frozen older input changed: '+name)
    roots = (ROOT/'ROOTS.txt').read_text().splitlines()
    declared = math_roots()
    if len(roots) != len(set(roots)) or len(declared) != len(set(declared)) or set(roots) != set(declared):
        raise RuntimeError('Mathematical declaration/root inventory mismatch')
    controls = (ROOT/'CONTROLS.txt').read_text().splitlines()
    if len(controls) != len(set(controls)) or not set(controls) <= set(roots):
        raise RuntimeError('Invalid controls')
    if (ROOT/'lean-toolchain').read_text().strip() != 'leanprover/lean4:v4.34.1':
        raise RuntimeError('Wrong Lean toolchain')
    manifest = json.loads((ROOT/'lake-manifest.json').read_text())
    if [p.get('rev') for p in manifest['packages'] if p['name']=='mathlib'] != [PIN]:
        raise RuntimeError('Wrong Mathlib pin')
    for dep in manifest['packages']:
        if dep['type'] != 'git': continue
        source = ROOT/'.lake/packages'/dep['name']
        if not source.exists(): raise RuntimeError('Missing pinned dependency '+dep['name'])
        actual = subprocess.check_output(['git','-C',str(source),'rev-parse','HEAD'],text=True).strip()
        if actual != dep['rev']: raise RuntimeError('Wrong actual dependency pin '+dep['name'])
        if subprocess.run(['git','-C',str(source),'diff','--quiet','HEAD','--'],capture_output=True).returncode:
            raise RuntimeError('Tracked dependency edits '+dep['name'])
    for p,_ in math_files():
        if re.search(r'\b(sorry|admit|axiom|native_decide|unsafe)\b',without_comments(p.read_text())):
            raise RuntimeError('Forbidden mathematical proof token '+str(p))
    check_standard_cache()
    print('SOURCE_BINDING_PASS',len(inventory()),'ROOTS',len(roots),'CONTROLS',len(controls),flush=True)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--write-manifest',action='store_true')
    ap.add_argument('--check-only',action='store_true')
    ap.add_argument('--fresh',action='store_true')
    args=ap.parse_args()
    if args.write_manifest:
        (ROOT/'SOURCE_HASHES.json').write_text(json.dumps(inventory(),indent=2)+'\n')
        print('MANIFEST_WRITTEN_NOT_VERIFICATION'); return
    check()
    if args.check_only: return
    outputs = [ROOT.parent/pkg/'.lake/build' for pkg in NEW_PACKAGES]
    if args.fresh:
        for output in outputs:
            if output.is_symlink() or output.name!='build' or not output.resolve().is_relative_to(REPO.resolve()):
                raise RuntimeError('Unsafe owned build path '+str(output))
        for output in outputs:
            if output.exists(): shutil.rmtree(output)
    stamp=datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    out=ROOT/'verification'/('reproduction-'+stamp)
    out.mkdir(parents=True,exist_ok=False)
    shutil.copy2(ROOT/'SOURCE_HASHES.json',out/'SOURCE_HASHES.json')
    records=[]
    def stage(name,cmd,limit):
        log=out/(name+'.log'); start=time.monotonic()
        with log.open('w') as f:
            p=subprocess.Popen(cmd,cwd=ROOT,stdout=f,stderr=subprocess.STDOUT,start_new_session=True)
            try: code=p.wait(timeout=limit)
            except subprocess.TimeoutExpired:
                os.killpg(p.pid,signal.SIGKILL); p.wait(); code=124
        rec=dict(stage=name,command=cmd,exit_code=code,seconds=round(time.monotonic()-start,3),
                 log=log.name,sha256=sha(log))
        records.append(rec);(out/'STAGES.json').write_text(json.dumps(records,indent=2)+'\n')
        print(json.dumps(rec),flush=True)
        if code: print(log.read_text()[-10000:]);raise RuntimeError('Failed stage '+name)
        return log.read_text()
    stage('toolchain',['lake','env','lean','--version'],90)
    # Build component libraries in dependency order to limit memory pressure.
    # No third-party or frozen old owned-output directory is deleted.
    for label,target in [
        ('matrix-projector','@extractionMatrixProjector/MatrixSubspace'),
        ('symmetric-support','@extractionSymmetricSupport/SymmetricSupport'),
        ('information-spectrum','@extractionInformationSpectrum/Spectrum'),
        ('rank-support','@extractionRankFoundation/RankSupport'),
        ('spectral-protocol','@extractionSpectralProtocol/SpectralProtocol'),
        ('universal-orbit','@extractionUniversalOrbit/UniversalOrbit'),
        ('minimax-profile','@extractionMinimaxProfile/MinimaxProfile')]:
        stage('build-'+label,['lake','build',target],1200)
    stage('build',['lake','build','Connections','ConnectionsVerification'],1200)
    stage('types-and-axioms',['lake','env','lean','-j1','-M9000','Check.lean'],300)
    audit=stage('kernel',['lake','env','lean','-j1','-M10000','Audit.lean'],1800)
    controls=(ROOT/'CONTROLS.txt').read_text().splitlines()
    if audit.count('EMPTY_KERNEL_REPLAY_PASS')!=1 or audit.count('CORRUPTED_PROOF_REJECTED')!=len(controls):
        raise RuntimeError('Incomplete replay/control markers')
    axioms=set((ROOT/'verification/connections-kernel-axioms.txt').read_text().splitlines())
    if not axioms <= ALLOWED_AXIOMS: raise RuntimeError('Unexpected axioms')
    for p in (ROOT/'verification').glob('connections-*.txt'): shutil.copy2(p,out/p.name)
    check()
    result=dict(status='PASS',scope='Combined new extraction additions: actual pure balanced target-uniform minimax; actual intrinsic rank support and fixed-spectrum integer Bell optima; actual finite spectral envelopes and multisector local protocols; universal orbit compression with retained complete product-local witnesses, fixed-dimension pointwise subcritical unit-fidelity and positive-varentropy Gaussian limits; actual iid spectrum converses, variational identities and type/escort bounds. Not whole-manuscript formalization: no general-rank sharp Haar two moments or Weyl constants, efficient circuit/gate counts, Berry--Esseen, composed matching exponents/reliability inverses or abstract CP/Kraus equivalence.',
        fresh_owned_output_build=args.fresh, fresh_packages=NEW_PACKAGES if args.fresh else [],
        source_files=len(inventory()),roots=len((ROOT/'ROOTS.txt').read_text().splitlines()),
        kernel_declarations=int(re.search(r'EMPTY_KERNEL_REPLAY_PASS (\d+) declarations',audit).group(1)),
        kernel_trust=0,axioms=sorted(axioms),same_type_forged_proof_controls=len(controls),
        standardized_multinomial_cache=True,source_manifest_sha256=sha(ROOT/'SOURCE_HASHES.json'),stages=records)
    (out/'SUMMARY.json').write_text(json.dumps(result,indent=2)+'\n')
    (ROOT/'verification/LATEST.json').write_text(json.dumps(dict(directory=out.name,
        summary_sha256=sha(out/'SUMMARY.json')),indent=2)+'\n')
    print('CONNECTIONS_REPRODUCTION_PASS',str(out),flush=True)

if __name__=='__main__':main()
