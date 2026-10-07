#!/usr/bin/env python3
"""Replay exact finite evidence and check the source-complete public whitelist.

This script uses only Python's standard library and writes replay results into
a temporary directory. It does not certify the infinite mathematical proofs.
"""
from pathlib import Path
import ast, hashlib, importlib.util, json, os, shutil, subprocess, sys, tempfile

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
B=ROOT/'notes/bounded-cluster-avoidance/verification'

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def need(condition,message):
    if not condition: raise ArithmeticError(message)
def main():
    manifest=json.loads((HERE/'MANIFEST.json').read_text())
    payload=manifest['files']
    for row in payload:
        p=ROOT/row['path']
        need(p.is_file(),f'Missing public file: {row["path"]}')
        need(digest(p)==row['sha256'],f'Hash mismatch: {row["path"]}')
        need(p.stat().st_size==row['bytes'],f'Byte size mismatch: {row["path"]}')
    allowed=set(manifest['whitelist'])
    actual=set()
    for prefix in manifest['owned_directories']:
        for p in (ROOT/prefix).rglob('*'):
            if p.is_file():actual.add(str(p.relative_to(ROOT)))
    for path in manifest['owned_single_files']:
        if (ROOT/path).is_file():actual.add(path)
    need(actual==allowed,f'Whitelist differs: missing={sorted(allowed-actual)}, extra={sorted(actual-allowed)}')
    prov=json.loads((HERE/'PROVENANCE.json').read_text())
    for row in prov['source_snapshots']:
        p=HERE/row['file']; data=p.read_bytes()
        need(digest(p)==row['sha256'],f'Source SHA-256 mismatch: {row["file"]}')
        need(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==row['git_blob_sha1'],
             f'Source Git blob mismatch: {row["file"]}')
    for row in prov['audited_subjects']:
        need(digest(HERE/row['file'])==row['sha256'],'Audited subject changed')
    def algorithm(p):
        tree=ast.parse(p.read_text())
        if tree.body and isinstance(tree.body[0],ast.Expr) and isinstance(tree.body[0].value,ast.Constant):
            tree.body.pop(0)
        return ast.dump(tree,include_attributes=False)
    need(algorithm(B/'check_cluster_cover.py')==algorithm(HERE/'audited-subjects/check_cluster_cover.original.py'),
         'Public checker algorithm differs from original')
    with tempfile.TemporaryDirectory(prefix='avoidance-cover-replay-') as tmp:
        work=Path(tmp)
        for p in B.glob('*'):
            if p.is_file():shutil.copyfile(p,work/p.name)
        env={**os.environ,'PYTHONDONTWRITEBYTECODE':'1'}
        def run(args):
            r=subprocess.run([sys.executable,*args],cwd=work,env=env,capture_output=True)
            need(r.returncode==0,r.stderr.decode() or r.stdout.decode())
            return r.stdout
        expected=(B/'self_test.json').read_bytes()
        normal=run(['check_cluster_cover.py','--self-test'])
        optimized=run(['-O','check_cluster_cover.py','--self-test'])
        need(normal==expected==optimized,'Regression output changed')
        for suffix in ('','_3_4'):
            stdout=run(['check_cluster_cover.py',f'toy_cluster_certificate{suffix}.json'])
            need(stdout==(B/f'toy_cluster_result{suffix}.json').read_bytes(),'Toy certificate output changed')
            need(run(['-O','check_cluster_cover.py',f'toy_cluster_certificate{suffix}.json'])==stdout,
                 'Optimized toy output differs')
        run(['independent_checker_audit.py'])
        need((work/'independent_checker_results.json').read_bytes()==(B/'independent_checker_results.json').read_bytes(),
             'Independent oracle output changed')
        oracle=json.loads((work/'independent_checker_results.json').read_text())
        need((oracle['cases'],oracle['covers'],oracle['failures'])==(1006,159,847),'Wrong oracle case count')
        run(['-O','independent_checker_audit.py'])
        need((work/'independent_checker_results.json').read_bytes()==(B/'independent_checker_results.json').read_bytes(),
             'Optimized independent oracle output changed')
    print(json.dumps({'status':'PASS','public_payload_files':len(payload),'whitelist_files':len(allowed),
        'pinned_source_snapshots':len(prov['source_snapshots']),'original_regressions':7,
        'independent_oracle_cases':1006,'covers':159,'failures':847,
        'scope':'Exact finite certificate replay and public-package/source integrity; not formal verification of the infinite proofs'},indent=2))

if __name__=='__main__':main()
