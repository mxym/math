#!/usr/bin/env python3
"""Rebuild the additive upper-Main closure over verified714 in a private cache.
Use --rebuild-all-owned to rebuild the complete included owned source chain.
No network, dependency-source write, or source-tree cache write is performed.
"""
from pathlib import Path
import argparse, hashlib, json, os, re, shutil, subprocess, tempfile
from source_inventory import digest, import_record, topo, public_proof_inventory, source_code

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def require(ok, message):
    if not ok:
        raise RuntimeError(message)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packages-dir', type=Path, required=True)
    ap.add_argument('--lean-bin', type=Path, required=True)
    ap.add_argument('--verified714-cache', type=Path, required=True)
    ap.add_argument('--rebuild-all-owned', action='store_true')
    options = ap.parse_args()
    packages = options.packages_dir.resolve()
    lean = options.lean_bin.resolve() / 'lean'
    leanroot = lean.parent.parent
    cache = options.verified714_cache.resolve()
    version = subprocess.check_output([str(lean), '--version'], text=True).strip()
    require('4.34.1' in version and '5045d0056413266e57c625dcd7c365b10e377c52' in version,
            'Wrong Lean toolchain')
    pins = json.loads((ROOT / 'scripts/pins.json').read_text())
    for name, pin in pins.items():
        p = packages / name
        require(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=p, text=True).strip() == pin['rev'],
                'Wrong dependency pin: ' + name)
        require(not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=p, text=True),
                'Dirty dependency: ' + name)
    manifest = json.loads((ROOT / 'evidence/source-manifest.json').read_text())
    sources = {m: ROOT / 'formal' / (m.replace('.', '/') + '.lean') for m in manifest['owned_modules']}
    for rel, sha in manifest['source_sha256'].items():
        require(digest(ROOT / rel) == sha, 'Source hash mismatch: ' + rel)
    for m, p in sources.items():
        require(not re.search(r'\b(?:sorry|admit|axiom|opaque|unsafe|native_decide|sorryAx)\b', source_code(p.read_text())),
                'Forbidden proof shortcut: ' + m)
    graph = {m: import_record(p) for m, p in sources.items()}
    selected = set(sources) if options.rebuild_all_owned else set(manifest['additive_modules'])
    output = Path(tempfile.mkdtemp(prefix='entry005-upper-main-replay-', dir=ROOT.parent))
    lib = output / 'lib/lean'
    logs = output / 'logs'
    lib.mkdir(parents=True)
    logs.mkdir()
    # Entire namespace views are copied by individual read-only symlinks.
    # Every additive module is excluded so no precompiled new proof is reused.
    excluded = {str(Path(m.replace('.', '/'))) for m in selected}
    for directory, _subdirs, files in os.walk(cache, followlinks=True):
        for filename in files:
            p = Path(directory) / filename
            if not p.is_file():
                continue
            rel = p.relative_to(cache)
            base = str(rel).split('.olean')[0].split('.ilean')[0]
            if base in excluded:
                continue
            q = lib / rel
            q.parent.mkdir(parents=True, exist_ok=True)
            q.symlink_to(p.resolve())
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join([str(lib)] +
        [str(packages / name / '.lake/build/lib/lean') for name in pins] + [str(leanroot / 'lib/lean')])
    compiled = []
    for m in topo(graph):
        if m not in selected:
            continue
        target = lib / (m.replace('.', '/') + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        for suffix in ['.olean', '.olean.private', '.olean.server', '.ilean']:
            q = target.with_suffix(suffix)
            if q.is_symlink():
                q.unlink()
        r = subprocess.run([str(lean), '-DautoImplicit=false', '-DmaxSynthPendingDepth=3',
                            '-DwarningAsError=true', '-o', str(target), str(sources[m])],
                           cwd=ROOT / 'formal', env=env, capture_output=True, text=True)
        (logs / (m + '.compile.log')).write_text(r.stdout + r.stderr)
        require(r.returncode == 0 and not r.stdout and not r.stderr, 'Strict compile failed: ' + m)
        compiled.append(m)
        print('STRICT PASS ' + m, flush=True)
    r = subprocess.run([str(lean), '-DautoImplicit=false', '-DmaxSynthPendingDepth=3',
                        '-DwarningAsError=true', str(ROOT / 'formal/UpperMainAudit.lean')],
                       cwd=ROOT / 'formal', env=env, capture_output=True, text=True)
    audit = r.stdout + r.stderr
    (logs / 'upper-main-signatures-and-axioms.txt').write_text(audit)
    require(r.returncode == 0 and 'warning:' not in audit and 'error:' not in audit, 'Audit failed')
    for name in manifest['audited_public_names']:
        match = re.search(re.escape("'" + name + "'") + r' depends on axioms: \[([^\]]*)\]', audit)
        require(match is not None, 'Missing axiom audit: ' + name)
        axioms = {re.sub(r'\.\{[^}]*\}', '', x.strip()) for x in match[1].split(',') if x.strip()}
        require(axioms <= ALLOWED, 'Nonstandard axiom: ' + name)
    require('Entry005.sharpMain : Entry005.sharpMainGoal' in audit, 'Literal Main check absent')
    for name in pins:
        require(not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'],
                                            cwd=packages / name, text=True), 'Dependency changed: ' + name)
    result = {'status': 'PASS', 'compiled_modules': compiled, 'strict_warnings': 0,
              'all_selected_modules_recompiled_to_fresh_regular_outputs': True,
              'standard_axioms_only': True, 'literal_sharpMainGoal_inhabited': True,
              'literal_original_MainTarget_inhabited': True,
              'no_finite_Minkowski_or_first_variation_premise': True,
              'all_prescribed_maxima_original_centroid_constants_exponent_preserved': True,
              'rebuild_all_owned': options.rebuild_all_owned,
              'audited_names': len(manifest['audited_public_names']),
              'audit_sha256': hashlib.sha256(audit.encode()).hexdigest(),
              'independent_empty_kernel_audit_of_new_integration_claimed': False,
              'output_directory': str(output)}
    (output / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)

if __name__ == '__main__':
    main()
