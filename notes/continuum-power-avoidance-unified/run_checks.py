#!/usr/bin/env python3
"""Read-only public manuscript checks. Never generates or refreshes trusted hashes.

Python 3 and GNU patch suffice for the standalone checks. Formal source checks
read the two separately distributed projects. PDF rebuilds require pdflatex and
pdftotext, run without shell escape, and never overwrite the supplied PDF.
This public-derived checker does not prove the infinite theorem or run Lean.
"""
from pathlib import Path, PurePosixPath
import argparse
import csv
import difflib
import hashlib
import io
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent
ANCHORS = {
    'source/continuum-avoidance.tex': 'd184d2dcd5571726f1591c9d2f2aa0d87a4607985761c31753a432b4c3d6ca88',
    'continuum-avoidance.pdf': '3b431f48eb326de717df9bcdde698dcd591fd70377b1fe6754aae02119a6411c',
    'revision/source.patch': '0ac73402a4e2f71f5215e817f8d7cf69c0e8b9ba486cef8b6922de09e07dd099',
    'revision/baseline/source/continuum-avoidance.tex': '6d91b919c57397590baeb1ab6b11eafadd573fddde37c8d6226984c847d9452b',
    'revision/baseline/continuum-avoidance.pdf': 'ad6c51378aa6105336183ead1596b8310c4d5bc76544e79938881effc9ab14d2',
}

def require(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Duplicate JSON key: ' + key)
        result[key] = value
    return result


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'), object_pairs_hook=unique_object)


def safe_path(root, relative):
    p = PurePosixPath(relative)
    require(isinstance(relative, str) and str(p) == relative and not p.is_absolute()
            and relative not in ('', '.') and '..' not in p.parts and '\\' not in relative,
            'Unsafe relative path')
    result = root.joinpath(*p.parts)
    current = root
    for part in p.parts:
        current = current / part
        require(not current.is_symlink(), 'Symlink is not an authenticated source: ' + relative)
    require(result.is_file(), 'Missing file: ' + relative)
    return result


def command(args, cwd=None, env=None):
    require(shutil.which(str(args[0])) is not None, 'Required executable is missing: ' + str(args[0]))
    process = subprocess.run(args, cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    require(process.returncode == 0, 'Subprocess failed: ' + str(args[0]) + '\n' +
            process.stderr.decode(errors='replace')[-2000:] +
            process.stdout.decode(errors='replace')[-2000:])
    return process.stdout


def check_integrity():
    require(not (ROOT/'MANIFEST.json').is_symlink() and not (ROOT/'SHA256SUMS').is_symlink(),
            'Symlinked integrity file')
    manifest = read_json(ROOT/'MANIFEST.json')
    require(manifest['schema_version'] == 1 and manifest['manuscript_revision'] == 2,
            'Unsupported manifest')
    files = manifest['files']
    require(isinstance(files, dict) and files, 'Empty manifest')
    actual = set()
    for path in ROOT.rglob('*'):
        require(not path.is_symlink(), 'Unexpected symlink in package')
        if path.is_file():
            actual.add(path.relative_to(ROOT).as_posix())
        else:
            require(path.is_dir(), 'Non-regular package entry')
    require(actual == set(files) | {'MANIFEST.json', 'SHA256SUMS'},
            'Package inventory changed: ' + repr(sorted(actual ^ (set(files) | {'MANIFEST.json', 'SHA256SUMS'}))))
    for rel, record in files.items():
        data = safe_path(ROOT, rel).read_bytes()
        require(type(record['bytes']) is int and len(data) == record['bytes'], 'Byte-size mismatch: ' + rel)
        require(sha(data) == record['sha256'], 'Manifest hash mismatch: ' + rel)
    sums = {}
    for line in (ROOT/'SHA256SUMS').read_text().splitlines():
        matched = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        require(matched is not None, 'Malformed checksum line')
        digest, rel = matched.groups()
        require(rel not in sums, 'Duplicate checksum path: ' + rel)
        require(sha(safe_path(ROOT, rel).read_bytes()) == digest, 'Checksum mismatch: ' + rel)
        sums[rel] = digest
    require(set(sums) == set(files) | {'MANIFEST.json'}, 'Checksum inventory changed')
    for rel, digest in ANCHORS.items():
        require(sha(safe_path(ROOT, rel).read_bytes()) == digest, 'Frozen revision anchor changed: ' + rel)
    origin = read_json(ROOT/'provenance/original-revision2-manifest.json')
    provenance = read_json(ROOT/'PROVENANCE.json')
    for rel, record in provenance['unchanged_source_members'].items():
        require(origin['files'][rel] == record, 'Source provenance record changed: ' + rel)
        require(sha(safe_path(ROOT, rel).read_bytes()) == record['sha256'], 'Original member changed: ' + rel)
    require(provenance['input_archive']['sha256'] == '73772896db3dabaa4fc38eb389bbef7d6f1d09b2fdffde2bf0c80b8da869a7d2',
            'Revision delivery identity changed')
    return len(files)


def check_revision():
    old = (ROOT/'revision/baseline/source/continuum-avoidance.tex').read_text()
    new = (ROOT/'source/continuum-avoidance.tex').read_text()
    patch = (ROOT/'revision/source.patch').read_text()
    independent = ''.join(difflib.unified_diff(old.splitlines(keepends=True), new.splitlines(keepends=True),
                                             fromfile='a/source/continuum-avoidance.tex',
                                             tofile='b/source/continuum-avoidance.tex'))
    require(independent == patch, 'Independent unified diff does not match frozen patch')
    with tempfile.TemporaryDirectory(prefix='manuscript-revision-') as temp:
        root = Path(temp)
        (root/'source').mkdir()
        (root/'source/continuum-avoidance.tex').write_text(old)
        patch_file = root/'revision.patch'
        patch_file.write_text(patch)
        command(['patch', '--batch', '--fuzz=0', '-p1', '-i', str(patch_file)], cwd=root)
        require((root/'source/continuum-avoidance.tex').read_bytes() ==
                (ROOT/'source/continuum-avoidance.tex').read_bytes(), 'Exact patch replay mismatch')
        shutil.copyfile(ROOT/'revision/check_origin_guard.py', root/'check_origin_guard.py')
        flags = ['-B'] + ([] if __debug__ else ['-O'])
        result = json.loads(command([sys.executable, *flags, str(root/'check_origin_guard.py')]))
        require(result['status'] == 'PASS' and result['early_window']['old_lower_count_refuted'] is True,
                'Origin control did not refute the old statement')
        require(len(result['guarded_endpoint_cases']) == 8, 'Origin endpoint controls incomplete')
        require(result['optimization_active'] is (not __debug__), 'Origin control optimization mode mismatch')
    require('\\author{}' in new, 'Blank author field changed')
    closure = read_json(ROOT/'review/REVISION2_CLOSURE.json')
    require(closure['status'] == 'PASS' and closure['all_four_corrections_closed'] is True
            and closure['remaining_mathematical_blockers'] == [], 'Revision closure not PASS')
    return {'exact_diff_and_zero_fuzz_replay': True, 'old_origin_countercontrol': True,
            'guarded_endpoint_cases': 8, 'blank_author_preserved': True}


def read_csv(relative):
    return list(csv.DictReader(io.StringIO((ROOT/relative).read_text())))


def check_correspondence():
    tex = (ROOT/'source/continuum-avoidance.tex').read_text() + (ROOT/'source/correspondence.tex').read_text()
    labels = re.findall(r'\\label\{([^}]+)\}', tex)
    require(len(labels) == len(set(labels)), 'Duplicate paper labels')
    refs = re.findall(r'\\(?:eqref|ref)\{([^}]+)\}', tex)
    require(set(refs) <= set(labels), 'Unresolved paper reference')
    citations = {key.strip() for group in re.findall(r'\\cite\{([^}]+)\}', tex) for key in group.split(',')}
    require(citations <= set(re.findall(r'\\bibitem\{([^}]+)\}', tex)), 'Unresolved bibliography citation')
    mapping = read_json(ROOT/'evidence/theorem-correspondence.json')
    mapped_csv = read_csv('evidence/theorem-correspondence.csv')
    normalized = [{key: str(value) for key, value in row.items()} for row in mapping]
    require(normalized == mapped_csv, 'Correspondence CSV/JSON mismatch')
    require(len(mapping) == 57 and len({row['declaration'] for row in mapping}) == 57,
            'Expected 57 distinct mapped declarations')
    steps = {row['paper_label'] for row in mapping}
    require(len(steps) == 20 and steps <= set(labels), 'Expected 20 valid mapped paper steps')
    inventory = read_csv('evidence/declaration-inventory.csv')
    require(len(inventory) == 759, 'Expected 759 source-visible inventory entries')
    index = {row['declaration']: row for row in inventory}
    require(len(index) == len(inventory), 'Duplicate inventory declaration')
    for row in mapped_csv:
        require(row['declaration'] in index, 'Mapped declaration absent from inventory')
        require(all(row[key] == value for key, value in index[row['declaration']].items()),
                'Mapped declaration/inventory mismatch')
    imports = read_json(ROOT/'evidence/module-imports.json')
    require(len(imports) == 65, 'Expected 65 source modules including two aggregates')
    edges = read_csv('evidence/module-imports.csv')
    require(len([e for e in edges if e['scope'] == 'local']) == 172, 'Expected 172 local module-import edges')
    for row in inventory:
        require(row['module'] in imports and imports[row['module']]['path'] == row['archive_path']
                and imports[row['module']]['sha256'] == row['source_sha256'], 'Inventory module/hash mismatch')
    return mapping, inventory, imports, {'paper_steps': 20, 'mapped_declarations': 57,
            'source_visible_declarations': 759, 'source_modules': 65, 'local_import_edges': 172,
            'scope': 'Source map and inventories; not kernel proof dependency closure.'}


def check_formal_sources(geometric, continuum, mapping, inventory, imports):
    geometric, continuum = geometric.resolve(strict=True), continuum.resolve(strict=True)
    source_bytes = {}
    for module, record in imports.items():
        raw = safe_path(continuum, record['path']).read_bytes()
        require(sha(raw) == record['sha256'], 'Formal source hash mismatch: ' + module)
        source_bytes[record['path']] = raw
    geometric_modules = [record for module, record in imports.items() if module.startswith('ContinuumGeometric.')]
    require(len(geometric_modules) == 45, 'Expected 45 reused geometric modules')
    for record in geometric_modules:
        rel = str(PurePosixPath(record['path']).relative_to('project'))
        require(safe_path(geometric, rel).read_bytes() == source_bytes[record['path']],
                'Geometric reuse differs: ' + rel)
    for row in inventory:
        lines = source_bytes[row['archive_path']].decode().splitlines()
        number = int(row['line'])
        require(1 <= number <= len(lines), 'Invalid declaration line')
        line = lines[number-1]
        require(re.search(r'\b(theorem|lemma|def|abbrev|structure|class|inductive)\b', line),
                'Inventory source location is not a declaration')
        short_name = row['declaration'].split('.')[-1]
        require(re.search(r'(?<![\w\'])' + re.escape(short_name) + r'(?![\w\'])', line),
                'Exact declaration name absent at pinned line: ' + row['declaration'])
    freeze = read_json(ROOT/'evidence/source-freeze.json')
    require(len(freeze) == 18, 'Expected 18 continuum module pins')
    for rel, digest in freeze.items():
        require(sha(source_bytes[rel]) == digest, 'Continuum frozen-source mismatch')
    return {'status': 'PASS', 'module_hashes_verified': 65, 'inventory_declaration_lines_verified': 759,
            'mapped_declaration_lines_verified': len(mapping), 'geometric_reuse_modules': 45,
            'continuum_frozen_modules': 18, 'new_lean_build': False, 'new_kernel_replay': False}


def check_pdf_build(output):
    if output:
        output = output.resolve()
        require(output != ROOT and ROOT not in output.parents, 'Build output must be outside frozen package')
        require(not output.exists(), 'Build output already exists; choose a new directory')
    with tempfile.TemporaryDirectory(prefix='manuscript-pdf-') as temp:
        build = Path(temp)
        for name in ['continuum-avoidance.tex', 'correspondence.tex']:
            shutil.copyfile(ROOT/'source'/name, build/name)
        environment = os.environ.copy()
        environment.update(TEXMFVAR=str(build/'tex-cache'), TEXMFCONFIG=str(build/'tex-config'),
                           VARTEXFONTS=str(build/'tex-fonts'))
        environment['TEXFORMATS'] = str(build) + os.pathsep + environment.get('TEXFORMATS', '')
        require(shutil.which('kpsewhich') is not None, 'TeX kpsewhich is missing')
        def located(name):
            probe = subprocess.run(['kpsewhich', name], env=environment, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            return probe.returncode == 0 and bool(probe.stdout.strip())
        format_bootstrap = not all(located(name) for name in ['pdflatex.fmt', 'article.cls', 'pdftex.map'])
        if format_bootstrap:
            # Some minimal Debian TeX installations have the standard package
            # files but neither a format nor an ls-R index. Read those installed
            # files directly; never download packages or write system caches.
            base, extra = Path('/usr/share/texlive/texmf-dist'), Path('/usr/share/texmf')
            ini = base/'tex/latex/tex-ini-files/pdflatex.ini'
            require(ini.is_file(), 'A usable standard pdfLaTeX installation is required')
            cache = build/'tex-cache'
            cache.mkdir()
            (cache/'language.dat').write_text('english hyphen.tex\n')
            environment.update(TEXMF='{'+str(base)+','+str(extra)+'}',
                TEXINPUTS='.'+os.pathsep+str(cache)+os.pathsep+str(base)+'/tex//'+os.pathsep+str(extra)+'/tex//'+os.pathsep,
                TEXFORMATS=str(cache)+os.pathsep, TEXFONTMAPS=str(cache)+os.pathsep+str(base)+'/fonts/map//'+os.pathsep+str(extra)+'/fonts/map//'+os.pathsep)
            for variable, directory in [('TFMFONTS','tfm'),('VFFONTS','vf'),('T1FONTS','type1'),('ENCFONTS','enc')]:
                environment[variable] = str(base)+'/fonts/'+directory+'//'+os.pathsep+str(extra)+'/fonts/'+directory+'//'+os.pathsep
            maps = [extra/'fonts/map/dvips/lm/lm.map', base/'fonts/map/dvips/amsfonts/cm.map',
                    base/'fonts/map/dvips/amsfonts/symbols.map', base/'fonts/map/dvips/amsfonts/euler.map']
            require(all(path.is_file() for path in maps), 'Standard TeX font maps are missing')
            (cache/'pdftex.map').write_bytes(b'\n'.join(path.read_bytes() for path in maps))
            format_log = command(['pdftex', '-ini', '-etex', '-no-shell-escape', '-interaction=nonstopmode',
                                  '-halt-on-error', '-jobname=pdflatex', str(ini)], cwd=cache, env=environment)
            (cache/'format-bootstrap.txt').write_bytes(format_log)
            require((cache/'pdflatex.fmt').is_file(), 'Isolated TeX format generation failed')
        for turn in range(1, 4):
            log = command(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode', '-halt-on-error',
                           'continuum-avoidance.tex'], cwd=build, env=environment)
            (build/f'pass-{turn}.txt').write_bytes(log)
        log = (build/'continuum-avoidance.log').read_text()
        for marker in ['undefined references', 'undefined on input', 'multiply defined', 'Overfull', 'Missing character']:
            require(marker not in log, 'Final TeX problem: ' + marker)
        supplied_text = command(['pdftotext', '-layout', str(ROOT/'continuum-avoidance.pdf'), '-'])
        rebuilt_text = command(['pdftotext', '-layout', str(build/'continuum-avoidance.pdf'), '-'])
        require(supplied_text == rebuilt_text, 'Rebuilt PDF text differs from frozen PDF:\n' + ''.join(difflib.unified_diff(supplied_text.decode().splitlines(keepends=True), rebuilt_text.decode().splitlines(keepends=True), fromfile='frozen-pdf', tofile='rebuilt-pdf'))[:4000])
        require(rebuilt_text.count(b'\f') == 14 and b'??' not in rebuilt_text, 'PDF page/reference check failed')
        result = {'status': 'PASS', 'pages': 14, 'text_equal_to_frozen_pdf': True,
                  'text_sha256': sha(rebuilt_text), 'shell_escape': False,
                  'isolated_format_bootstrap': format_bootstrap,
                  'fallback_hyphenation': 'english hyphen.tex' if format_bootstrap else None,
                  'pdf_byte_identity_required': False,
                  'reason': 'PDF timestamps/engine metadata may differ; frozen delivery PDF stays unchanged.'}
        if output:
            shutil.copytree(build, output)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repository-root', type=Path, help='Checkout containing both formalizations/ projects')
    parser.add_argument('--geometric-root', type=Path, help='Separately extracted geometric-avoidance project root')
    parser.add_argument('--continuum-root', type=Path, help='Separately extracted continuum-remainder-avoidance root')
    parser.add_argument('--build-pdf', action='store_true', help='Rebuild in isolation and compare all PDF text')
    parser.add_argument('--build-output', type=Path, help='New external directory to retain isolated PDF build; implies --build-pdf')
    args = parser.parse_args()
    require(not (args.repository_root and (args.geometric_root or args.continuum_root)), 'Choose one formal-source input route')
    require(bool(args.geometric_root) == bool(args.continuum_root), 'Both separate formalization roots are required')
    count = check_integrity()
    revision = check_revision()
    mapping, inventory, imports, correspondence = check_correspondence()
    formal = {'status': 'NOT_RUN', 'reason': 'Supply a repository root or both public formalization roots.',
              'new_lean_build': False, 'new_kernel_replay': False}
    if args.repository_root:
        formal = check_formal_sources(args.repository_root/'formalizations/geometric-avoidance',
                                     args.repository_root/'formalizations/continuum-remainder-avoidance',
                                     mapping, inventory, imports)
    elif args.geometric_root:
        formal = check_formal_sources(args.geometric_root, args.continuum_root, mapping, inventory, imports)
    pdf = check_pdf_build(args.build_output) if args.build_pdf or args.build_output else {'status': 'NOT_RUN'}
    require(check_integrity() == count, 'Package changed while checking')
    print(json.dumps({'status': 'PASS', 'python_optimization_active': not __debug__,
                      'payload_files_verified': count, 'revision': revision,
                      'correspondence': correspondence, 'formal_source_comparison': formal,
                      'isolated_pdf_rebuild': pdf, 'package_mutations': 0,
                      'scope': 'Integrity, finite origin controls, revision, correspondence, and requested optional checks; not a proof of the infinite theorem.'}, indent=2))


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print(json.dumps({'status': 'FAIL', 'error': str(error)}, indent=2), file=sys.stderr)
        sys.exit(1)
