#!/usr/bin/env python3
"""Typeset this paper; reuse only the source-pinned repository TeX setup."""
import argparse
from hashlib import sha256
import importlib.util
import json
from pathlib import Path
import re
import shutil
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    helper = ROOT / 'manuscripts/build.py'
    pins = json.loads((HERE / 'SOURCES.json').read_text())['local_files']
    pin = next(item for item in pins if item['path'] == 'manuscripts/build.py')
    if sha256(helper.read_bytes()).hexdigest() != pin['sha256']:
        raise RuntimeError('Changed pinned TeX environment helper')
    spec = importlib.util.spec_from_file_location('pinned_tex_helper', helper)
    utils = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(utils)
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    with tempfile.TemporaryDirectory(prefix='growing-gaps-paper-') as tmp:
        work = Path(tmp)
        env = utils.environment(work)
        source = (HERE / 'paper.md').read_text()
        # Use the first two prose lines as title/author metadata, not sections.
        body = source.split('\n', 4)[4]
        (work / 'paper.md').write_text(body)
        (work / 'header.tex').write_text(
            '\\usepackage{amsmath,amssymb,mathtools,xurl}\n'
            '\\emergencystretch=3em\n')
        utils.command(['pandoc', 'paper.md', '--from=markdown+tex_math_single_backslash',
            '--standalone', '--include-in-header=header.tex',
            '--metadata=title:A facet-exchange counterexample to the fixed-mass regular-simplex conjecture',
            '--metadata=author:mxym/math research project (AI-assisted)',
            '--metadata=date:8 October 2026', '-V', 'geometry:margin=25mm',
            '-V', 'fontsize:11pt', '-o', 'paper.tex'], work, env)
        # Pandoc wraps display math in \[...\]. An AMS aligned block with
        # its own \tag needs an equation environment rather than that wrapper.
        tex = (work / 'paper.tex').read_text()
        tex = re.sub(r'\\\[\s*(\\begin\{aligned\}.*?\\end\{aligned\}\s*\\tag\{[^}]+\})\s*\\\]',
                     lambda m: '\\begin{equation*}\n' + m[1] + '\n\\end{equation*}',
                     tex, flags=re.S)
        (work / 'paper.tex').write_text(tex)
        for _ in range(3):
            utils.command(['pdflatex', '-no-shell-escape', '-interaction=nonstopmode',
                           '-halt-on-error', 'paper.tex'], work, env)
        log = (work / 'paper.log').read_text(errors='replace')
        if re.search(r'undefined references|undefined on input|multiply defined|Missing character', log):
            raise RuntimeError('Unresolved reference or missing character')
        overfull = re.findall(r'Overfull \\hbox \(([^)]+)\)', log)
        if overfull:
            raise RuntimeError('Overfull boxes: ' + str(overfull))
        text = utils.command(['pdftotext', '-layout', 'paper.pdf', '-'], work, env)
        if len(text) < 14000:
            raise RuntimeError('Unexpectedly short PDF text')
        info = utils.command(['pdfinfo', 'paper.pdf'], work, env).decode()
        for name in ('paper.tex', 'paper.pdf', 'paper.log'):
            shutil.copyfile(work / name, output / name)
        (output / 'paper.txt').write_bytes(text)
        report = {'status': 'PASS', 'pages': int(re.search(r'Pages:\s+(\d+)', info)[1]),
                  'overfull_hboxes': overfull, 'shell_escape': False,
                  'markdown_sha256': sha256((HERE / 'paper.md').read_bytes()).hexdigest(),
                  'pdf_sha256': sha256((work / 'paper.pdf').read_bytes()).hexdigest(),
                  'tex_sha256': sha256((work / 'paper.tex').read_bytes()).hexdigest(),
                  'environment_helper_sha256': pin['sha256']}
        (output / 'report.json').write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
