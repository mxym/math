#!/usr/bin/env python3
"""Fresh owned compilation, declaration audit, and empty-kernel replay.

Uses already-installed official dependencies; does not install or download.
Run with --help for explicit filesystem paths. No old owned .olean is used.
"""
import argparse
import json
import pathlib
import shutil
import subprocess

ROOT = pathlib.Path(__file__).resolve().parent

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=pathlib.Path, required=True)
    parser.add_argument('--toolchain', type=pathlib.Path, required=True)
    parser.add_argument('--packages-root', type=pathlib.Path, required=True)
    parser.add_argument('--cache-root', type=pathlib.Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    for name in ['bin', 'checks']:
        shutil.copytree(ROOT / 'verifier' / name, output / name)
    for name in ['config', 'locks', 'tasks']:
        (output / name).mkdir()
    environment = json.loads((ROOT / 'verifier/environment-template.json').read_text())
    environment.update(toolchain_path=str(args.toolchain.resolve()),
                       packages_root=str(args.packages_root.resolve()),
                       cache_root=str(args.cache_root.resolve()),
                       owner_thread='independent cofactor finite ring construction reproduction')
    (output / 'config/environment.json').write_text(json.dumps(environment, indent=2) + '\n')
    case = json.loads((ROOT / 'case.json').read_text())
    case['source_dir'] = str(ROOT / 'src')
    case_path = output / 'config/case.json'
    case_path.write_text(json.dumps(case, indent=2) + '\n')
    subprocess.run(['python3', str(output / 'bin/leanctl.py'), 'verify', str(case_path)], check=True)

if __name__ == '__main__':
    main()
