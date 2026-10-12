#!/usr/bin/env python3
"""Clean Lean kernel compilation of every owned mathematical module.

Run inside `lake env`; dependencies must have official pinned cache artifacts.
An optional ENTRY005_MATHLIB_OVERLAY selects a separately verified official
mathlib cache directory. No source replacement or kernel options are used.
"""
import os
import pathlib
import re
import shutil
import subprocess
import sys

root = pathlib.Path(__file__).resolve().parents[1]
os.chdir(root)
sources = [root / "Entry005.lean"]
sources += sorted((root / "Entry005").glob("*.lean"))
sources += sorted((root / "Mxym").glob("*.lean"))
modules = {p.relative_to(root).with_suffix("").as_posix().replace("/", "."): p for p in sources}
deps = {}
for name, path in modules.items():
    deps[name] = [m for line in path.read_text().splitlines()
                  if line.startswith("import ") for m in line[7:].split() if m in modules]
order = []
visiting = set()
seen = set()
def visit(name):
    if name in visiting:
        raise RuntimeError("cyclic owned imports: " + name)
    if name in seen:
        return
    visiting.add(name)
    for dep in deps[name]:
        visit(dep)
    visiting.remove(name)
    seen.add(name)
    order.append(name)
for name in modules:
    visit(name)
build = root / ".lake/build"
if build.is_symlink():
    raise RuntimeError("refusing to clear a symlinked owned build directory")
if build.exists():
    shutil.rmtree(build)
lib = build / "lib/lean"
lib.mkdir(parents=True)
env = os.environ.copy()
prefix = env.get("ENTRY005_MATHLIB_OVERLAY")
env["LEAN_PATH"] = str(lib) + ":" + ((prefix + ":") if prefix else "") + env.get("LEAN_PATH", "")
subprocess.run(["lean", "--version"], check=True, env=env)
for name in order:
    src = modules[name].relative_to(root)
    output = lib / src.with_suffix(".olean")
    output.parent.mkdir(parents=True, exist_ok=True)
    print("KERNEL_COMPILE " + str(src), flush=True)
    subprocess.run(["lean", "-DautoImplicit=false", str(src), "-o", str(output),
                    "-i", str(output.with_suffix(".ilean"))], check=True, env=env)
print(f"CLEAN_OWNED_BUILD_PASS {len(order)} modules", flush=True)
