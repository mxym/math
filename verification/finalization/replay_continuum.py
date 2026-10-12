#!/usr/bin/env python3
"""Replay the sealed continuum package with its cache-miss build repairs.

The original release is validated by its unchanged verifier. Only its Python
dependency scanner, cached import-closure traversal and Mathlib compilation
options are corrected; every Lean source, guard, inventory and kernel replay
is the original pinned input.
"""
import hashlib
import importlib.util
import sys
from pathlib import Path

sys.dont_write_bytecode = True
REPO = Path(__file__).resolve().parents[2]
RELEASE = REPO / "formalizations/continuum-remainder-avoidance"
ORIGINAL = RELEASE / "scripts/verify.py"
ORIGINAL_SHA256 = "c0f68c5904bf175e284d4255f5dfb3a1c43a19643e821172b2d88b7d6330bdc5"
SCANNER = REPO / "formalizations/sharp-simplex-upper-bound/scripts/source_inventory.py"
SCANNER_SHA256 = "3f4732fab33823e303dc60452ddf7f3d6f1cb4152c816229e166343576be1e8b"


def load_verifier():
    if hashlib.sha256(ORIGINAL.read_bytes()).hexdigest() != ORIGINAL_SHA256:
        raise RuntimeError("The pinned historical verifier changed")
    sys.path.insert(0, str(RELEASE / "scripts"))
    spec = importlib.util.spec_from_file_location("sealed_continuum_verifier", ORIGINAL)
    if spec is None or spec.loader is None:
        raise RuntimeError("Cannot load the pinned verifier")
    module = importlib.util.module_from_spec(spec)
    source = ORIGINAL.read_text()
    old_call = "run([lean,'-o',dest,f],cwd=f.parents[len(rel.parts)-1],key='official.'+n)"
    new_call = (
        "run([lean]+(['-DautoImplicit=false','-DmaxSynthPendingDepth=3'] "
        "if n.startswith('Mathlib.') else [])+['-o',dest,f],"
        "cwd=f.parents[len(rel.parts)-1],key='official.'+n)"
    )
    if source.count(old_call) != 1:
        raise RuntimeError("The pinned external-compilation call changed")
    source = source.replace(old_call, new_call)
    old_union = "for d in [extra/'.lake/build/lib/lean',dep/'.lake/packages/mathlib/.lake/build/lib/lean']:"
    new_union = "for d in [extra/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in sources]:"
    if source.count(old_union) != 1:
        raise RuntimeError("The pinned dependency-cache union changed")
    # Lean selects an entire module root. Materialize every package cache,
    # including Batteries, so a partial overlay cannot hide its cached siblings.
    source = source.replace(old_union, new_union)
    old_seen = "seen=set();official=[]"
    old_cache = "  if any((d/rel.with_suffix('.olean')).is_file() for d in [overlay]+dep_roots):return"
    new_cache = """  if n in official_seen:return
  official_seen.add(n)
  if any((d/rel.with_suffix('.olean')).is_file() for d in [overlay]+dep_roots):
   cached_sources=[d/rel.with_suffix('.lean') for d in sources if (d/rel.with_suffix('.lean')).is_file()]
   need(len(cached_sources)<=1,'ambiguous cached pinned source '+n)
   if cached_sources:
    for imported in imports(cached_sources[0]):dep_build(imported)
   else:
    need((toolchain/'lib/lean'/rel.with_suffix('.olean')).is_file(),'cached module has no pinned source '+n)
   return"""
    if source.count(old_seen) != 1 or source.count(old_cache) != 1:
        raise RuntimeError("The pinned external-cache traversal changed")
    source = source.replace(old_seen, old_seen + ";official_seen=set()")
    source = source.replace(old_cache, new_cache)
    # A cached module may import an absent dependency. Walk its pinned source
    # imports as well; a partial cache is not necessarily transitively closed.
    # Leave owned compilation, artifact/ownership guards and kernel checks intact.
    exec(compile(source, str(ORIGINAL), "exec"), module.__dict__)

    if hashlib.sha256(SCANNER.read_bytes()).hexdigest() != SCANNER_SHA256:
        raise RuntimeError("The pinned comment/string-aware import scanner changed")
    scanner_spec = importlib.util.spec_from_file_location("pinned_source_scanner", SCANNER)
    if scanner_spec is None or scanner_spec.loader is None:
        raise RuntimeError("Cannot load the pinned import scanner")
    scanner = importlib.util.module_from_spec(scanner_spec)
    scanner_spec.loader.exec_module(scanner)

    def imports(source):
        return scanner.import_record(source)["imports"]

    module.imports = imports
    return module


if __name__ == "__main__":
    load_verifier().main()
