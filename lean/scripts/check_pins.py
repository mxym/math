#!/usr/bin/env python3
"""Fail closed on this project's official compiler, source origins and reviewed lock."""
from pathlib import Path
import json, subprocess, sys, tomllib

ROOT = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent
LEAN = "leanprover/lean4:v4.34.1"
COMPILER = "5045d0056413266e57c625dcd7c365b10e377c52"
EXPECTED = {
    "mathlib": ("https://github.com/leanprover-community/mathlib4.git", "d13f23b723b8a846827a245b89c10fc7d3f11612"),
    "plausible": ("https://github.com/leanprover-community/plausible", "118aa17ee84656b8bd727fef7c458ee8c833385c"),
    "LeanSearchClient": ("https://github.com/leanprover-community/LeanSearchClient", "ddf04cf3949fa556442341e87d47f9f6e6074707"),
    "importGraph": ("https://github.com/leanprover-community/import-graph", "e928b72544873815af278d38681b31c0293588e3"),
    "proofwidgets": ("https://github.com/leanprover-community/ProofWidgets4", "106ff4fafc74ef4ac99d81dbf3ab399118f497a5"),
    "aesop": ("https://github.com/leanprover-community/aesop", "355695d523e41d0554926416cba2a2b3544fbbc9"),
    "Qq": ("https://github.com/leanprover-community/quote4", "6a489d9af5d0c47e5b259e2e8bcdfc1811b5a259"),
    "batteries": ("https://github.com/leanprover-community/batteries", "f2effa3d803fda822b1f97b806c47cf2adfbcbc2"),
    "Cli": ("https://github.com/leanprover/lean4-cli", "e92c9f15fdfacc8536f31cfb3b7ad26c3c8cd204"),
}
def require(condition, message):
    if not condition:
        raise RuntimeError(message)
def command(args, cwd=ROOT):
    return subprocess.check_output(args, cwd=cwd, text=True).strip()
def canonical(url):
    return url[:-4] if url.endswith(".git") else url
require((ROOT/"lean-toolchain").read_text().strip()==LEAN, "Toolchain file differs from reviewed pin")
config=tomllib.loads((ROOT/"lakefile.toml").read_text())
manifest=json.loads((ROOT/"lake-manifest.json").read_text())
require(config.get("fixedToolchain") is True and manifest.get("fixedToolchain") is True, "fixedToolchain must be true")
require(manifest.get("packagesDir")==".lake/packages", "Unexpected dependency directory")
requires=config.get("require", [])
require(len(requires)==1 and requires[0].get("name")=="mathlib", "Unexpected direct dependencies")
require(requires[0].get("git")==EXPECTED["mathlib"][0] and requires[0].get("rev")==EXPECTED["mathlib"][1],
        "Direct mathlib source or revision differs from reviewed pin")
packages=manifest.get("packages", [])
require(len(packages)==len(EXPECTED) and {a["name"] for a in packages}==set(EXPECTED),
        "Missing, duplicated or unexpected locked package")
version=command(["lean","--version"])
require("version 4.34.1," in version and COMPILER in version, "Installed compiler differs from reviewed pin")
lake=command(["lake","--version"])
require("5.0.0-src+5045d00" in lake, "Installed Lake differs from reviewed pin")
print(version);print(lake)
for package in packages:
    name=package["name"]
    url, rev=EXPECTED[name]
    require(package.get("type")=="git" and package.get("subDir") is None, name+": unexpected source type/subdirectory")
    require(package.get("url")==url and package.get("rev")==rev, name+": locked source or revision differs from reviewed pin")
    if name=="mathlib":
        require(package.get("inputRev")==rev, "mathlib inputRev differs from reviewed direct revision")
    checkout=ROOT/manifest["packagesDir"]/name
    require(command(["git","rev-parse","HEAD"],checkout)==rev, name+": checkout revision differs")
    require(canonical(command(["git","remote","get-url","origin"],checkout))==canonical(url), name+": checkout origin differs")
    require(not command(["git","status","--porcelain","--untracked-files=all"],checkout), name+": source checkout is modified")
    print(name+": "+rev+" (reviewed source, clean checkout)")
nested=json.loads((ROOT/".lake/packages/mathlib/lake-manifest.json").read_text())
for package in nested["packages"]:
    require(package["name"] in EXPECTED, "Unexpected transitive package")
    url, rev=EXPECTED[package["name"]]
    require((package["url"],package["rev"])==(url,rev), package["name"]+": transitive lock differs")
require((ROOT/".lake/packages/mathlib/lean-toolchain").read_text().strip()==LEAN, "mathlib toolchain differs")
print("PASS: reviewed compiler, nine official origins, all revisions, direct/transitive lock agreement and clean sources.")

