#!/usr/bin/env python3
"""Read-only run artifact validation. This does not rerun Lean or certify a proof."""
from pathlib import Path
import argparse,json,sys
sys.dont_write_bytecode=True
from release_integrity import validated_snapshot,ReleaseIntegrityError
ROOT=Path(__file__).resolve().parents[1]
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);ap.add_argument('--expect-manifest-sha256');a=ap.parse_args()
    validated_snapshot(ROOT)
    from output_integrity import verify_outputs
    print(json.dumps(verify_outputs(a.output,ROOT,a.expect_manifest_sha256),sort_keys=True))
if __name__=='__main__':
    try:main()
    except (ReleaseIntegrityError,OSError,ValueError,KeyError,RuntimeError) as e:print(str(e),file=sys.stderr);sys.exit(1)
