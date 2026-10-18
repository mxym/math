#!/usr/bin/env python3
from pathlib import Path
import argparse,json
import reproduce as a
from audit_runtime import configure
from evidence import verify_run


def verify(directory):
    a.check_execution_inputs(False);configure(False);a.check_binding()
    out=Path(directory).resolve()
    if not out.is_relative_to((a.ROOT/'verification').resolve()):raise RuntimeError('Local evidence is outside owned D-backed output')
    result=verify_run(out,'D_BACKED_STORAGE_VERIFIED')
    execution=a.readj(out/'EXECUTION.json')
    if execution['guard']!='D_BACKED_STORAGE_VERIFIED'or execution['execution_inputs']!=a.readj(a.ROOT/'EXECUTION_INPUTS.json'):raise RuntimeError('Actual local execution inputs differ')
    return result

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('directory');args=ap.parse_args();print(json.dumps(verify(args.directory),indent=2))
