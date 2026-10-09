#!/usr/bin/env python3
"""Emit exact Nat/Int constructors, avoiding overloaded-numeral instance search.

This changes only literal elaboration. The resulting data are definitionally
identical to the original signed integer arrays; all kernel equality proofs
remain unchanged. No arithmetic procedure outside Lean is made an assumption.
"""
from __future__ import annotations
import argparse
import ast
import json
import re
from pathlib import Path

DEFINITION = re.compile(r'^def (\w+) : (CoefficientMerge|SparsePolynomial)\.Poly := (\[.*\])$', re.M)


def integer(c: int) -> str:
    if type(c) is not int:
        raise ValueError('Non-integer coefficient')
    return f'Int.ofNat (nat_lit {c})' if c >= 0 else f'Int.negSucc (nat_lit {-c-1})'


def natural(k: int) -> str:
    if type(k) is not int or k < 0:
        raise ValueError('Invalid monomial index')
    return f'nat_lit {k}'


def convert(source: str) -> tuple[str, int]:
    count = 0
    def replacement(match):
        nonlocal count
        name,namespace,literal = match.groups()
        if 'nat_lit' in literal:
            return match[0]
        data = ast.literal_eval(literal)
        terms=[]
        for key,c in data:
            if namespace == 'CoefficientMerge':
                monomial=natural(key)
            else:
                if not isinstance(key,list):
                    raise ValueError('Expected list monomial')
                monomial='['+', '.join(natural(k) for k in key)+']'
            terms.append(f'({monomial}, {integer(c)})')
        count += 1
        return f'def {name} : {namespace}.Poly := ['+', '.join(terms)+']'
    return DEFINITION.sub(replacement,source),count


def transform_dimension(root: Path, dimension: int):
    report=[]
    for path in sorted((root/f'APPT/Finite{dimension}Sparse').glob('*.lean')):
        source,count=convert(path.read_text())
        if count:
            path.write_text(source)
            report.append({'path':str(path.relative_to(root)),'literal_definitions':count})
    return report


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parent.parent)
    parser.add_argument('--dimensions',type=int,nargs='+',default=[9,12,15,18,21,24])
    args=parser.parse_args()
    report=[]
    for dimension in args.dimensions:
        report.extend(transform_dimension(args.root,dimension))
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
