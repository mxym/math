#!/usr/bin/env python3
"""Retain the independently inventoried original 158 and seven-module 10 declarations."""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parent.parent
old=json.loads((ROOT/'baseline/75-independent-declaration-inventory.json').read_text())
new=json.loads((ROOT/'declaration-inventory.json').read_text());byname={row['name']:row for row in new}
if len(old)!=168 or sum(not row['module'].startswith('Mxym.StochasticRigidity') for row in old)!=158:
 raise RuntimeError('Unexpected independent prior declaration inventory')
for row in old:
 if row['name'] not in byname:raise RuntimeError('Missing prior declaration: '+row['name'])
 current=byname[row['name']]
 for field in ['module','kind','unsafe','partial','private','type','axioms']:
  a,b=row[field],current[field]
  if field=='axioms':a,b=sorted(a),sorted(b)
  if a!=b:raise RuntimeError('Prior declaration '+field+' changed: '+row['name'])
print('PASS: all original 158 compiler declarations and all 10 stochastic declarations retain exact types/kinds/axiom sets/flags.')
