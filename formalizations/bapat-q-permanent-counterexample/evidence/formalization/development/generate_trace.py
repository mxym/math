#!/usr/bin/env python3
"""Generate arithmetic witnesses; all transitions are subsequently kernel checked."""
from pathlib import Path
import csv, hashlib, json, sys

ROOT = Path(__file__).resolve().parent.parent
raw = (ROOT / 'reference/counterexample_vectors_n200.csv').read_bytes()
assert hashlib.sha256(raw).hexdigest() == '9d16617d6eb287535a752cf5ef6f3d4672a133812bf0fbd908738a10c223fc25'
rows = list(csv.DictReader(raw.decode().splitlines()))
V = [((int(r['a_real']), int(r['a_imag'])), (int(r['b_real']), int(r['b_imag']))) for r in rows]
assert len(V) == 200
Z = (0, 0)
def addz(x,y): return (x[0]+y[0], x[1]+y[1])
def mulz(x,y): return (x[0]*y[0]-x[1]*y[1], x[0]*y[1]+x[1]*y[0])
def negz(x): return (-x[0],-x[1])
def add(p,q): return [addz(p[k] if k<len(p) else Z,q[k] if k<len(q) else Z) for k in range(max(len(p),len(q)))]
def scale(z,p): return [mulz(z,c) for c in p]
def sub(p,q): return add(p,[negz(c) for c in q])
def deriv(p): return [mulz((k,0),p[k]) for k in range(1,len(p))]
def mullinear(a,b,p): return add(scale(a,p),[Z]+scale(b,p))
states = [([(1,0)], [])]
for m,(a,b) in enumerate(V):
 f,s = states[-1]
 ds=deriv(f)
 states.append((mullinear(a,b,f),sub(add(mullinear(a,b,s),scale(b,sub(scale((m,0),f),[Z]+ds))),scale(a,ds))))
certificate=json.loads((ROOT/'reference/independent_certificate.json').read_text())
assert states[-1][0]==[tuple(x) for x in certificate['F_coefficients']]
assert states[-1][1][:199]==[tuple(x) for x in certificate['S_coefficients']]
assert all(x==Z for x in states[-1][1][199:])
def coeffs(p): return '['+', '.join(f'⟨{r}, {i}⟩' for r,i in p)+']'
header=['import BapatExactCoefficients','','set_option autoImplicit false','set_option maxRecDepth 100000','set_option maxHeartbeats 0','','namespace BapatRankTwo.N200','open Exact','','/-- Exactly the 200 published CSV rows, without reordering. -/','def vectors : List (GI × GI) := [']
header += [f'  (⟨{a[0]}, {a[1]}⟩, ⟨{b[0]}, {b[1]}⟩)'+(',' if i<199 else '') for i,(a,b) in enumerate(V)]
header += [']','','theorem vectors_length : vectors.length = 200 := rfl','','end BapatRankTwo.N200','']
(ROOT/'development/BapatN200Data.lean').write_text('\n'.join(header))
limit=int(sys.argv[1]) if len(sys.argv)>1 else 200
lines=['import BapatN200Data','','set_option autoImplicit false','set_option maxRecDepth 100000','set_option maxHeartbeats 0','','namespace BapatRankTwo.N200','open Exact','']
for m,(f,s) in enumerate(states[:limit+1]):
 name=f'checkpoint_{m:03d}'
 lines += [f'def {name} : Coeffs × Coeffs :=',f'  ({coeffs(f)},',f'   {coeffs(s)})','',f'theorem state_eq_{m:03d} : state (vectorAt vectors) {m} = {name} := by']
 if m==0: lines += ['  rfl']
 else: lines += [f'  rw [state, state_eq_{m-1:03d}]','  decide +kernel']
 lines += ['']
if limit==200:
 lines += ['noncomputable def permanentNorm : ℤ := fischerInt 200 checkpoint_200.1','noncomputable def wedgeNorm : ℤ := fischerInt 198 checkpoint_200.2','','/-- Full integer gap, checked only by Lean kernel reduction. -/','theorem norm_gap_positive : 19900 * permanentNorm < wedgeNorm := by','  decide +kernel','']
lines += ['end BapatRankTwo.N200','']
(ROOT/'development/BapatN200Trace.lean').write_text('\n'.join(lines))
print({'transitions':limit,'bytes':(ROOT/'development/BapatN200Trace.lean').stat().st_size,'final_coefficient_lists_match_public_certificate':True})
if limit == 200:
 # Bound Lean elaborator memory: four consecutive blocks of fifty transitions.
 # The imported preceding theorem connects every block to the original input.
 starts=[0,51,101,151]
 ends=[50,100,150,200]
 for block,(start,end) in enumerate(zip(starts,ends)):
  imp='BapatN200Data' if block==0 else f'BapatN200Trace{block-1}'
  out=[f'import {imp}','','set_option autoImplicit false','set_option maxRecDepth 100000','set_option maxHeartbeats 0','','namespace BapatRankTwo.N200','open Exact','']
  for m in range(start,end+1):
   f,s=states[m]
   out += [f'def checkpoint_{m:03d} : Coeffs × Coeffs :=',f'  ({coeffs(f)},',f'   {coeffs(s)})','',f'theorem state_eq_{m:03d} : state (vectorAt vectors) {m} = checkpoint_{m:03d} := by']
   out += ['  rfl'] if m==0 else [f'  rw [state, state_eq_{m-1:03d}]','  decide +kernel']
   out += ['']
   if m%10==0: out += [f'#check state_eq_{m:03d}','']
  out += ['end BapatRankTwo.N200','']
  (ROOT/f'development/BapatN200Trace{block}.lean').write_text('\n'.join(out))
 out=['import BapatN200Trace3','','set_option autoImplicit false','set_option maxRecDepth 100000','set_option maxHeartbeats 0','','namespace BapatRankTwo.N200','open Exact','','noncomputable def permanentNorm : ℤ := fischerInt 200 checkpoint_200.1','noncomputable def wedgeNorm : ℤ := fischerInt 198 checkpoint_200.2','','theorem norm_gap_positive : 19900 * permanentNorm < wedgeNorm := by','  decide +kernel','','end BapatRankTwo.N200','']
 (ROOT/'development/BapatN200Trace.lean').write_text('\n'.join(out))
