#!/usr/bin/env python3
"""Direct original-monomial checks; these finite tests are not the proof."""
from itertools import combinations
from random import Random
def check(n,r,preset=None,seed=0):
 X=frozenset(range(n)); base=[frozenset(t) for t in combinations(range(n),r)];R=Random(seed)
 F=set();forbid=set();trace=[]
 for v in range(n):
  valid=[]
  for m in base:
   if v in m or m in forbid:continue
   new=frozenset((m-{t})|{v} for t in m)
   if not new&F:valid.append((m,new))
  trace.append(len(valid))
  if not valid:return trace
  if preset is not None and v<len(preset):
   selected=[z for z in valid if z[0]==preset[v]]
   if len(selected)!=1:raise ValueError("bad designated prefix")
   m,new=selected[0]
  else:m,new=R.choice(valid)
  F.add(m);forbid.update(new)
 return trace
def main():
 X=frozenset(range(8)); fano=[X-{i,(i+1)%7,(i+3)%7} for i in range(7)]
 tr=check(8,5,preset=fano)
 assert len(tr)==8 and all(tr[:7]) and tr[7]==0
 print("PASS n=8, r=5: seven legal choices and zero final choices; all 21 candidates fail.")
 print("Counts of currently valid candidates at the eight successive stages:",tr)
 for n in range(9,14):
  for i in range(20):
   rr=check(n,n-3,seed=i)
   assert len(rr)==n and min(rr)>0
 print("Smoke test only: 100 deterministic prefixes completed for n=9..13. Uniform n>=9 is analytical (PROOF.md).")
if __name__=="__main__":main()
