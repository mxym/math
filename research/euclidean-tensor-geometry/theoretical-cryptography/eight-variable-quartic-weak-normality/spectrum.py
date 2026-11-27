#!/usr/bin/env python3
"""Derive and independently recompute the complete absolute spectrum table of the GLP cover."""
import sys,hashlib,itertools
from collections import Counter
from pathlib import Path
import numpy as np

def terms(s): return tuple(sum(1<<(ord(c)-97) for c in t) for t in s[4:].strip().split('+') if t and t!='0')
def parse(p): return [terms(s) for s in Path(p).read_text().splitlines() if s.startswith('anf=')]
def md(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def header(t): return tuple(sorted(u for u in t if u.bit_count()==4))
def ht(x):
 w=x.copy()
 for n in [1,2,4,8,16,32,64]:
  z=w.reshape(-1,2*n);a=z[:,:n].copy();b=z[:,n:].copy();z[:,:n]=a+b;z[:,n:]=a-b
 return w
def main(raw,q7):
 assert md(raw)=='fc58fe0b3b11b67056ebb5f49c58aea8b338edb8d9cda9313d15494850dc7c80'
 rec=parse(raw); reps=[header(t) for t in parse(q7)]; assert len(rec)==39952 and len(reps)==12
 n=len(rec);anf=np.zeros((n,128), dtype='int16')
 for i,r in enumerate(rec): anf[i,list(r)]=1
 vals=np.arange(128);mono=np.stack([(vals&m)==m for m in vals]).astype('int16')
 truth=(anf@mono)&1
 y=1-2*truth
 coef=ht(y); chars=np.array([[1-2*((x&y).bit_count()%2) for x in range(128)] for y in range(128)],dtype='int16')
 # Second route: independently evaluate ANFs through an in-place subset transform:
 truth2=anf.copy()
 for s in [1,2,4,8,16,32,64]:
  v=truth2.reshape(-1,s*2);v[:,s:]^=v[:,:s]
 assert np.array_equal(truth,truth2)
 # direct signed dot products, not a butterfly
 assert np.array_equal(coef,(1-2*truth2)@chars)
 specs=Counter(); accum=Counter()
 for r,v in zip(rec,coef):
  assert np.max(np.abs(v))<=40 and np.all(v%4==0)
  k=tuple(np.bincount(np.abs(v)//4,minlength=11)); assert sum(k)==128
  h=reps.index(header(r)); specs[k]+=1;accum[h,k]+=1
 print('h | counts of |W|=0,4,...,40 | row multiplicity')
 for k,c in sorted(specs.items()):
  print(' '.join(map(str,k)),';',c,'; by header', ' '.join(str(accum[h,k]) for h in range(12)))
 assert len(specs)==14
if __name__=='__main__': main(*sys.argv[1:])
