#!/usr/bin/env python3
"""Emit integer leaf witnesses from the pinned authors' eight-point checker."""
from pathlib import Path
import sys

if not __debug__: raise RuntimeError("run without -O")
source = Path(sys.argv[1]).read_text(encoding="utf-8")
patches = [
 [
  "import itertools,sys,time,math",
  "import itertools,sys,time,math,json\ndef audit(*v): print('AUD '+json.dumps(v),flush=True)"
 ],
 [
  " SY=np.zeros((len(sym),ne))",
  " audit('start',list(G),[[int(a),int(b)] for a,b in sym],int(chief) if chief is not None else None,tar)\n SY=np.zeros((len(sym),ne))"
 ],
 [
  "  gco=[0]*ne;gc=0;wco=[0]*ne",
  "  gco=[0]*ne;gc=0;wco=[0]*ne;aw=[];asym=[];av=[]"
 ],
 [
  "    t=round(D*v0);w=list(map(int,Ws[WI[ii]]));tweight+=t;diag+=t*sum(c*c for c in w)",
  "    t=round(D*v0);w=list(map(int,Ws[WI[ii]]));tweight+=t;diag+=t*sum(c*c for c in w);aw.append([t,w])"
 ],
 [
  "    a,b=sym[ii-swi];t=round(D*v0);gco[a]+=t;gco[b]-=t",
  "    a,b=sym[ii-swi];t=round(D*v0);gco[a]+=t;gco[b]-=t;asym.append([t,int(a),int(b)])"
 ],
 [
  "    v=list(map(int,Ps[PI[ii-swi-ss]]));norm=sum(c*c for c in v);t=round(D*v0/norm);gc+=t*norm",
  "    v=list(map(int,Ps[PI[ii-swi-ss]]));norm=sum(c*c for c in v);t=round(D*v0/norm);gc+=t*norm;av.append([t,v])"
 ],
 [
  "  return (upper*10**6<=tar*tweight*H)if tweight else upper<0",
  "  ok=(upper*10**6<=tar*tweight*H)if tweight else upper<0\n  if ok:audit('close',lo.tolist(),hi.tolist(),ls.tolist(),bs.tolist(),aw,asym,av)\n  return ok"
 ],
 [
  "  if lo is None:stats[0]+=1;return True",
  "  if lo is None:audit('sphere');stats[0]+=1;return True"
 ],
 [
  "  if np.any(lo>hi):stats[0]+=1;return True",
  "  if np.any(lo>hi):audit('order');stats[0]+=1;return True"
 ],
 [
  "  return go(lo,h,ww,pp,depth+1) and go(l,hi,ww,pp,depth+1)",
  "  audit('split',lo.tolist(),hi.tolist(),e,t)\n  return go(lo,h,ww,pp,depth+1) and go(l,hi,ww,pp,depth+1)"
 ]
]
for before, after in patches:
    if source.count(before) != 1:
        raise RuntimeError("expected exactly one occurrence: " + repr(before))
    source = source.replace(before, after, 1)
filename = sys.argv[1]
sys.argv = [filename]
ns = {"__name__": "__main__", "__file__": filename}
exec(compile(source, filename, "exec"), ns)
