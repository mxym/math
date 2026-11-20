"""Verify the 16 finite infeasibility certificates using integers only."""
from pathlib import Path
import gzip,json
from model import build,specs,check
def verify_model(model,cert):
 A,b,U,q,ae,au=model;acc=[0]*A.shape[1];value=0
 for M,bb,ids,terms,eq in ((A,b,ae,cert['u'],True),(U,q,au,cert['v'],False)):
  by={t:j for j,t in enumerate(ids)};used=set()
  for tag,c in terms:
   tag=tuple(tag);check(tag in by and tag not in used,'invalid row key');used.add(tag)
   check(type(c)==int and (eq or c<0),'invalid multiplier');j=by[tag]
   value+=c*int(bb[j])
   for ptr in range(M.indptr[j],M.indptr[j+1]):acc[M.indices[ptr]]+=c*int(M.data[ptr])
 lo=value-sum(max(0,s)for s in acc)
 check(type(cert['lower'])==int and lo==cert['lower'] and lo>0,'certificate failed')
 return lo
def main():
 src=Path(__file__).resolve().parent/'certs';expected=set()
 for tw in (0,1):
  for sp,size in specs(tw):
   tag='%d-%d%d%d'%(tw,*sp);expected.add(tag+'.json.gz');obj=json.loads(gzip.decompress((src/(tag+'.json.gz')).read_bytes()))
   M=build(tw,sp);val=verify_model(M,obj);print(tag,'class size',size,'columns',M[0].shape[1],'rows',M[0].shape[0],M[2].shape[0],'lower',val,flush=True)
 check({p.name for p in src.iterdir()}==expected,'certificate list mismatch')
 print('PASS: 16 representatives, both sets of 64 labeled profiles; every integer lower bound positive.')
if __name__=='__main__':main()
