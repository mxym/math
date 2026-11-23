"""Native original Hoffman-mass floors and graph charge-(2,32) caps."""
from fractions import Fraction
from math import ceil
from pathlib import Path
from original_site_populations import calc
import json
def check(rank,rows):
 o,w,c,g,u,ub,red=calc(rank,[],export=True)
 extra=w((1,23))-99*o-7*w((0,14))
 d={str(k):v for k,v in ub.items()}
 d.update({'444':w((4,44)), 'Waff':w((3,39))-231*o-22*w((2,22))-extra})
 if rank==42:d['-compat(-4, 46, -1)']=(-1)*d['compat(-4, 46, -1)']
 for tag in ['CM','minus232']:
  if tag=='CM':
   tgt=c((2,22));ab=({18,127,228,230,337} if rank==40 else {16,18,228,230,337})
  else:tgt=(-1)*g((2,32));ab={18,121,127,228,230,337}
  tab=dict(d)
  for h in ab:tab['abs'+str(h)]=(-1)*u[divmod(h,100)]
  n,k,weights=rows[tag];assert n>0 and len(weights)==len(dict(weights))
  assert {name for name,aa in weights if name.startswith('abs')}=={'abs'+str(h)for h in ab}
  z=n*tgt-k*o
  for j,aa in weights:
   assert type(aa)is int and aa>0;z-=aa*tab[j]
  assert not any(red(z))
  out=ceil(Fraction(k,n))
  assert out==(78 if tag=='CM' else (-1575 if rank==40 else -252))
  print(rank,tag,'>=',out,'if absent:',sorted(ab))
if __name__=='__main__':
 d=json.loads(Path(__file__).with_name('hoffman-fano-large-family.json').read_text())
 for r in (40,42):check(r,d[str(r)])
