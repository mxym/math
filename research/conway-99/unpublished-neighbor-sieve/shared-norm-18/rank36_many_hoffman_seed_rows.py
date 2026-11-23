"""Verify original rank36 C222/N18 joint lower bounds on the 230–337 face."""
from fractions import Fraction as Q
from original_site_populations import calc
from math import ceil
import json
from pathlib import Path
def check():
 o,w,c,g,u,ub,red=calc(36,[],export=True); p=2402
 N=p*u[0,18]; M=c((2,22))
 # Reproduce the Ct tangent on literal original Y2 and zero-class cocliques.
 y2=c((0,28))+2*c((3,39)); t=34
 Ct=9*y2+18*c((0,14))-(369+10*t)*M+(5*t*t-4158)*o
 D={**{str(k):v for k,v in ub.items()},'root':(-1)*g((0,14)),'444':w((4,44)),
    "SC('u', (3, 37))":u[3,37],"SC('Ct', 34)":Ct,'nest':29842*o-N}
 absent={16,121,125,127,226,228}
 for h in absent:D['abs'+str(h)]=(-1)*u[divmod(h,100)]
 data=json.loads(Path(__file__).with_name('rank36-many-hoffman-seed-rows.json').read_text())
 assert len(data)==2
 for (den,num,terms),v in zip(data,[M,N]):
  assert den>0 and num>0 and len(terms)==len(dict(terms))
  row=den*v-num*o
  for k,a in terms:
   assert k in D and isinstance(a,int) and a>0
   row-=a*D[k]
  assert not any(red(row))
 assert (ceil(Q(data[0][1],data[0][0])), 2*ceil(Q(data[1][1],2*data[1][0])))==(23,27820)
 print('Rank36: original C222 >= 23 and oriented N18 >= 27820.')
if __name__=='__main__':check()
