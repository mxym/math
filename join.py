#!/usr/bin/env python3
"""Join exact integer Walsh-histogram certificates to the complete quartic restriction type list."""
from pathlib import Path
from collections import defaultdict
import numpy as np
import sys
directory=Path(sys.argv[1]) if len(sys.argv)>1 else Path('.')
SP=[];HD=[]
for l in (directory/'spectrum.txt').read_text().splitlines():
 if ';' not in l:continue
 k,m,h=l.split(';');SP.append(list(map(int,k.strip().split())));HD.append([int(z)>0 for z in h.strip().split()[2:]])
SP=np.array(SP,dtype='int32');HD=np.array(HD);O=SP[:,1::2].sum(axis=1)>0
# bin 11: number of generic even spectra (0 or 64 coefficients with half-unit odd).
SP=np.column_stack([SP,(SP[:,2]+SP[:,6]+SP[:,10])//64, SP[:,0]-SP[:,4], SP[:,0]-2*SP[:,4]])
# minimum and maximum over the allowed local spectrum patterns, for each bin and each head
def build(odd):
 a=[];b=[];allow=[]
 for j in range(12):
  sub=SP[HD[:,j] & (O==odd)];allow.append(1 if not len(sub) else 0)
  a.append(sub.min(axis=0) if len(sub) else np.zeros(SP.shape[1]))
  b.append(sub.max(axis=0) if len(sub) else np.zeros(SP.shape[1]))
 return np.array(a,dtype='int32'),np.array(b,dtype='int32'),np.array(allow,dtype='int32')
lE,hE,nE=build(False);lO,hO,nO=build(True)
spec=[]
for i,l in enumerate((directory/'histograms.txt').read_text().splitlines()):
 p,c=l.split(';');p,z,ng,*Hs=map(int,p.split());c=list(map(int,c.split()))
 if Hs[4]==256:continue # bent is already known to satisfy the conjecture.
 spec.append((i,p,z,np.array(c+[ng,c[0]-c[4],c[0]-2*c[4]],dtype='int32')))
M=np.array([[(i&j).bit_count()%2 for j in range(1,256)] for i in range(1,256)],dtype='int32')
def main(simple=False):
 for l in (directory/'headers.txt').read_text().splitlines()[1:]:
  i,p,h=l.split();i=int(i);p=int(p);h=np.array([int(z,16) for z in h]);f=np.bincount(h,minlength=12)
  one=np.eye(12,dtype='int32')[h];o2=M@one # for each nonzero linear form, the number of each head in its nonzero coset
  for z in (0,255,256):
   odd={0:np.zeros((1,12),dtype='int32'),255:f[np.newaxis,:],256:2*o2}[z]; even=2*f-odd
   ok=(odd@nO+even@nE)==0;lo=odd@lO+even@lE;hi=odd@hO+even@hE
   for j,pf,zo,c in spec:
    if pf!=p or z!=zo:continue
    n=12 if simple else 14
    keep=ok & np.all((lo[:,:n]<=c[:n])&(c[:n]<=hi[:,:n]),axis=1)
    for x in np.flatnonzero(keep):yield int(i),j,(int(x+1) if z==256 else 0)
if __name__=='__main__':
 from collections import Counter
 lst=list(main());r=Counter(j for i,j,l in lst);print('# surviving non-bent (head,histogram,linear residue) triples:',len(lst),'heads',len(set(i for i,j,l in lst)),'histograms',dict(r))
 for row in lst:print(*row)
 assert lst==[(130,7,0)]
 from collections import Counter
 assert Counter(i for i,j,l in main(True))=={130:1,134:15,168:1,358:1,563:3}
