"""Verify the explicit arithmetic/16-row nonzero-isotropic obstruction. Standard library only."""
from itertools import product
from math import comb
from collections import Counter
Q=[]
for a,b,c,e in product(range(3),range(7),range(7),range(2)):
 if a+b+c>6 or a+e>2 or a+b==5: continue
 if (43-18*a-4*(a+b)-6*c-60*e)%7:continue
 F=comb(c,2)+b*c+(e-2)*c+2*comb(a,2)
 assert F>=0
 Q.append((a,b,c,e,F))
assert len(Q)==16
assert [q[-1] for q in Q]==[0,3,0,0,0,10,2,2,0,2,0,2,0,5,0,3]
cc,bc,ec,c,aa=3*6+12*7,6*4+24*3,6*2,6*2*10,3*(1-1)+12*(2-1)
assert (cc,bc,ec,c,aa)==(102,96,12,120,12)
assert cc+bc+ec-2*c+2*aa==-6
print('All sixteen would-be zero-row profiles have F>=0; actual sum F=-6.')
