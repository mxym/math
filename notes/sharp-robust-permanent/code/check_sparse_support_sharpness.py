#!/usr/bin/env python3
"""Exact sharpness witness for the m+2 support theorem at (n,k)=(11,4).

No scipy, no optimization, and no imported fixed-certificate checker.
Uses standard-library rational arithmetic and the proven integer transfer recurrence.
"""
from fractions import Fraction
from pathlib import Path
from json import loads
from check_universal_max_minors import profiles, column, det_int

n,m=11,4
record=loads((Path(__file__).resolve().parents[1]/
   'certificates'/'four_subset_n8_64.json').read_text(encoding='utf-8'))['degrees'][n-8]
lam=list(map(Fraction,record['dual']))
low,high=Fraction(record['lower']),Fraction(record['upper'])
T=profiles(n,m)
H=[];L=[]
for typ in T:
    F=column(n,m,typ)
    h=Fraction(typ==(n,0,0,0))-sum(lam[j]*F[j+1] for j in range(m))
    assert low<=h<=high
    if h==high:H.append(typ)
    if h==low:L.append(typ)
assert len(H)==len(L)==3,(H,L)
assert (n,0,0,0) in H

selected=((n,0,0,0),)+tuple(sorted(set(H+L)-{(n,0,0,0)}))
assert len(selected)==6
V=[column(n,m,t) for t in selected]
cof=[]
for j in range(6):
    sub=[[V[i][r] for i in range(6) if i!=j] for r in range(5)]
    cof.append((-1)**j*det_int(sub))
assert all(c!=0 for c in cof)
assert all(sum(cof[j]*V[j][i] for j in range(6))==0 for i in range(5))
ratio=Fraction(2*abs(cof[0]),sum(abs(x) for x in cof))
assert ratio==Fraction(record['C'])==Fraction(1629,4549)
assert high-low==ratio

# Stronger than 'there exists a 6-profile certificate': every signed
# optimum can only use the 6 contact types, and their 5x6 integer
# matrix has 1-D kernel with all six cofactor coordinates nonzero.
print('PASS n=11 k=4 EXACT CONTACT CLASSES: upper',H,'lower',L)
print('PASS full-rank six-type cofactor kernel:',cof)
print('PASS unique full-support circuit, optimal value:',ratio)
print('SHARP m+2 SUPPORT BOUND CERTIFIED')
