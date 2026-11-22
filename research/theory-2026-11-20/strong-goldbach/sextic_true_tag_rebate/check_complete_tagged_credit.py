#!/usr/bin/env python3
"""Strict signed upper for all remaining higher ranks in the actual tag chamber."""
from fractions import Fraction as F
from math import factorial as f
from pathlib import Path
from runpy import run_path

def require(ok):
 if not ok:raise ArithmeticError("complete tagged chamber certificate failed")

a=F(".110")
n=0; B9=F(0)
for i in range(3,58):
 u=F(i+1,500)
 for j in range(i+1,65):
  v=F(j+1,500);s=u+v
  if s-F(".004")<=F(".065") or s>F(".170") or v>=a:continue
  T=1-s+F(".004")
  w9=16896*(T/7)**2+322560*(T/7)**4
  require(w9<410)
  B9+=w9*(T-7*a)**6/(f(7)*f(6)*a**7*500**2)
  n+=1
require(n==961 and B9<F(".00000918"))
U=F(410)*F(2)/F(".329")*F(n,500**2)
require(U<F("9.581"))
require(2*B9*U<F(".000176"))
pos=run_path(str(Path(__file__).with_name('check_tagged_negative_credit.py')),
             run_name='__main__')['res']
require(pos>F(".15686") and pos-2*B9*U>F(".156"))
print('ordinary absolute rank-nine mass, true positive uniform receiver:', float(B9),float(U))
print('strict complete signed chamber lower:',float(pos-2*B9*U))
