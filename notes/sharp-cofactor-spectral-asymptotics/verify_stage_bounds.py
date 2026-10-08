#!/usr/bin/env python3
"""Exact rational certification of the rank-two factorial exclusion thresholds."""
import math,json
from fractions import Fraction
from pathlib import Path
if not __debug__:raise SystemExit('Optimized Python is not allowed.')
e_upper=Fraction(87,32)
series_bound=sum((Fraction(1,math.factorial(k)) for k in range(7)),Fraction(0))+Fraction(8,7*math.factorial(7))
assert series_bound<e_upper
out=[]
for m,k in [(7,2),(4,3),(3,7)]:
 gap=math.factorial(m*k+1)*32**(m*k)-math.factorial(m)*math.factorial(k)**m*87**(m*k)
 assert gap>0
 out.append({'m':m,'k':k,'integer_positive_gap':str(gap)})
s=json.dumps({'e_upper':'87/32','series_plus_geometric_tail_bound':str(series_bound),'all_thresholds_pass':True,'thresholds':out,'arithmetic':'Python integers and fractions only'},indent=2)+'\n'
Path(__file__).with_name('STAGE_BOUNDS_EXACT_RESULT.json').write_text(s);print(s,end='')
