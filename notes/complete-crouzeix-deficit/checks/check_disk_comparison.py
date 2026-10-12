#!/usr/bin/env python3
"""Exact scalar algebra in the classical-input disk deduction; not operator proof."""
from fractions import Fraction as F
import json

def require(value, message):
    if not value:
        raise RuntimeError(message)

cases=0
for denominator in range(3, 61):
    for numerator in range(denominator//2+1, denominator):
        R=F(numerator,denominator)
        if not F(1,2)<R<1:
            continue
        s=(4*R*R-1)/(3*R*R)
        require(0<s<1, 'interpolation range')
        require((1-s)*(1-4*R*R)+s*(1-R*R)==0, 'exact contraction cancellation')
        require(1+3*s==5-1/(R*R), 'similarity factor squared')
        require(1<5-1/(R*R)<4, 'strict complete disk factor range')
        cases+=1
require(5-1/F(1,2)**2==1, 'continuous endpoint')
require(5-1/F(1)**2==4, 'boundary endpoint')
print(json.dumps({'status':'PASS','arithmetic':'fractions.Fraction; no floating point','interpolation_parameter_cases':cases,'endpoint_cases':2,'scope':'Exact scalar cancellation and parameter range in the similarity deduction. The classical similarity input and operator inequalities are justified in the written proof.'},indent=2,sort_keys=True))
