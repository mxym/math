#!/usr/bin/env python3
"""Exact rational regressions from the independent boundary audit."""
import json
from fractions import Fraction as Q
def p2(n):return Q(2)**n
def radius(q,k,alpha,s1,u):
 e=Q(-alpha*(u+k),s1)
 if e.denominator!=1:raise RuntimeError('This exact test requires integral power')
 return (q*p2(-k)+1)*p2(-u)*p2(e.numerator)
checks={}
def check(name,condition,details):
 if not condition:raise RuntimeError(name)
 checks[name]=details
for u in [0,1,2,6,20,100]:
 cost=4*p2(u+2)*radius(1,0,0,1,u)
 check(f'alpha_zero_cost_U_{u}',cost==32,{'cost':str(cost),'threshold':'1','below_threshold':False})
for u in [6,20,100]:
 cost=4*p2(u+2)*radius(1,0,1,1,u)
 check(f'positive_alpha_cost_U_{u}',cost<1,{'cost':str(cost),'threshold':'1','below_threshold':True})
check('dropped_exponent_upper_bound',3<2*2 and Q(1,4)**6>radius(1,0,4,1,3),{'a':'1/4','z':2,'s':2,'s1':1,'alpha':4,'U':3,'k':0,'active':True,'error':str(Q(1,4)**6),'radius':str(radius(1,0,4,1,3))})
check('dropped_nonnegative_shift',-3<1*(-2) and Q(4)**7>radius(1,0,6,3,-3),{'a':'4','z':-2,'s':1,'s1':3,'alpha':6,'U':-3,'k':0,'active':True,'error':str(Q(4)**7),'radius':str(radius(1,0,6,3,-3))})
for x,e in [(Q(1,2),Q(1)),(-Q(1,2),-Q(1))]:
 check(f'doubled_open_buffer_{x}_{e}',abs(x)<1 and abs(e)<=1 and 1<abs(x+e)<2,{'inner_distance':str(abs(x)),'error':str(abs(e)),'outer_distance':str(abs(x+e))})
check('closed_inner_endpoint_breaks_outer',abs(Q(1))<=1 and abs(Q(1))<=1 and not abs(Q(1)+Q(1))<2,{'inner_distance':'1','error':'1','outer_distance':'2'})
check('strict_activation',not (1<Q(1)*2-1<3) and (1<Q(3,2)*2-1<3) and not (1<Q(2)*2-1<3),{'lower':False,'interior':True,'upper':False})

if len(checks)!=15:raise RuntimeError("incorrect arithmetic check count")
print(json.dumps({"status":"PASS","exact_arithmetic_regressions":checks},sort_keys=True,indent=2))
