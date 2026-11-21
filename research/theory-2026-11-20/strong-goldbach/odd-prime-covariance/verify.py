#!/usr/bin/env python3
"""Build/run the finite upper cubature and check all thresholds over Q."""
from fractions import Fraction as F
from math import comb, factorial as fac
import os, subprocess, tempfile
from pathlib import Path
here=Path(__file__).resolve().parent
expected={(5,224,0):3818069,(7,64,0):276050,(7,64,1):276050}
ledger={(5,224,0):(1548649460784975336313262500,1856198965985280000000000000),
        (7,64,0):(6639968841975281434099343180383442248,1021416395487628492800000000000000000000),
        (7,64,1):(37496824479853097264877986874445249536,1021416395487628492800000000000000000000)}
def check(x,msg):
    if not x: raise RuntimeError(msg)
with tempfile.TemporaryDirectory() as tmp:
    exe=Path(tmp)/'cells'
    subprocess.run([os.environ.get('CXX','c++'),'-std=c++17','-O3',str(here/'cubes.cpp'),'-lgmpxx','-lgmp','-o',str(exe)],check=True)
    vals={}
    for (j,K,pos),count in expected.items():
        p=subprocess.run([str(exe),str(j),str(K),str(pos)],capture_output=True,text=True,check=True)
        tag,jj,kk,rows,mass,num,den=map(int,p.stdout.split())
        check((tag,jj,kk,rows,mass)==(pos,j,K,count,K**(j-1)),p.stdout)
        check((num,den)==ledger[j,K,pos], "physical envelope ledger disagreement: "+p.stdout)
        vals[j,pos]=F(num,den)
k=F(333,4000)
def tail(j):
    return 4*comb(j-2,(j-2)//2)*(1/k-j)**(j-1)/(j*(1-(j-1)*k)*fac(j-1)**2)
hi=tail(9)+tail(11)
r5=vals[5,0]; neg=vals[7,0]+hi; pos=vals[7,1]+hi
check(r5<F(835,1000),'rank 5 negative')
check(neg<F(67,10000),'rank >=7 negative')
check(pos<F(37,1000),'rank >=7 positive')
check(r5+neg<F(842,1000),'entire adverse physical prime side')
check(1/(2*k*5040)+F(1,2)<F(502,1000),'hard ordinary mean upper')
check(F(1,2)-(F(1,720)+F(1,5040))/(2*k)>F(49,100),'hard ordinary mean lower')
print('Exact upper bounds (negative rank 5, negative >=7, positive >=7):')
print(r5,neg,pos,sep='\n')
