"""Run alongside rooted-unsaturated-dyadic.py (the 230-orbit atlas)."""
from pathlib import Path
from runpy import run_path
atlas = run_path(str(Path(__file__).with_name('rooted-unsaturated-dyadic.py')))
lower, pairs, shapes = (atlas[k] for k in ('lower', 'pairs', 'shapes'))
from itertools import chain

def ok(j,v):
    xs=list(chain.from_iterable(v))
    return lower(v)<=16*j and (16*j+sum((xs[i]+xs[k])**2 for i,k in pairs)+96*sum(xs))%128==0
def check(j,v,c,o,at):
    xs=list(chain.from_iterable(c));ls=list(chain.from_iterable(v))
    assert all((a-b)%8==0 for a,b in zip(xs,ls))
    assert all((3*xs[i]-xs[i^1]-o)%8==0 for i in range(14))
    assert (3*o-sum(xs))%8==0 and (o+sum(xs))%8==0
    a=(o+sum(xs))//8
    n=16*j+7*sum(3*u*u-2*u*w+3*w*w for u,w in c)+35*o*o-112*a*o+128*a*a
    assert (a,n)==(at[0],64*at[1])
def main():
    z=(0,0);v1=((0,2),)*4+((1,5),)+((7,7),)*2
    v2=(z,)*6+((4,4),);v3=(z,)*3+((2,6),)*4;v4=((0,4),)*3+((1,7),)*4
    expected={22:set(),23:{v1},24:{(z,)*7,v2,v3,v4},25:set()}
    vals=list(shapes())
    for j in expected: assert {v for v in vals if ok(j,v)}==expected[j]
    check(23,v1,((0,2),)*4+((1,5),)+((-1,-1),)*2,6,(2,26))
    check(24,v2,(z,)*6+((-4,4),),0,(0,20));check(24,v3,(z,)*3+((2,-2),)*4,0,(0,20))
    check(24,v4,((0,-4),)*3+((1,-1),)*4,-4,(-2,28))
    print('A22=A25=0 universally; A23,A24 follow from the three stated raw shell absences.')
if __name__=='__main__': main()
