"""Verified rank-36 must-hit sets and rational controls; no numerical solver.\n\nRun from a checkout with python-flint next to higher_moments.py.\n"""
from fractions import Fraction as Q
from math import lcm
from pathlib import Path
import runpy, sys
from flint import fmpq_mat
from higher_moments import rows, projections, SHIFTS
from rank36_three_types import UNIT

P=2402

def integer(r):
    de=lcm(*(Q(x).denominator for x in r))
    return [int(de*x) for x in r]

def engine():
    allowed=set(UNIT)
    # In all rows a vector slot is a linear form on the following raw variables.
    raw=rows()
    keys=sorted(set().union(*raw,*(projections(sh,n) for sh in (None,*SHIFTS) for n in (1,2,3))))
    cols=keys+['N14','X14','M0']; n=len(cols)
    def e(k):
        return [int(h==k) for h in cols]
    def add(*vs):
        return [sum(z) for z in zip(*vs)]
    def times(z,v):
        return [z*x for x in v]
    def lin(*terms):
        return add(*(times(c,e(k)) for c,k in terms))
    one=e((0,0))
    ch=[((1,25),(0,16),8),((1,27),(0,18),9),((1,27),(2,26),2),((0,26),(1,21),8)]
    eq=[]
    for r in raw:
        # The source checker exports unit counts but our W coordinates are raw.
        z=dict(r)
        for target,src,mul in ch:z[src]=z.get(src,0)-mul*r.get(target,0)
        eq.append([z.get(k,0) for k in cols])
    for k in sorted(UNIT-allowed):
        eq.append(lin((1,k),*((-m,s) for target,s,m in ch if target==k)))
    reg={0:one,7:e('N14'),8:times(P,e((0,16))),9:times(P,e((0,18))),
         10:times(P,e((0,20))),11:lin((P,(0,22)),(2*P,(3,33))),
         12:lin((P,(0,24)),(2*P,(3,35))),13:lin((P,(0,26)),(2*P,(3,37))),
         14:e('X14')}
    path=Path(__file__).resolve().parents[2]/'maximal-marked-lattice'/'verify.py'
    b=runpy.run_path(str(path))['fourier_basis']()
    # Convert echelon basis to the one whose first 15 X coefficients are the coordinate units.
    for i in reversed(range(15)):
        x,y=b[i]
        for j in range(i+1,15):
            u,v=b[j];a=x[j];x=[h-a*k for h,k in zip(x,u)];y=[h-a*k for h,k in zip(y,v)]
        b[i]=x,y
    def X(j):return add(*(times(b[i][0][j],v) for i,v in reg.items()))
    def Y(j):return add(*(times(7**7*b[i][1][j],v) for i,v in reg.items()))
    yH=lin((1000,(0,0)),(-8,(0,14)),(200,(0,16)),(88,(0,18)),(64,(0,20)),
           (24,(0,22)),(48,(3,33)),(8,(0,24)),(16,(3,35)))
    eq.extend([add(Y(0),times(-1,one)),
               add(e('N14'),times(P-1,Y(1)),times(-P,e((0,14)))),
               add(e('X14'),times(P-1,Y(2)),times(-P,yH))])
    M=e((2,22));M0=e('M0');m=add(times(P,M),times(1-P,M0))
    S=lin((1,(1,23)),(-99,(0,0)),(-7,(0,14)))

    u={k:lin((1,k),*((-d,s) for q,s,d in ch if q==k)) for k in UNIT}
    # eq*r=0; rref of all equations once, in native raw columns.
    a,rank=fmpq_mat([integer(v) for v in eq]).rref()
    mat=[[Q(str(x)) for x in row] for row in a.tolist()[:rank]]
    piv=[next(i for i,x in enumerate(r) if x) for r in mat]
    free=[i for i in range(n) if i not in piv]
    def red(v):
        return [Q(v[j])-sum(Q(v[k])*mat[i][j] for i,k in enumerate(piv) if v[k] and mat[i][j]) for j in free]
    R={}
    def ge(label,v):R[label]=red(v)
    for k in keys:ge(('w',k),e(k))
    for k in UNIT:ge(('u',k),u[k])
    ge('M0',M0);ge('m',m);ge('M>=M0',add(M,times(-1,M0)));ge('S',S)
    ge('N',e('N14'));ge('Ncap',add(times(990,one),times(-1,e('N14'))))
    ge('Y1',Y(1));ge('Y2',add(Y(2),times(-462,one)));ge('Y3',add(Y(3),times(-44804,one)))
    ge('Y4',add(Y(4),times(-3564978,one)))
    # Norm16 and norm18 packing, Fano caps.
    ge('W14cap',lin((4,(0,0)),(-1,(0,14))))
    ge('N16cap',lin((6930,(0,0)),(-P,(0,16))))
    ge('mixed18',lin((646800,(0,0)),(4972*P,(0,16)),(-9*P,(0,18))))
    ge('N18cap',lin((289520,(0,0)),(-P,(0,18))))
    ge('N16lift',add(u[(1,27)],times(-1,e((0,16)))))
    # C1,21 positive-edge injection all ranks G<=44352.
    ge('G121cap',lin((44352,(0,0)),(-P,(1,21))))
    # All-graph harmonic site and H quadruple-Sidon cuts (unit variables).
    for label,co,constant in [('site',{(0,16):6120,(0,18):2940,(0,20):580,(0,26):300,(1,21):3420,(1,25):600,(2,26):1920,(2,28):-920,(2,30):240},210),
       ('s4',{(0,16):-193,(0,18):676,(0,20):212,(1,21):-112,(1,25):-52,(2,26):-304,(2,28):-12,(2,30):92,(3,37):72},545)]:
        ge(label,add(times(-constant,one),*(times(v,u[k]) for k,v in co.items())))
    ts=(0,8,20,34,48,64,80,100,128)
    for t in ts:
        ge(('Ht',t),add(times(9,yH),times(18,e((0,14))),times(-18,S),times(-369-10*t,M),times(5*t*t-4158,one)))
        ge(('Ct',t),add(times(9,Y(2)),times(18,Y(1)),times(-369-10*t,M0),times(5*t*t-4158,one)))
    def nu(j):
        k=(3,2*j+11)
        if j%7 and k in keys:return add(X(j),times(-2*P,e(k)))
        if j==14:return add(X(j),times(-462,one),times(-44,m))
        return X(j)
    upper=add(*(times(2*P,e((4,44+2*k))) for k in range(5)),*(nu(j) for j in range(7,18)))
    for t in (200,1000,3000,6000,10000,15000,30000):
        ge(('G',t),add(upper,times(1-2*t,m),times(t*t,one)))
    for t in (200,400,600,800,990):
        ge(('F',t),add(times(132*P,e((0,20))),times(1386-14*t,e('N14')),times(7*t*t,one)))
    # Welch-type Fano incidence of differences, rank 44, unconditional.
    for t in (112,200,400,600,800,990):
        ge(('jF',t),add(times(660*P,e((0,20))),times(132*P,e((0,24))),times(4290-76*t,e('N14')),times(38*t*t,one)))
    # Directed Fano square incidences are integers; the lower convex hull is stronger than the real tangent.
    # 2N20 >= 2q * (21N14) - 4158 q(q+1), valid for every integer q.
    for q in range(1,6):
        ge(('iF',q),add(times(2*P,e((0,20))),times(-42*q,e('N14')),times(4158*q*(q+1),one)))
    cond={}
    def condge(k,z):cond[k]=red(z)
    condge('no20',add(times(198,one),times(-1,e('N14'))))
    condge('no20/24',add(times(112,one),times(-1,e('N14'))))
    condge('no16/20',lin((16166,(0,0)),(-P,(0,18))))
    condge('no16/18/20',lin((5544,(0,0)),(-P,(1,21))))
    D={k:red(v) for k,v in u.items()}
    assert (len(piv),len(free),len(R))==(39,24,131)
    return R,cond,D,red(one)


import json
from itertools import combinations

REQUIRES={'no20':{(0,20)},'no20/24':{(0,20),(0,24)},
          'no16/20':{(0,16),(0,20)},'no16/18/20':{(0,16),(0,18),(0,20)}}

def dot(a,b):
    assert len(a)==len(b)
    return sum(x*y for x,y in zip(a,b))

def check():
    R,cond,D,o=engine()
    guide={str(k): (v,set()) for k,v in R.items()}
    for k,v in cond.items(): guide[k]=(v,REQUIRES[k])
    for k,v in D.items(): guide[str(('minus',k))]=([-x for x in v],{k})
    base=Path(__file__).resolve().parent
    h=json.loads((base/'rank36-four-hit-sets.json').read_text())
    names=h['rows'];assert len(names)==len(set(names)) and set(names)<=set(guide)
    hits=[]
    for k,den,weights in h['proof']:
        absent=frozenset(map(tuple,k));assert absent <= UNIT and absent not in hits
        used=set(); sm=[Q(0)]*len(o);den=int(den)
        assert len(weights)==len(dict(weights)) and den>0
        for i,x in weights:
            x=int(x);assert 0<=i<len(names) and x>0
            row,needed=guide[names[i]];used.update(needed)
            sm=[a+x*b for a,b in zip(sm,row)]
        assert used==absent and sm==[-den*z for z in o]
        hits.append(absent)
    assert len(hits)==49 and not any(a<b for a in hits for b in hits)
    layer=[sum(all(s&z for z in hits) for ss in combinations(sorted(UNIT),n)
               for s in [set(ss)]) for n in range(13)]
    assert layer==[0,0,0,0,19,214,552,662,471,218,66,12,1]
    # 16-positive forces 127-positive; the original scalar identity separately forces 16,18 or 20.
    implication=lambda s:(0,16) not in s or (1,27) in s
    neutral=lambda s:bool(s & {(0,16),(0,18),(0,20)})
    def refined(extra):
        return [sum(all(s&z for z in hits) and implication(s) and (not extra or neutral(s))
                    for a in combinations(sorted(UNIT),j) for s in [set(a)]) for j in range(13)]
    imp,filt=refined(False),refined(True)
    assert imp==[0,0,0,0,16,156,392,478,354,173,56,11,1]
    assert filt==[0,0,0,0,16,145,365,456,346,172,56,11,1]
    profiles=json.loads((base/'rank36-four-controls.json').read_text())
    possible=set()
    for a,den,vec in profiles:
        allowed=frozenset(map(tuple,a));den=int(den);vec=list(map(int,vec))
        assert len(allowed)==4 and allowed<=UNIT and allowed not in possible
        assert len(vec)==len(o) and den>0 and dot(o,vec)==den
        assert all(dot(row,vec)>=0 for row in R.values())
        assert all(dot(row,vec)>=0 for k,row in cond.items() if not allowed&REQUIRES[k])
        assert {k for k,row in D.items() if dot(row,vec)>0}==allowed
        assert all(allowed&h for h in hits);possible.add(allowed)
    assert len(possible)==filt[4] and all(implication(s) and neutral(s) for s in possible)
    print('49 unconditional rank-36 must-hit sets; surviving by support size 0..12:',layer)
    print('After 16 => 127 and the neutral hit:',filt)
    print('All 16 surviving four-type supports have exact positive-support rational controls.')
if __name__=='__main__':check()
