
"""Exact verification of three more rank-36 four-palette cuts.
Place beside higher_moments.py and rank36_three_types.py (repository's shared-norm-18 path).
Uses the repository's local dependencies and SymPy rational arithmetic; no optimization.
"""
from fractions import Fraction as Q
from math import lcm
from pathlib import Path
import runpy, sys
from higher_moments import rows, projections, SHIFTS
from rank36_three_types import UNIT

P=2402
spec=[(16,18,24,26),(16,18,24,127),(16,18,121,125),(16,18,125,127),
 (16,24,127,337),(18,20,24,26),(18,20,26,125),(18,20,121,125),
 (18,20,125,127),(18,26,125,230),(20,24,26,228),(20,24,26,337),
 (20,26,125,228),(20,26,125,337),(20,26,228,230),(20,125,127,337),
 (16,18,24,121),(18,20,24,121),(18,24,26,230)]


def integer(r):
    de=lcm(*(Q(x).denominator for x in r))
    return [int(de*x) for x in r]

def engine():
    allowed=set(UNIT)
    # In all rows a vector slot is a linear form on the following raw variables.
    raw=rows()
    keys=sorted(set().union(*raw,*(projections(sh,n) for sh in (None,*SHIFTS) for n in (1,2,3))))
    cols=keys+['N14','X14','M0','F1','F2','F4']; n=len(cols)
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
    from sympy import Matrix
    def pack(x):
        return [Q(v) for v in x]
    # eq*r=0; rref of all equations once, in native raw columns.
    mat,piv=Matrix(eq).to_DM().rref()
    mat=mat.to_Matrix(); free=[i for i in range(n) if i not in piv]
    def red(v):
        return [Q(v[j])-sum(Q(v[k])*Q(mat[i,j]) for i,k in enumerate(piv) if v[k] and mat[i,j]) for j in free]
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

    # Literal Fano line pairs of each absolute inner product, before dividing by p.
    F1,F2,F4=e('F1'),e('F2'),e('F4')
    for i,f,a,k in [(1,F1,(0,26),(0,30)),(2,F2,(0,24),(0,32)),(4,F4,(0,20),(0,36))]:
        ge(('Fano pairs',i),f)
        ge(('Fano short difference',i),add(times(P,e(a)),times(-2,f)))
        if k in cols:ge(('Fano long sum',i),add(times(P,e(k)),times(-2,f)))
    ge('Fano→U125 or G121',add(times(7*P,u[(1,25)]),times(4*P,e((1,21))),times(-1,F1)))
    ge('Fano→U127 or N18',add(times(8*P,u[(1,27)]),times(45*P,e((0,18))),times(-2,F2)))
    ge('Fano→G230',add(times(3*P,e((2,30))),times(-1,F4)))
    for q in range(1,9):
        ge(('Fano common pairs',q),add(times(2,F4),times(-21*q,e('N14')),times(2079*q*(q+1),one)))
    for t in (50,100,198,300,400,500,600,700,800,900,990):
        ge(('Fano Gram',t),add(times(88,F1),times(352,F2),times(1408,F4),times(4312-98*t,e('N14')),times(49*t*t,one)))
        ge(('Fano total pairs',t),add(nu(14),times(4,F1),times(4,F2),times(4,F4),times(1-t,e('N14')),times(Q(t*t,2),one)))

    cond={}
    def condge(k,z):cond[k]=red(z)
    condge('no20',add(times(198,one),times(-1,e('N14'))))
    condge('no20/24',add(times(112,one),times(-1,e('N14'))))
    condge('no16/20',lin((16166,(0,0)),(-P,(0,18))))
    condge('no16/18/20',lin((5544,(0,0)),(-P,(1,21))))
    D={k:red(v) for k,v in u.items()}
    return R,cond,D,red(one)


CERTS=[[[[0,20],[0,24],[0,26],[2,28]],406138318584356050,[["('w', (0, 22))",38570118325480126],["('w', (2, 26))",67328652959754494],["('w', (3, 33))",24614394781303558],["('w', (3, 35))",39146748662586334],["('w', (4, 44))",3723911631257818],["Y1",1813149658005147],["Y3",40513289281773],["('Ct', 34)",35108475633231],["('G', 15000)",345082353],["Fano\u2192U125 or G121",12891160556472],["Fano\u2192U127 or N18",25782321112944],["Fano\u2192G230",206258568903552],["('Fano Gram', 198)",146490460869],["('minus', (0, 16))",1757360214509543644],["('minus', (0, 18))",3167523238138558178],["('minus', (1, 21))",58072695394770386],["('minus', (1, 25))",243306253608932052],["('minus', (1, 27))",486572814365534292],["('minus', (2, 30))",1494465726537830926],["('minus', (3, 37))",12587495323303054]]],
[[[0,20],[0,24],[0,26],[3,37]],85401435,[["('w', (2, 22))",781851],["('w', (2, 26))",3152625],["('w', (3, 33))",10290168],["('w', (3, 35))",5901714],["('w', (4, 44))",3732708],["S",2849973],["Y1",12972603],["Y3",7203],["Fano\u2192G230",36298],["('Fano common pairs', 1)",18149],["('minus', (0, 16))",283105725],["('minus', (0, 18))",60328632],["('minus', (1, 21))",5296410],["('minus', (1, 25))",3051741],["('minus', (1, 27))",882735],["('minus', (2, 28))",7061880],["('minus', (2, 30))",259898802]]],
[[[0,20],[1,25],[1,27],[3,37]],50714072332,[["('w', (2, 22))",4930133824],["('w', (3, 33))",17835484128],["('w', (3, 35))",8700236160],["('w', (4, 46))",761270664],["S",3045082656],["Y1",11290068636],["Y3",10353112],["('Fano short difference', 1)",1606044],["('Fano short difference', 2)",6424176],["Fano\u2192G230",51393408],["('Fano Gram', 198)",36501],["('minus', (0, 16))",392380650816],["('minus', (0, 18))",106070379184],["('minus', (0, 24))",14125835328],["('minus', (0, 26))",5380259016],["('minus', (1, 21))",33906824160],["('minus', (2, 26))",14065381792],["('minus', (2, 28))",6815184992],["('minus', (2, 30))",368455846880]]]]

def verify():
    R,cond,D,one=engine()
    # Each source row is a nonnegative linear form. An inactive unit type is zero.
    conditional={
      'no20':[(0,20)],'no20/24':[(0,20),(0,24)],
      'no16/20':[(0,16),(0,20)],
      'no16/18/20':[(0,16),(0,18),(0,20)]}
    for face,den,cert in CERTS:
       here=set(map(tuple,face))
       assert len(here)==4 and here<=set(UNIT) and den>0
       rows={str(k):v for k,v in R.items()}
       for k,tests in conditional.items():
           if not here&set(tests):rows[k]=cond[k]
       for k in UNIT-here:rows[str(('minus',k))]=[-x for x in D[k]]
       for k in here:rows[str(('plus',k))]=[P*x-(2 if not k[0] else 1)*c for x,c in zip(D[k],one)]
       assert all(c>0 for k,c in cert) and len({k for k,c in cert})==len(cert)
       assert all(len(rows[k])==len(one) for k,c in cert)
       result=[sum(c*rows[k][i] for k,c in cert) for i in range(len(one))]
       assert result==[-den*x for x in one]
       print(tuple(map(tuple,face)),'contradiction',-den,'from',len(cert),'rows')
if __name__=='__main__':verify()
