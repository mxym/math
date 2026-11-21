from fractions import Fraction as F

j_lower = 2*(F(1,6)+F(1,6)**3/3)-F(160,1000)+F(192,10000)
n1 = F(24,100)*F(86,100)/F(89,100)**2*j_lower
n2 = F(9,2)*F(174,900)**2*j_lower
m_narrow = F(27,12)*(F(25,100)**2-3*F(5,100)**2)
m_broad = F(27,12)*F(47,100)**2
narrow, broad = m_narrow*(n1+n2), m_broad*(n1+n2)
if not (j_lower>0 and narrow>F(1037,100000) and broad>F(416,10000)):
    raise ArithmeticError((narrow,broad))
print("Exact lower products", narrow, broad)
print("Decimal for display only:", float(narrow), float(broad))

# Legible independent finite replay: genuine small prime bases, varying
# integer thresholds, direct divisor convolutions. Represent logs formally
# as vectors of log(prime base); no floating point signs or factorizations.
from itertools import combinations
from math import prod
bases=(3,5,7,11,13,17,19,23)

def run(ps, U, V, B):
    rank=len(ps)
    top=(1<<rank)-1
    val=[prod(p for i,p in enumerate(ps) if mask>>i&1) for mask in range(top+1)]
    sub=[[a for a in range(top+1) if a&b==a] for b in range(top+1)]
    mu=[(-1)**mask.bit_count() for mask in range(top+1)]
    logs=[tuple((mask>>i)&1 for i in range(rank)) for mask in range(top+1)]
    lam=[logs[mask] if mask.bit_count()==1 else (0,)*rank for mask in range(top+1)]
    mu2=[sum(mu[d]*mu[mask^d] for d in sub[mask]) for mask in range(top+1)]
    mul=[tuple(sum(mu[d]*lam[mask^d][i] for d in sub[mask])
                for i in range(rank)) for mask in range(top+1)]
    p_b=[-sum(mu2[mask^b] for b in sub[mask] if val[b]>B) for mask in range(top+1)]
    h_b=[tuple(sum(mu[mask^b]*logs[b][i]-mul[mask^b][i]
                   for b in sub[mask] if val[b]>B)
               for i in range(rank)) for mask in range(top+1)]
    out=[0]*rank
    for k in range(top+1):
        if val[k]<=V:
            continue
        for r in sub[top^k]:
            if val[r]<=U:
                continue
            row=[(mu[r]-p_b[r])*(lam[k][i]-h_b[k][i]) for i in range(rank)]
            if r|k!=top and any(z>0 for z in row):
                raise ArithmeticError(("positive nonunit h", ps,U,V,B,r,k,row))
            out=[a+b for a,b in zip(out,row)]
    return out

counts=[0,0,0]
for rank in (2,3):
    for ps in combinations(bases,rank):
        q=prod(ps)
        for B in sorted({ps[-1],13,23,40,60,90,130,180}):
            if ps[-1]>B or B*B<=q:
                continue
            for U in (3,5,7,11):
                V=2
                if U>=B:
                    continue
                if rank==2 and ps[0]>U:
                    expected=-1; case=0
                elif rank==3 and ps[0]<=U<ps[1] and ps[1]*ps[2]>B and ps[0]*q<B*B:
                    expected=sum(ps[0]*p>B for p in ps[1:]); case=1
                elif rank==3 and ps[0]>U and ps[0]*ps[1]>B:
                    expected=2; case=2
                else:
                    continue
                got=run(ps,U,V,B)
                if got != [expected]*rank:
                    raise ArithmeticError((ps,U,V,B,got,expected))
                counts[case]+=1
if not all(counts):
    raise ArithmeticError(counts)
print("Exact divisor/log-vector replays (negative, one-small, balanced):",counts)
