#!/usr/bin/env python3
"""Exact finite dual no-go for all nonnegative even-power Bellman envelopes.

No floats, optimizers or disabled-assert decisions. All real logarithms are
bounded by rational atanh series with explicit remainder inequalities.
"""
from fractions import Fraction as F
from math import factorial,comb
from functools import lru_cache

SAMPLES=((5,F(6)),(13,F(10)),(36,F(133,8)))
WEIGHTS=(F(93264,10**6),F(3651,10**6),F(24062,10**6))
T_FLOOR=F(48613,10**6)
N_TERMS=22


def require(b,msg):
    if not b:raise RuntimeError('power-Bellman dual certificate: '+msg)


@lru_cache(maxsize=None)
def log2_bounds():
    z=F(1,3);power=z;S=F(0)
    for j in range(N_TERMS):
        S+=2*power/F(2*j+1)
        power*=z*z
    return S,S+2*power/(F(2*N_TERMS+1)*(1-z*z))


@lru_cache(maxsize=None)
def log_bounds(x):
    x=F(x)
    require(x>0,'ln argument nonpositive')
    k=x.numerator.bit_length()-x.denominator.bit_length()
    y=x/F(2**k) if k>=0 else x*F(2**-k)
    if y<1:y*=2;k-=1
    elif y>=2:y/=2;k+=1
    require(1<=y<2,'normalization failed')
    z=(y-1)/(y+1);power=z;S=F(0)
    for j in range(N_TERMS):
        S+=2*power/F(2*j+1)
        power*=z*z
    rem=2*power/(F(2*N_TERMS+1)*(1-z*z))
    l2,h2=log2_bounds()
    return (S+k*l2,S+rem+k*h2) if k>=0 else (S+k*h2,S+rem+k*l2)


def sample_multiplier(r,h):
    # Exact product multiplier C*x at (r,h) x (r,h).
    return h*F(comb(2*r,r),4**r)


def delta_power(r,h,p):
    # Φ(product)-2Φ(factor) per coefficient a_p, equal factors.
    return h**p*(F(2,(r+1)**(p-1))-F(1,(2*r+1)**(p-1)))-1


def dual_column(p):
    return sum(w*delta_power(r,h,p) for w,(r,h) in zip(WEIGHTS,SAMPLES))


def universal_tail():
    # For every even p>=14, drop favorable negative terms.
    # r5, h6: δ_p <= 11;
    # r13, h10: δ_p <=20(5/7)^(p-1)-1;
    # r36, h133/8: δ_p<=(133/4)(133/296)^(p-1)-1.
    y1,y2,y3=WEIGHTS
    B=(11*y1-y2-y3
       +20*y2*F(5,7)**13
       +F(133,4)*y3*F(133,296)**13)
    require(B<1,'universal even-degree tail p>=14 is not closed')
    return B


def weighted_log_bound():
    weighted_lo=F(0);weighted_hi=F(0)
    terms=[]
    for y,(r,h) in zip(WEIGHTS,SAMPLES):
        m=sample_multiplier(r,h)
        lo,hi=log_bounds(m)
        weighted_lo+=y*lo;weighted_hi+=y*hi
        terms.append((r,str(h),str(m)))
    require(weighted_lo>T_FLOOR,
            'three product multipliers do not force the stated constant floor')
    return weighted_lo,weighted_hi,terms


def comparison_with_binary_orbit():
    # Certified v5 upper endpoint for the binary T5 orbit is 2.853465550704.
    # A positive Taylor partial sum strictly underestimates exp(1+T_FLOOR).
    x=F(1)+T_FLOOR
    lower=sum(x**n/F(factorial(n)) for n in range(18))
    endpoint=F(2853465550704,10**12)
    require(lower>endpoint,
            'new Bellman method floor not separated from inherited T5 endpoint')
    return lower


def audit_attainable_sample_states():
    # Genuine source states, not fabricated values in a continuous H-box.
    from pathlib import Path
    import json,hashlib
    base=Path(__file__).resolve().parent.parent.parent/'exact-product-join-finite-optima'/'certificates'/'frontiers48.json'
    sha='975c4cc5c37f309426d57661e8b5d4dcb45fb2811c6a000da3204faeb4ddea38'
    require(hashlib.sha256(base.read_bytes()).hexdigest()==sha,
            'previously certified source-frontier hash does not match')
    data=json.loads(base.read_text())['states']
    for d,h in SAMPLES:
        require(any(F(x['H'])==h for x in data[d]),
                'sample H was not shown to be a genuinely attainable state')
    # Two explicit simple sample constructions:
    require(F(5)+F(5)==F(10),'13D join example H incorrectly stated')
    Hinner=F(1)+F(5)+F(5)
    Houter=F(24)/(F(6,7)+F(18)/Hinner)
    require(F(1)+F(6)+Houter==F(133,8),
            '36D nested sample affine H construction invalid')


def check_convex_escape_and_its_failure():
    # A non-power convex hinge profile evades ALL THREE obstruction tests,
    # but deliberately fails a later attained binary-orbit product.
    knots=(F(1,5),F(1,2),F(3,4))
    slopes=(F(3,100),F(1,25),F(3,200))
    def psi(t):
        return sum(s*max(F(0),t-k) for s,k in zip(slopes,knots))
    c=psi(F(1))
    require(c==F(191,4000),'incorrect hinge-profile endpoint')
    for r,h in SAMPLES:
        D=r+1
        product_increment=-c+2*D*psi(h/D)-(2*r+1)*psi(h/F(2*r+1))
        require(product_increment>log_bounds(sample_multiplier(r,h))[1],
                f'convex hinge sample must evade the power barrier at d={r}')
    # The actual binary T5 level-two body has d=85, H=24; here the same
    # hinge profile violates product closure in the opposite direction.
    r=85;h=F(24);D=r+1
    product_increment=-c+2*D*psi(h/D)-(2*r+1)*psi(h/F(2*r+1))
    require(product_increment<log_bounds(sample_multiplier(r,h))[0],
            'hinge profile unexpectedly survived the higher binary-orbit test')
    return c


def check():
    audit_attainable_sample_states()
    finite=[]
    for k in range(1,7):
        d=dual_column(2*k)
        require(d<1,f'positive-power column 2k={2*k} violates dual inequality')
        finite.append((2*k,1-d))
    B=universal_tail()
    lower,upper,terms=weighted_log_bound()
    ebound=comparison_with_binary_orbit()
    escape=check_convex_escape_and_its_failure()
    print('PASS: universal exact obstruction for any finite or summable nonnegative even-power Bellman envelope')
    print('three attainable self-product samples (dimension,H,multiplier) =',terms)
    print('positive rational dual weights =',','.join(str(x) for x in WEIGHTS))
    print('finite even-degree columns checked =',len(finite),'for p=2,4,6,8,10,12')
    print('every even p>=14 covered analytically by monotone geometric powers')
    print('all dual columns are strictly < 1')
    print('weighted log lower >',T_FLOOR)
    print('no nonnegative even-power full-state product-inductive Bellman envelope can certify T<=',T_FLOOR)
    print('inherited T5 rate < 2853465550704/10^12 < exp(1+T_floor)')
    print('explicit convex non-power hinge profile passes all three tests at endpoint =',escape)
    print('the same hinge profile FAILS a fourth attainable binary-orbit product at (d,H)=(85,24)')
    print('all checks: Python int/Fraction and rigorous rational atanh remainder')


if __name__=='__main__':check()
