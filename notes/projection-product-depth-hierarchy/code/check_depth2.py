#!/usr/bin/env python3
"""Exact checker for the full product-depth-two projection-body spectral optimum.

Uses already published, hash-pinned exact Pareto frontiers for arbitrary
joins of two-simplex products. Every new numerical decision uses integers
or Fraction, including logarithm intervals, finite core and infinite tails.

Proof of finite reduction and induction over product-depth is in paper.md.
"""
from fractions import Fraction as F
from functools import lru_cache
from math import factorial
from pathlib import Path
import hashlib
import json
import sys

HERE=Path(__file__).resolve().parent.parent
PREV=HERE.parent/'projection-first-nesting-d55'/'certificates'/'two_layer56.json'
EXT=HERE.parent/'projection-persistent-nesting-gap'/'certificates'/'extension57to85.json'
OLD_HASH='101ffdf287f984965c941b1f98f93de89ae4a3bd0d4e796f02558a8039cb3d9f'
NEW_HASH='caaa1ced19c2a2511e3537a8a4851d0d2e5bcb51d8b857990360c4fa2efcdb8d'
FIN=HERE/'certificates'/'finite_splits.tsv'
PI_LO=F(333,106)
PI_HI=F(355,113)
Q4=F(175,128)
Q5=F(189,128)
TERMS=18


def need(b,msg):
    if not b:raise RuntimeError('depth2 certificate: '+msg)


@lru_cache(maxsize=None)
def g(n):
    need(n>=1 and type(n)==int,'invalid g(n)')
    return F(n**n,factorial(n))


def target():
    # Each child is the join of two B(5,5) blocks.
    return F(12)*Q5**4*g(21)**2/g(42)


def atan_interval(z,count=12):
    need(F(0)<z<F(1) and count%2==0,'atan series domain')
    s=sum(((-1)**i)*z**(2*i+1)/F(2*i+1) for i in range(count))
    return s,s+z**(2*count+1)/F(2*count+1)


def check_pi():
    a,b=atan_interval(F(1,5));c,d=atan_interval(F(1,239))
    need(PI_LO<16*a-4*d and 16*b-4*c<PI_HI,'Machin pi bounds')


@lru_cache(maxsize=20000)
def log_interval(x):
    x=F(x)
    need(x>0,'log input positive')
    shift=x.numerator.bit_length()-x.denominator.bit_length()
    y=x/F(2**shift) if shift>=0 else x*F(2**(-shift))
    if y<1:y*=2;shift-=1
    if y>=2:y/=2;shift+=1
    z=(y-1)/(y+1)
    p=z;S=F(0)
    for j in range(TERMS):
        S+=2*p/F(2*j+1);p*=z*z
    rem=2*p/(F(2*TERMS+1)*(1-z*z))
    if shift==0:return S,S+rem
    z2=F(1,3);t=z2;L2=F(0)
    for j in range(TERMS):L2+=2*t/F(2*j+1);t*=z2*z2
    L2hi=L2+2*t/(F(2*TERMS+1)*(1-z2*z2))
    if shift>0:return S+shift*L2,S+rem+shift*L2hi
    return S+shift*L2hi,S+rem+shift*L2


def loglo(x):return log_interval(F(x))[0]
def loghi(x):return log_interval(F(x))[1]


def check_analytic_tails():
    check_pi()
    T=target()
    need(T==F(257554342358885086515,36893488147419103232),
         'wrong candidate depth-two body')
    need(T**11>Q5**43,'depth two must strictly improve on depth one')
    # A third product layer beats the exact second-layer optimum.
    Q3=T**4*F(24)*g(85)**2/g(170)
    need(Q3**43>T**171,'explicit depth-three amplification certificate fails')
    Qlo=loglo(T)/43;Qhi=loghi(T)/43
    Alo=loglo(Q5)/11;Ahi=loghi(Q5)/11
    Blo=loglo(Q4)/4
    need(Qlo>Ahi and Qlo-Ahi>F(1,126),
         'separation needed for analytic tail monotonicity')
    need(Blo>F(31,400),'positive affine-defect slope needed')
    need(Q5**80>Q4**99 and Q5**200<Q4**253,
         'exact rational power bounds on t_star=1-A/B')
    need(F(2,27)<F(31,400),
         'product-envelope kink derivative bound fails')
    # CASE I: min(r,s)>=12 and r+s>=63. At each input the
    # optimal H for the two-layer A/B envelope occurs at its kink.
    # C*(1+2rs/n)<U(n) by uniform two-simplex Robbins estimate.
    n=63
    U2=((F(1)+F(n,2))/(F(1)-F(1,12*n)))**2*F(2)/(PI_LO*n)
    F63=(Qlo-Ahi)*(n+1)-Ahi-loghi(F(11,20))-loghi(U2)/2
    need(F63>0,'analytic equal-large n=63 anchor not positive')
    # F'(x) > Qlo-Ahi-1/(2x)>0 for x>=63 by the derivative
    # of log U(x) displayed and proved in the paper.

    # CASE II: 1<=r<=11, s>=80. The H of the large parent is
    # optimally bounded at the kink; both Q's have spectral bound A.
    # Apply the explicit dimension-uniform Robbins product multiplier.
    checked=0
    for r in range(1,12):
        L=(Ahi*(r+82)+loghi(g(r))-F(r)
           +loghi(F(1)+F(r,80))/2
           +F(1,12*(r+80))
           +loghi(F(r+1)+F(r)*F(11,20)*F(81,80)))
        need(L<Qlo*(r+81),f'small-r, arbitrary s>=80 tail fails r={r}')
        checked+=1
    return checked


def pinned_two_layer_states():
    need(hashlib.sha256(PREV.read_bytes()).hexdigest()==OLD_HASH,
         'previous two-layer base certificate changed')
    need(hashlib.sha256(EXT.read_bytes()).hexdigest()==NEW_HASH,
         'previous two-layer extension certificate changed')
    a=json.loads(PREV.read_text());b=json.loads(EXT.read_text())
    need(a['max_D']==56 and len(a['frontiers'])==57,
         'prior two-layer base levels incomplete')
    need(b['first_D']==57 and b['last_D']==85 and len(b['frontiers'])==29,
         'prior two-layer extension levels incomplete')
    need(b['parent_sha256']==OLD_HASH,'extension chain provenance mismatch')
    f=a['frontiers']+b['frontiers']
    need(len(f)==86,'missing frontiers through D=85')
    vals=[]
    for d in range(1,80):
        arr=[]
        for st in f[d+1]:
            arr.append((F(st['H']),F(st['Q'])))
        need(arr,'missing parent states')
        vals.append(arr)
    return vals


def check_all_finite_pairs(path=None):
    V=pinned_two_layer_states()
    lines=Path(path or FIN).read_text().splitlines()
    need(len(lines)==1215 and lines[0]=='r\ts\twinner_i\twinner_j\tbest_product_Q',
         'finite core certificate has wrong header or row count')
    row_iter=iter(lines[1:])
    T=target()
    checks=0;split_count=0;equality_count=0;equal_split=None
    # The two analytic tails exclude every split NOT in this loop.
    # r<=11: s<=79; r>=12: r+s<=62, by Case I above.
    for r in range(1,80):
        left=V[r-1]
        for s in range(r,80):
            if r>11 and r+s>62:continue
            right=V[s-1]
            best=F(0);best_i=None;ties=0
            for i,(ha,qa) in enumerate(left):
                for j,(hb,qb) in enumerate(right):
                    z=qa*qb*(s*ha+r*hb)
                    if z>best:
                        best=z;best_i=(i,j);ties=1
                    elif z==best:
                        ties+=1
                    checks+=1
            n=r+s
            prod=best*g(r)*g(s)/(F(n)*g(n))
            row=next(row_iter).split('\t')
            need(len(row)==5 and (int(row[0]),int(row[1]))==(r,s),
                 f'finite split record missing/misordered at ({r},{s})')
            need((int(row[2]),int(row[3]))==best_i and F(row[4])==prod,
                 f'wrong attained finite split maximum at ({r},{s})')
            lhs=prod**43
            rhs=T**(n+1)
            need(lhs<=rhs,f'finite product exceeds candidate at dims ({r},{s})')
            if lhs==rhs:
                equality_count+=1
                equal_split=(r,s,best_i,ties)
                need(r==s==21 and best_i==(48,48) and ties==1,
                     'unexpected equality split')
                need(left[48]==(F(12),Q5**2),
                     'candidate parent must be join of two B(5,5)')
            split_count+=1
    need(next(row_iter,None) is None,'unexpected extra dimension split record')
    need(split_count==1214 and checks==2770504,
         'finite input split/candidate count has changed')
    need(equality_count==1 and equal_split==(21,21,(48,48),1),
         'unique winning product state has not been certified')
    return split_count,checks,equal_split


def check():
    ntail=check_analytic_tails()
    splits,candidates,winner=check_all_finite_pairs()
    print('PASS: sharp product-depth-two spectral classification for all dimensions')
    print('winning primitive = ((T5 x T5) * (T5 x T5)) x ((T5 x T5) * (T5 x T5))')
    print('winning dimension=42, H=12, Q='+str(target()))
    print('exact spectral supremum=lambda_2=Q^(1/43), asymptotic rate=e*lambda_2')
    print('finite split maxima checked =',splits)
    print('producer/checker crosschecked all winning rational split records')
    print('exact product candidate comparisons =',candidates)
    print('unique winning dimension split =',winner)
    print('exact depth-three example is strictly better: ((K2 x K2) with K2=P*P), dimension=170')
    print('infinite tails: r>=12,r+s>=63 and 1<=r<=11,s>=80')
    print('small-parent tail scalar interval checks =',ntail)
    print('all proof decisions: exact Fraction/integer arithmetic and rational log intervals')


if __name__=='__main__':check()
