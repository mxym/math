#!/usr/bin/env python3
"""Exact, dependency-free certificates refuting Amdeberhan–Moll Conjecture 21.
No floating-point arithmetic is used. Run with Python 3.8+.
"""
from fractions import Fraction as F
from math import comb, factorial
import json
from pathlib import Path
if not __debug__: raise SystemExit("Run without -O or -OO; certificate checks require assertions")


def L(a):
    return [x*x - (a[k-1] if k else 0)*(a[k+1] if k+1 < len(a) else 0)
            for k, x in enumerate(a)]


def cycle_coefficients(n):
    """Absolute coefficients of (q-1)^n + (-1)^n(q-1), degree ascending."""
    signed = [(-1)**(n-k)*comb(n,k) for k in range(n+1)]
    signed[0] -= (-1)**n
    signed[1] += (-1)**n
    return [abs(x) for x in signed]


def cycle_by_deletion_contraction(n):
    """Independent polynomial derivation: P(C_j)=q(q-1)^(j-1)-P(C_(j-1))."""
    p = [0, 2, -3, 1]  # q(q-1)(q-2)
    for j in range(4,n+1):
        tree = [0] + [(-1)**(j-1-k)*comb(j-1,k) for k in range(j)]
        p = [tree[k] - (p[k] if k < len(p) else 0) for k in range(j+1)]
    return [abs(x) for x in p]


# Polynomial arithmetic over Q, ascending coefficient order.
def trim(p):
    while len(p)>1 and p[-1]==0:p.pop()
    return p

def add(a,b):
    return trim([(a[i] if i<len(a) else F(0)) + (b[i] if i<len(b) else F(0))
                 for i in range(max(len(a),len(b)))])

def scale(a,c):return trim([c*x for x in a])

def mul(a,b):
    r=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):r[i+j]+=x*y
    return trim(r)

def power(a,n):
    r=[F(1)]
    for _ in range(n):r=mul(r,a)
    return r

def evaluate(p,n):
    r=F(0)
    for x in reversed(p):r=r*n+x
    return r


def symbolic_certificate():
    a=[[F(0)],[F(-1),F(1)]]
    for k in range(2,6):
        p=[F(1)]
        for j in range(k):p=mul(p,[F(-j),F(1)])
        a.append(scale(p,F(1,factorial(k))))
    # Drop the rightmost entry on every step, never inventing a boundary value there.
    for _ in range(3):
        a=[add(mul(a[k],a[k]),scale(mul(a[k-1],a[k+1]),-1)) if k
           else mul(a[0],a[0]) for k in range(len(a)-1)]
    q=[F(36),F(-412),F(-327),F(-12),F(2)]
    expected=scale(mul(mul(power([F(0),F(1)],3),power([F(-1),F(1)],8)),
                       mul([F(4),F(1)],q)),F(-1,103680))
    assert a[2]==expected, 'Symbolic identity failed'
    shifted=[F(0)]
    for j,c in enumerate(q):shifted=add(shifted,scale(power([F(17),F(1)],j),c))
    assert shifted==[F(6615),F(17370),F(2529),F(124),F(2)]
    assert all(c>0 for c in shifted)
    assert evaluate(expected,17)==-28272276537344
    return {'L3_q2_factorization':'-n^3*(n-1)^8*(n+4)*(2*n^4-12*n^3-327*n^2-412*n+36)/103680',
            'Q_shift17_coefficients':[int(x) for x in shifted]}


def main():
    report={'symbolic':symbolic_certificate(),'cycles':{},'classification':{}}
    for n,steps,negative in [(12,5,-249621701601023742801969101519201265582387397744),
                             (17,3,-28272276537344)]:
        a=cycle_coefficients(n)
        assert a==cycle_by_deletion_contraction(n)
        rows=[a]
        for _ in range(steps):rows.append(L(rows[-1]))
        assert all(all(x>=0 for x in row) for row in rows[:-1])
        assert rows[-1][2]==negative
        report['cycles'][str(n)]={'coefficients':a,'iterations':rows,'first_negative_iteration':steps,
                                  'negative_index':2,'negative_value':negative}
        print(f'C{n}: first negative at L^{steps}, coefficient index 2 = {negative}')
    expected_small={3:(0,3),4:(1,28),5:(2,25825),6:(2,90846),7:(2,271656),
                    8:(3,711608924160),9:(3,4029124698225),10:(3,19225238518750),
                    11:(3,79738750726206)}
    for n,(steps,minimum) in expected_small.items():
        a=cycle_coefficients(n)
        for _ in range(steps):
            assert all(x>=0 for x in a)
            a=L(a)
        assert all(x>=0 for x in a)
        slack=[a[k]**2-3*a[k-1]*a[k+1] for k in range(1,n)]
        assert all(x>=0 for x in slack)
        assert min(slack[1:])==minimum
        report['classification'][str(n)]={'type':'3-factor certificate','iteration':steps,
                                           'iterate':a,'minimum_slack_indices_2_to_n_minus_1':minimum}
    for n,expected in [(13,-3618341131654935620812800),
                       (14,-199158562975246657489530096),
                       (15,-2734560032125157358883149375),
                       (16,-25982668618402950000000000000)]:
        a=cycle_coefficients(n)
        for _ in range(4):
            assert all(x>=0 for x in a)
            a=L(a)
        assert a[2]==expected
        report['classification'][str(n)]={'type':'negative','iteration':4,'index':2,'value':expected}
    for n,isolates,steps,expected in [(17,1,3,-28272276537344),
          (12,3,5,-249621701601023742801969101519201265582387397744)]:
        a=[0]*isolates+cycle_coefficients(n)
        for _ in range(steps):
            a=[a[k]**2-a[k-1]*a[k+1] for k in range(1,len(a)-1)]
        assert a[2+isolates-steps]==expected
    print('C3 through C11: exact 3-factor certificates verified.')
    print('C13 through C16: negative fourth-iterate entries verified.')
    print('Endpoint-deleting variants C17 + K1 and C12 + 3K1 verified.')
    print('Symbolic identity verified over Q[n]. Q(n)>0 for every integer n>=17.')
    print('Therefore every cycle C_n with n>=17 fails 3-log-concavity.')
    path=Path(__file__).with_name('exact_certificates.json')
    path.write_text(json.dumps(report,indent=2)+'\n')
    print('All exact checks passed.')

if __name__=='__main__':main()
