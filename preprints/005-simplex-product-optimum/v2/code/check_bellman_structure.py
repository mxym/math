#!/usr/bin/env python3
"""Independent rational structural regression for the 005 Bellman proof.

No floating-point proof comparison. This supplements, rather than replaces,
the full exact interval replay in check_bellman_upper.py.
"""
from fractions import Fraction as Q
from pathlib import Path
import importlib.util

SPEC = importlib.util.spec_from_file_location(
    'bellman', Path(__file__).resolve().with_name('check_bellman_upper.py'))
m = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(m)


def require(cond, message):
    if not cond:
        raise RuntimeError(message)


def direct_q(r, s, H1, H2):
    C0 = Q(r * H1 + s * H2, r+s)
    return H1 * H1 / (r+1) + H2 * H2 / (s+1) - C0*C0 / (r+s+1)


def direct_derivative(r, s, H1, H2):
    n = r+s
    C0 = (r*H1+s*H2)/n
    return -2*r*H1/(s*(r+1)) + 2*H2/(s+1) - 2*C0*Q(s-r,s)/(n+1)


def main():
    points = branches = 0
    for s in range(1,10):
        for r in range(s,1000):
            n=r+s
            Delta=4*r*s+3*n+2
            curvature = Q(2*r*r,s*s*(r+1))+Q(2,s+1)-Q(2*(s-r)**2,s*s*(n+1))
            require(curvature>0,'quadratic curvature')
            for name,lo,hi,A,D,E in m.branch_data(r,s):
                branches+=1
                require(A>0,'B-quadratic curvature')
                for B in (lo,(lo+hi)/2,hi):
                    if name=='low': H2=Q(1)
                    elif name=='high': H2=Q(s+1)
                    else: H2=B*Q((s+1)*(3*r+s+2),Delta)
                    H1=(n*B-r*H2)/s
                    require(1<=H1<=r+1 and 1<=H2<=s+1, 'box feasibility')
                    require(direct_q(r,s,H1,H2)==A*B*B+D*B+E,'coefficient mismatch')
                    derivative=direct_derivative(r,s,H1,H2)
                    require(derivative>=0 if name=='low' else derivative<=0 if name=='high' else derivative==0,'wrong constrained minimizer')
                    points+=1
    require(branches==26847 and points==80541,'structural scope mismatch')
    # Endpoint maxima omitted as explicit conditions in the public checker.
    require(1-2*m.ALPHA_I[1]*Q(3,7)*9>0,'s=1 endpoint is not increasing')
    for s in (2,3):
        B=Q(4*s+3,3)
        require(1-2*m.ALPHA_I[1]*Q(3,4*s+3)*B*B>0,'s=2,3 endpoint is not increasing')
    # Preserve the distinction between the full piecewise q and q_high.
    # These witnesses refute the old, overbroad full-q formulation.
    require(Q(3008,11008)*9==Q(423,172)<3,'s=2 correction witness')
    require(Q(3011,15011)*16==Q(48176,15011)<4,'s=3 correction witness')
    for r,s,B,limit in ((1000,2,Q(3),Q(3)),(1000,3,Q(4),Q(4))):
        mid=next(row for row in m.branch_data(r,s) if row[0]=='mid')
        require(mid[1] < B < mid[2], 'notation witness not in middle branch')
        q_full=mid[3]*B*B+mid[4]*B+mid[5]
        A,D,E=m.boundary_coefficients(r,s,s+1)
        q_high=A*B*B+D*B+E
        require(q_full < limit <= q_high, 'piecewise/high distinction lost')
    # The actual high boundary covers only the required high branch, and its
    # q difference coefficients are nonpositive on the enlarged intervals.
    for s,lo,hi in ((2,Q(3),Q(5)),(3,Q(4),Q(7))):
        for B in (lo,hi):
            if s==2:
                require(4*B*B-48*B+108<=0 and 3*B*B-54*B+99<=0,'s=2 tail sign')
            else:
                require(B*B-20*B+64<=0 and -24*B+60<=0,'s=3 tail sign')
    # Verify the high-branch difference identities as B-polynomials for
    # several dimensions, including a very large dimension beyond the strip.
    for r in (3,10,1000,10**6):
        for s in (2,3):
            A,D,E=m.boundary_coefficients(r,s,s+1)
            for B in (Q(0),Q(1),Q(2)):
                if s==2:
                    limit=Q(3,2)*(B*B-6*B+11)
                    difference=-(r*(4*B*B-48*B+108)+(3*B*B-54*B+99))/(2*(r+1)*(r+3))
                else:
                    limit=B*B-8*B+20
                    difference=-4*(r*(B*B-20*B+64)-24*B+60)/(3*(r+1)*(r+4))
                require(A*B*B+D*B+E-limit==difference, 'high-boundary identity mismatch')
    # Convex quadratics lie below the maximum of their endpoint values on
    # each interval, so the preceding signs cover every real B there.
    rejected=0
    for bad in (Q(0),Q(-1)):
        try: m.log_bounds(bad)
        except ValueError: rejected+=1
    require(rejected==2,'nonpositive log input accepted')
    require(m.log_bounds(Q(1))==(Q(0),Q(0)),'log identity')
    print('PASS: 26,847 independently reconstructed quadratic branches; 80,541 endpoint/midpoint minimizer checks.')
    print('PASS: all three implicit endpoint-tail monotonicity conditions verified exactly.')
    print('PASS: both manuscript high-branch notation counterexamples verified exactly.')
    print('PASS: limiting high-branch sign certificates and invalid-log negative controls.')

if __name__=='__main__': main()
