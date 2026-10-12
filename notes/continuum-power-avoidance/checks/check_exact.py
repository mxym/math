#!/usr/bin/env python3
"""Exact finite controls for the continuum proof, not its infinite theorem.

Standard library only. No floating powers, sampled exponent grid, numerical
solver, or submitted checker is used. The continuum toy is proved by a rational
range certificate. Activity counts are checked on every rational boundary and
intervening stratum of a finite example.
"""
import argparse
import itertools
import json
from fractions import Fraction as F
from pathlib import Path

def need(ok,message):
    if not ok:raise ArithmeticError(message)

def power2(n):
    need(type(n) is int,'integer exponent required')
    return F(2**n) if n>=0 else F(1,2**(-n))

def continuum_toy():
    # u=2^-s ranges over [1/4,1/2]. Derivative 1-2u>=0 on this
    # interval proves monotonicity of u-u^2; the extrema below are exact.
    ulo,uhi=F(1,4),F(1,2)
    need(1-2*uhi>=0,'quadratic derivative lower bound')
    dlo=ulo-ulo**2;dhi=2*(uhi-uhi**2)
    need((dlo,dhi)==(F(3,16),F(1,2)),'exact unperturbed difference range')
    threshold=F(7,160);rows=[]
    for r in [F(0),F(1,25),F(7,161),threshold,F(7,159),F(1,10)]:
        lower=dlo-2*r;upper=dhi+2*r
        if r<threshold:
            need(F(1,10)<lower<=upper<F(9,10),'strict complementary-gap exclusion')
            rows.append(dict(radius=str(r),valid=True,difference_enclosure=[str(lower),str(upper)]))
        else:
            # At s=2,t=1, use exact power values 1/4 and 1/16.
            x=F(143,160);errors=(-threshold,threshold)
            points=(x+F(1,4)+errors[0],x+F(1,16)+errors[1])
            need(points==(F(11,10),F(1)),'endpoint witness coordinates')
            need(all(abs(e)<=r for e in errors),'error budget witness')
            need(all((z-int(z)) in (F(0),F(1,10)) for z in points),'open-hole endpoints')
            rows.append(dict(radius=str(r),valid=False,witness=dict(s=2,t=1,x=str(x),errors=list(map(str,errors)),points=list(map(str,points)))))
    # At threshold, increasing t or decreasing s makes the difference strictly
    # exceed 1/10. Thus the counterexample cannot be found by interior sampling.
    need(dlo-2*threshold==F(1,10),'closed parameter boundary is sharp')
    return rows

def activity_strata():
    # z_n=4n, s in [1,2], output window (8,24); gaps are between 4 and 8.
    zs=[F(4*n) for n in range(1,7)]
    s0,s1=F(1),F(2);start,end=F(8),F(24);D=F(8)
    bounds={s0,s1}
    for z in zs:
        for point in (start/z,end/z):
            if s0<=point<=s1:bounds.add(point)
    bounds=sorted(bounds);representatives=[]
    for i,s in enumerate(bounds):
        representatives.append(('boundary',s))
        if i+1<len(bounds):representatives.append(('open interval',(s+bounds[i+1])/2))
    rows=[]
    for kind,s in representatives:
        active=[str(z) for z in zs if start<s*z<end]
        need(len(active)>=(end-start)/(2*D),'uniform strict-window count')
        rows.append(dict(stratum=kind,s=str(s),active_z=active,count=len(active)))
    need(min(x['count'] for x in rows)==1,'endpoint worst count retained')
    at_two=[z for z in zs if start<2*z<end]
    closed_at_two=[z for z in zs if start<=2*z<=end]
    need(len(at_two)==1 and len(closed_at_two)==3,'both activation endpoints excluded')
    return rows

def activation_closure_control():
    # Closed activation [1,2] has a nonclosed implication-failure set:
    # s_n<1 are inactive and converge to s=1, where 2^-s=1/2 lies in the hole.
    endpoint=F(1);value=F(1,2);hole=(F(2,5),F(3,5))
    need(hole[0]<value<hole[1],'limiting point is strictly inside hole')
    sequence=[F(1)-F(1,2**n) for n in range(2,12)]
    need(all(s<endpoint for s in sequence),'inactive approach to activation boundary')
    open_active=lambda s:F(1)<s<F(2)
    closed_active=lambda s:F(1)<=s<=F(2)
    need(not open_active(endpoint) and closed_active(endpoint),'exact activation conventions')
    return dict(closed_activation_failure_set_not_closed=True,open_activation_retains_limit=True,
                limiting_s='1',limiting_point='1/2',inactive_approach=list(map(str,sequence)))

def grid_curve_control():
    # q=2^s. Curves t=(3/8)q and t=(1/8)q^2 cross once at
    # q=3,t=9/8. With x=1/8,N=4 they are actual lifted grid boundaries.
    q=F(3);t=F(9,8);x=F(1,8);N=4
    need(F(3,8)*q==F(1,8)*q*q==t,'exponential curve intersection')
    need(F(2)<q<F(4) and F(1)<t<F(2),'interior parameter intersection')
    coordinates=[x+t/q,x+t/q**2]
    need(coordinates==[F(1,2),F(1,4)],'actual grid-boundary addresses')
    exact=[int(N*z) for z in coordinates]
    below=[int(N*(x+(t-F(1,64))/q**n)) for n in (1,2)]
    above=[int(N*(x+(t+F(1,64))/q**n)) for n in (1,2)]
    need(exact==above==[2,1] and below==[1,0],'right-cell boundary convention')
    return dict(q='3',s='log_2(3)',t=str(t),exact_keys=exact,keys_below=below,keys_above=above,
                pair_intersection_count=1)

def independent_terminal_control():
    p=F(1,7);rows=[]
    for m in range(2,7):
        # Exact conditioning identity. Shared auxiliary routing is permitted
        # only when the resulting terminal addresses remain distinct.
        averaged=sum(((1-p)**sum(bits) for bits in itertools.product((0,1),repeat=m)),F(0))/2**m
        independent=(1-p/2)**m
        shared=1-p+p*F(1,2**m)
        need(averaged==independent,'conditional terminal averaging')
        need(shared>independent,'one shared terminal address would invalidate the product')
        rows.append(dict(tests=m,distinct_terminal_failure=str(independent),shared_terminal_failure=str(shared)))
    return rows

def buffer_controls():
    rows=[]
    k=-2;q=3;alpha_over_s1=F(1,4);p=F(1,24)
    for U,T in [(18,20),(258,20),(514,40)]:
        exponent=alpha_over_s1*(U+k)
        need(exponent.denominator==1,'exact rational radius instance')
        r=(q*power2(-k)+1)*power2(-U)*power2(-int(exponent))
        N=2**(U+T+2)
        cost=4*N*r
        formula=power2(T+4)*(q*power2(-k)+1)*power2(-int(exponent))
        need(cost==formula,'absolute-position buffer cost identity')
        rows.append(dict(U=U,T=T,k=k,q=q,radius=str(r),cost=str(cost),below_budget=cost<p))
    need(not rows[0]['below_budget'] and all(x['below_budget'] for x in rows[1:]),'late position is necessary and useful')
    # These are scalar-interface tests, not full routing-tree calibrations.
    return rows

def double_buffer_control():
    endpoint=F(1,8);r=F(1,64);z=endpoint+r/2;error=r
    point=z+error
    need(z<endpoint+r,'unperturbed point belongs to first open buffer')
    need(point>endpoint+r,'one buffer would lose the permitted endpoint error')
    need(point<endpoint+2*r,'second open buffer retains the endpoint error')
    return dict(first_buffer_point=str(z),allowed_error=str(error),perturbed_point=str(point),
                first_buffer_right_endpoint=str(endpoint+r),second_buffer_right_endpoint=str(endpoint+2*r),
                one_buffer_fails=True,two_buffers_succeed=True)

def sparse_block_controls():
    rows=[]
    for m in range(4,8):
        R=2**(2**m);previous=2**(2**(m-1));following=R*R
        for U in (R,3*R//2,2*R):
            T=16*U.bit_length()
            need(T<F(U,4),'logarithmic span is short at this position')
            need(previous+m-1<F(U,2) and following>U+T,'only one input block can intersect')
            width=F(U+T,R)-F(U,R+m)
            need(width<1,'activating exponents cannot cover the compact interval')
            found=None
            for s in (F(1),F(3,2),F(2)):
                if all(not U<s*j<U+T for j in range(R,R+m+1)):
                    found=s;break
            need(found is not None,'exact missing-exponent witness')
            rows.append(dict(block=m,U=str(U),T=T,activation_interval_width=str(width),missing_exponent=str(found)))
    return rows

def main():
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--output',type=Path);args=parser.parse_args()
    result=dict(status='PASS',arithmetic='exact integer and rational',
                scope='finite controls; complete continuum/infinite proof is PROOF.txt',
                continuum_toy=continuum_toy(),activity_strata=activity_strata(),
                activation_closure=activation_closure_control(),grid_curve_intersection=grid_curve_control(),
                terminal_independence=independent_terminal_control(),buffer_identities=buffer_controls(),
                double_buffer=double_buffer_control(),positive_UBD_sparse_block_controls=sparse_block_controls())
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.output:args.output.write_text(text)
    print(text,end='')

if __name__=='__main__':main()
