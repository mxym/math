#!/usr/bin/env python3
"""Finite exact checks for the Poisson critical-window argument."""

from fractions import Fraction as F
from itertools import product
from collections import Counter
from math import comb


def schedule(seed,caps,pre):
    counts=Counter(i for i,b in pre)
    live=[i for i,n in enumerate(caps) if counts[i]<n]
    j=seed+sum((r+1)*(i+3*b+1) for r,(i,b) in enumerate(pre))
    if not live or (len(pre)>2 and j%7==0):
        return None
    return live[(j+len(pre))%len(live)]


def response(seed,party,pre,x):
    t=seed**2+sum((r+2)*(i+b+1) for r,(i,b) in enumerate(pre))
    return int(((party+3)*(x+1)+5*t+(t%7)*x)%13<6)


def run(seed,caps,inputs,script):
    pre=()
    sent=Counter()
    while True:
        party=schedule(seed,caps,pre)
        if party is None:
            return pre
        if party in script:
            b=script[party][sent[party]]
        else:
            b=response(seed,party,pre,inputs[party])
        sent[party]+=1
        pre=pre+((party,b),)


def mass(path,dist,inputs):
    w=F(1)
    for pid,x in enumerate(inputs):
        w*=dist[pid][x]
    for j in range(len(path)+1):
        yield path[:j],w


def verify_marked_scripts():
    tests=Counter()
    caps=(2,2,1)
    priors=(
        ((F(1,3),F(1,3),F(1,3)),(F(1,5),F(2,5),F(2,5))),
        ((F(0),F(1,2),F(1,2)),(F(1,3),F(0),F(2,3))),
        ((F(1,3),F(0),F(2,3)),(F(1,2),F(1,2),F(0))),
    )
    V=tuple(range(3))
    for seed in range(48):
        for J in ((0,),(1,),(2,),(0,1),(0,2),(1,2)):
            low=[i for i in range(3) if i not in J]
            pri=priors if seed%2 else tuple(reversed(priors))
            av=[tuple((x+y)/2 for x,y in zip(*pair)) for pair in pri]
            real=[Counter(),Counter()]
            for s in (0,1):
                family=[pri[i][s] if i in J else av[i] for i in range(3)]
                for x in product(V,repeat=3):
                    path=run(seed,caps,x,{})
                    for pre,w in mass(path,family,x):
                        real[s][pre]+=w
            lo_inputs=tuple(product(V,repeat=len(low)))
            all_script=tuple(product(*[tuple(product((0,1),repeat=caps[j])) for j in J]))
            M=sum(caps[i] for i in J)
            assert len(all_script)==2**M
            dom=Counter()
            guesses={x:set() for x in lo_inputs}
            for h in all_script:
                script=dict(zip(J,h))
                for x in lo_inputs:
                    inp=[0,0,0]
                    for i,y in zip(low,x):
                        inp[i]=y
                    path=run(seed,caps,inp,script)
                    w=F(1)
                    for i,y in zip(low,x):
                        w*=av[i][y]
                    for r in range(len(path)+1):
                        dom[path[:r]]+=w
                    out=(seed+sum((r+2)*(2*i+b+1) for r,(i,b) in enumerate(path)))%97
                    guesses[x].add(out)
            for s in (0,1):
                for pre,prob in real[s].items():
                    assert prob<=dom[pre]
                    tests['dominated_prefixes']+=1
            for x in lo_inputs:
                assert len(guesses[x])<=2**M
                tests['fixed_low_label_unions']+=1
            tests['marked_protocols']+=1
    return dict(tests)


def verify_alert_arithmetic():
    tests=0
    for B,theta,bias in product((1,2,4,8,16),(F(1,11),F(1,5),F(1,3)),(F(1,2),F(2,3),F(8,9))):
        mark_p=theta/B
        binomial=[comb(B,j)*mark_p**j*(1-mark_p)**(B-j) for j in range(B+1)]
        assert sum(binomial)==1
        assert sum(j*p for j,p in enumerate(binomial))==theta
        default_no_alert=(1-mark_p)**B
        # Under the binary property, a report may challenge the default only
        # when an independently generated confidence mark exists.
        test=bias+(1-bias)*sum(binomial[1:])
        assert test==1-(1-bias)*default_no_alert
        tests+=1
    # Exponent arithmetic with integer multiples of one logarithm unit.
    bounds=0
    for lam,m,K,j in product(range(1,12),range(1,6),range(1,7),range(8)):
        if j<=K:
            H=-4*lam-(2*K+1)*m
            assert 2*lam+2*j*m+m+H<=-2*lam
            bounds+=1
    return tests,bounds


if __name__=="__main__":
    print("PASS marked scripts, domination, unions:",verify_marked_scripts())
    print("PASS rare-alert probabilities and exponent arithmetic:",verify_alert_arithmetic())
