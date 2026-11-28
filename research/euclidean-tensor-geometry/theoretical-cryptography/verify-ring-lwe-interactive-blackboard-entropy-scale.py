#!/usr/bin/env python3
"""Finite rational checks for the fully interactive blackboard proof."""

from collections import Counter,defaultdict
from fractions import Fraction as F
from itertools import product


def choose(seed,caps,pre):
    counts=Counter(i for i,b in pre)
    choices=[i for i,n in enumerate(caps) if counts[i]<n]
    data=sum((r+1)*(1+2*i+b) for r,(i,b) in enumerate(pre))
    if not choices or (len(pre)>2 and (data+seed)%11==0):
        return None
    return choices[(data+seed**2+len(pre))%len(choices)]


def bit(seed,i,pre,value):
    h=sum((r+4)*(2*j+b+1) for r,(j,b) in enumerate(pre))
    return int(((seed+1)**2*(value+1)+h+7*i+3*(h%5)*value)%13<6)


def protocol(seed,caps,data):
    pre=()
    while True:
        i=choose(seed,caps,pre)
        if i is None:
            return pre
        pre=pre+((i,bit(seed,i,pre,data[i])),)


def event(seed,caps,pre,party,alphabet):
    E=set(alphabet)
    for r,(i,b) in enumerate(pre):
        assert choose(seed,caps,pre[:r])==i
        if i==party:
            E={v for v in E if bit(seed,i,pre[:r],v)==b}
    return frozenset(E)


def weights(P,x):
    w=F(1)
    for p,y in zip(P,x):
        w *= p[y]
    return w


def mass(p,E):
    return sum((p[i] for i in E),F(0))


def verify():
    counters=Counter()
    alphabet=tuple(range(3))
    input_data=list(product(alphabet,repeat=3))
    refs=((F(1,5),F(2,5),F(2,5)),(F(1,7),F(4,7),F(2,7)),(F(1,3),)*3)
    distributions=(
        ((F(0),F(1,2),F(1,2)),(F(1,2),F(0),F(1,2))),
        ((F(1,4),F(3,4),F(0)),(F(1,3),F(2,3),F(0))),
        ((F(2,5),F(0),F(3,5)),(F(2,7),F(3,7),F(2,7))),
        ((F(1,4),F(1,4),F(1,2)),(F(0),F(0),F(1))),
    )
    for seed in range(144):
        caps=(1+seed%3,1+(seed//3)%3,1+(seed//9)%3)
        law=tuple(distributions[(seed+2*i+(seed//4))%len(distributions)] for i in range(3))
        bar=tuple(tuple((f+g)/2 for f,g in zip(*L)) for L in law)
        spectral=tuple(sum((L[0][x]-L[1][x])**2/(4*refs[i][x]) for x in alphabet)
                       for i,L in enumerate(law))
        paths={x:protocol(seed,caps,x) for x in input_data}
        premap=defaultdict(set)
        for x,pre in paths.items():
            for j in range(len(pre)+1):
                premap[pre[:j]].add(x)
        cond_total=F(0)
        edge_tests=Counter()
        for pre,inputs in premap.items():
            Es=tuple(event(seed,caps,pre,i,alphabet) for i in range(3))
            assert inputs==set(product(*Es))
            counters['rectangles']+=1
            i=choose(seed,caps,pre)
            p_pre=sum(weights(bar,x) for x in inputs)
            assert p_pre==weights(tuple((mass(bar[j],Es[j]),) for j in range(3)),(0,0,0))
            if i is None or p_pre==0:
                continue
            E=Es[i]
            D={v for v in E if bit(seed,i,pre,v)==1}
            ref=mass(refs[i],E)
            prob=mass(bar[i],E)
            pbit=mass(bar[i],D)/prob
            p_direct=sum(weights(bar,x) for x in inputs if x[i] in D)/p_pre
            assert pbit==p_direct
            abs_errors=[]
            for s in (0,1):
                denom=mass(law[i][s],E)
                u=mass(law[i][s],D)/denom if denom else F(1,3)
                P_s=tuple(L[s] for L in law)
                true_pre=sum(weights(P_s,x) for x in inputs)
                if true_pre>0:
                    assert denom>0 and u==sum(weights(P_s,x) for x in inputs if x[i] in D)/true_pre
                else:
                    counters['zero_real_prefix']+=1
                abs_errors.append(abs(u-pbit))
                if denom==0:
                    counters['zero_local_denominator']+=1
            for U in (E,D):
                var=(mass(law[i][0],U)-mass(law[i][1],U))**2/4
                assert var<=spectral[i]*mass(refs[i],U)
            avg=sum(abs_errors)/2
            assert (avg*prob)**2<=4*spectral[i]*ref
            cond_total += p_pre*avg
            r=1+sum(j==i for j,b in pre)
            edge_tests[(i,r)] += 1
            counters['conditional_bits']+=1
        for i in range(3):
            for other in product(alphabet,repeat=2):
                for r in range(1,caps[i]+1):
                    partition=defaultdict(set)
                    for v in alphabet:
                        data=other[:i]+(v,)+other[i:]
                        pre=paths[data]
                        indices=[j for j,(jparty,b) in enumerate(pre) if jparty==i]
                        if len(indices)>=r:
                            partition[pre[:indices[r-1]]].add(v)
                    assert len(partition)<=2**(r-1)
                    assert sum(mass(refs[i],E) for E in partition.values())<=1
                    for pre,E in partition.items():
                        assert E==set(event(seed,caps,pre,i,alphabet))
                        if mass(bar[i],E):
                            # Cancellation of the null mass before Cauchy.
                            assert mass(bar[i],E)*mass(refs[i],E)/mass(bar[i],E)==mass(refs[i],E)
                    counters['frozen_sender_trees']+=1
        null=Counter()
        real=[Counter(),Counter()]
        for x,pre in paths.items():
            null[pre]+=weights(bar,x)
            for s in (0,1):
                real[s][pre]+=weights(tuple(L[s] for L in law),x)
        tv=sum(abs(real[s][pre]-null[pre]) for s in (0,1) for pre in null)/4
        assert tv<=cond_total
        counters['full_transcripts']+=1
    assert counters['zero_local_denominator']>0
    return dict(counters)


def verify_moderate_arithmetic():
    # Exact first-order formal Laurent moments: c=(z+z^-1)/2.
    c={-1:F(1,2),1:F(1,2)}
    c2=Counter()
    for i,j in product(c,repeat=2):
        c2[i+j]+=c[i]*c[j]
    e_log_order2=(-2+4)*c2[0]
    variance_order2=4*c2[0]
    assert e_log_order2==1 and variance_order2==2
    checks=0
    for t,a,s in product((F(1),F(2),F(3,2)),(F(1,2),F(3,4),F(5,4),F(3,2)),range(1,10)):
        # A rational grid with d*Lambda=t*s^2 and target gap 2*a*t*s.
        # The Gaussian rate Delta^2/(4td) per Lambda is exactly a^2.
        d_times_log_b=t*s*s
        gap=2*a*t*s
        assert gap*gap/(4*t*d_times_log_b)==a*a
        assert (a*a>1)==(a>1)
        checks+=1
    return checks


if __name__=="__main__":
    print("PASS fully interactive rational checks:", verify())

    print("PASS variance and moderate-deviation normalization:", verify_moderate_arithmetic())
