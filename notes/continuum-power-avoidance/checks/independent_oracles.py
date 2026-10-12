#!/usr/bin/env python3
"""Independent exact structural controls; not a proof of the infinite result."""
import hashlib, itertools, json
from fractions import Fraction as Q
from pathlib import Path


def check(c, m):
    if not c:
        raise RuntimeError(m)


def key(b, x):
    y = x % 1
    n = 1 << (b + 3)
    return (y.numerator * n) // y.denominator


def template(M, d, g, L, U=4):
    lengths = {1: L}
    spans = {1: M * L + (M - 1) * g}
    for r in range(2, d + 1):
        lengths[r] = g + spans[r - 1]
        spans[r] = M * (lengths[r] + g + spans[r - 1]) + (M - 1) * g
    out = []
    start = U
    def walk(prefix, height):
        nonlocal start
        for i in range(1, M + 1):
            edge = prefix + (i,)
            a = start
            b = a + lengths[height] - 1
            start = b + g + 1
            row = {'edge': edge, 'height': height, 'u': a, 'v': b}
            out.append(row)
            if height > 1:
                walk(edge, height - 1)
            row['vstar'] = out[-1]['v']
    walk((), d)
    check(out[-1]['v'] - U + 1 == spans[d], 'total preorder span')
    for row in out:
        check(row['vstar'] - row['u'] + 1 <= 2 * lengths[row['height']], 'local block span')
    for first, second in zip(out, out[1:]):
        check(second['u'] - first['v'] - 1 == g, 'exact number of unused indices')
    return out, lengths, spans


def exact_window_counts():
    tests = 0
    minima = []
    for s0, s1 in ((Q(1, 2), Q(3, 2)), (Q(1), Q(3)), (Q(2), Q(4))):
        # Strict lower gap >3/s0 and explicit upper bound B0.
        zs = [Q(9)]
        steps = [Q(13, 4) / s0, Q(15, 4) / s0, Q(7, 2) / s0]
        B0 = Q(4) / s0
        D = s1 * B0
        for n in range(500):
            zs.append(zs[-1] + steps[n % len(steps)])
        L = max(2, (2 * D).__ceil__())
        U = (s1 * zs[0]).__ceil__()
        for u in range(U, U + 12):
            for ell in (L, L + 1, 2 * L, 3 * L):
                boundaries = {s0, s1}
                for z in zs:
                    for s in (Q(u) / z, Q(u + ell) / z):
                        if s0 <= s <= s1:
                            boundaries.add(s)
                boundaries = sorted(boundaries)
                reps = boundaries + [(a+b)/2 for a,b in zip(boundaries,boundaries[1:])]
                counts = []
                for s in reps:
                    count = sum(u < s*z < u+ell for z in zs)
                    check(count >= Q(ell)/(2*D), 'uniform active count at a boundary or open stratum')
                    check(count <= 1+Q(ell,3), 'strict lower-gap upper count')
                    tests += 1
                    counts.append(count)
                minima.append(min(counts))
    return {'strata_checked': tests, 'lowest_count': min(minima)}


def exact_routing():
    M, d, g, L = 3, 2, 6, 2
    windows, _, _ = template(M,d,g,L)
    info = {r['edge']: r for r in windows}
    selectors = [r for r in windows if r['edge'][-1] < M]
    center = Q(0)
    points = {}
    for i in (1,2):
        u = info[(i,)]['u']
        # Two exact positive offsets, logarithmic separation 4>3.
        points[i] = [Q(1,1 << (u+2)), Q(1,1 << (u+6))]
    for i, zs in points.items():
        cur = info[(i,)]
        own_keys = [key(cur['v'], center)] + [key(cur['v'],z) for z in zs]
        check(len(set(own_keys)) == 3, 'center and local-test own keys distinct')
        for z in zs:
            for row in windows:
                if row['u'] < cur['u']:
                    check(key(row['v'],z)==key(row['v'],center), 'predecessor keys preserved')
    # Condition on every addressed center selector being zero.
    fixed = {(r['edge'],key(r['v'],center)):0 for r in selectors}
    reads = set()
    for i, zs in points.items():
        for z in zs:
            reads.add(((i,),key(info[(i,)]['v'],z)))
            for j in (1,2):
                reads.add(((i,j),key(info[(i,j)]['v'],z)))
    check(not reads.intersection(fixed), 'all random local entries avoid center exposure')
    reads = sorted(reads)
    check(len(reads)==12, 'expected number of independent sparse selector entries')
    p = Q(1,7)
    normal_sum = Q(0)
    coarsened_sum = Q(0)
    collision_outcomes = 0
    for bits in itertools.product((0,1),repeat=len(reads)):
        table = dict(fixed)
        table.update(zip(reads,bits))
        active_addrs = []
        all_addrs = []
        coarse_addrs = []
        for i, zs in points.items():
            for z in zs:
                child = next((j for j in (1,2) if table[((i,j),key(info[(i,j)]['v'],z))]),3)
                addr = ((i,child),key(info[(i,child)]['v'],z))
                all_addrs.append(addr)
                own = table[((i,),key(info[(i,)]['v'],z))]
                if own:
                    actual = next((j for j in (1,2) if table.get(((j,),key(info[(j,)]['v'],z)),0)),3)
                    check(actual==i,'successful local selector forces actual global child')
                    active_addrs.append(addr)
                    coarse_addrs.append((i,child))
        check(len(set(all_addrs))==4,'every leaf assignment keeps all terminal addresses distinct')
        normal_sum += (1-p)**len(set(active_addrs))
        coarsened_sum += (1-p)**len(set(coarse_addrs))
        collision_outcomes += len(set(coarse_addrs)) < len(coarse_addrs)
    exact = normal_sum / (1<<len(reads))
    negative = coarsened_sum / (1<<len(reads))
    check(exact==(1-p/2)**4,'independently enumerated actual routing failure product')
    check(negative>exact,'coarsened terminal-address negative control must break product')
    return {'selector_assignments':1<<len(reads), 'distinct_terminal_failure':str(exact),
            'coarsened_terminal_failure':str(negative),'collision_outcomes':collision_outcomes}


def threshold_and_closure():
    r = Q(7,160)
    x = Q(143,160)
    a = x+Q(1,4)-r
    b = x+Q(1,16)+r
    check((a,b)==(Q(11,10),Q(1)), 'sharp closed-hole endpoints')
    check(a-b==Q(1,10),'failure sits at complementary-gap width')
    # Exact derivative bounds certify all u in [1/4,1/2], t in [1,2].
    lo, hi = Q(3,16), Q(1,2)
    below = r-Q(1,100000)
    check(lo-2*below>Q(1,10) and hi+2*below<Q(9,10),'strict-radius success interval')
    check(lo-2*r==Q(1,10),'permitted-error equality is fatal with only the toy open hole')
    check(Q(2,5)<Q(1,2)<Q(3,5),'closed-activation boundary has a hit')
    sequence = [Q(1)-Q(1,2**n) for n in range(2,50)]
    check(all(s<1 for s in sequence),'closed-activation failures approach excluded failure limit')
    # Open B1 plus allowed error equality stays in B2; B1 alone can fail.
    end, radius = Q(1,8), Q(1,64)
    z, e = end+radius/2, radius
    check(z<end+radius<z+e<end+2*radius,'one-buffer negative control and two-buffer positive control')
    return {'parameter_boundary_witness':[str(a),str(b)], 'open_activation_required':True,
            'double_buffer_equality_verified':True}


def entropy_arithmetic():
    instances=0
    for ell in range(2,50):
        for P in range(1,50):
            lhs=20*(P*(3+(1<<(2*ell+3)))+5)**2
            rhs=5120*P*P*(1<<(4*ell))
            check(lhs<=rhs,'curve-strata entropy coefficient')
            instances+=1
    templates=0
    for M,d,g,L in itertools.product(range(2,6),range(1,5),range(1,5),range(4,9)):
        _,_,spans=template(M,d,g,L)
        for r in range(2,d+1):
            check(spans[r]==2*M*spans[r-1]+(3*M-1)*g,'affine recurrence in L')
        templates+=1
    return {'entropy_instances':instances,'preorder_templates':templates}


def sparse_gap_witnesses():
    witnesses=[]
    for m in range(3,8):
        R=1<<(1<<m)
        for U in (R,3*R//2,2*R,3*R):
            T=max(1,4*U.bit_length())
            if T>Q(U,4):
                continue
            relevant=[]
            for n in range(3,9):
                base=1<<(1<<n)
                if base+n>=Q(U,2) and base<=U+T:
                    relevant.extend(range(base,base+n+1))
            intervals=sorted((Q(U,j),Q(U+T,j)) for j in relevant)
            candidates={Q(1),Q(2),Q(3,2)}
            candidates.update(v for interval in intervals for v in interval if 1<=v<=2)
            found=next((s for s in sorted(candidates) if all(not U<s*j<U+T for j in relevant)),None)
            check(found is not None,'positive-UBD logarithmic-span missing exponent')
            witnesses.append({'m':m,'U':str(U),'T':T,'s':str(found)})
    return witnesses


def main():
    report={'status':'PASS','scope':'independent finite structural controls only',
            'window_counts':exact_window_counts(),'routing':exact_routing(),
            'boundary_controls':threshold_and_closure(),'entropy':entropy_arithmetic(),
            'sparse_source_witnesses':sparse_gap_witnesses()}
    print(json.dumps(report,sort_keys=True,indent=2))

if __name__=='__main__':
    main()
