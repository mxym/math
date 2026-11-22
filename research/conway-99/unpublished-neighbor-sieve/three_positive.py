"""Check the possible neighborhoods of the three positive sites of an F2 labeling.

The five separating inequalities use integer arithmetic. Run this module directly.
The optional support census imports signatures() and does its own spectral tests.
"""
from collections import Counter
from itertools import combinations, permutations, product

PAIRS = tuple(combinations(range(3), 2))
PAIR_MASKS = (3, 5, 6)


def members(mask):
    return tuple(i for i in range(3) if mask & (1 << i))


def signatures():
    """Outside cell populations and negative populations for each named positive graph."""
    for edges in ((), ((0, 1),), ((0, 1), (0, 2)), PAIRS):
        neighbors = [0]*3
        for i,j in edges:
            neighbors[i] |= 1 << j
            neighbors[j] |= 1 << i
        caps = [2-int((i,j) in edges)-(neighbors[i]&neighbors[j]).bit_count()
                for i,j in PAIRS]
        for triple in range(min(caps)+1):
            size = {7:triple, **{m:c-triple for m,c in zip(PAIR_MASKS,caps)}}
            for i in range(3):
                size[1<<i] = 14-neighbors[i].bit_count()-sum(
                    v for m,v in size.items() if i in members(m))
            size[0] = 96-sum(size.values())
            for values in product(*(range(size[m]+1) for m in (*PAIR_MASKS,7))):
                neg = dict(zip((*PAIR_MASKS,7),values))
                for i in range(3):
                    neg[1<<i] = 8+neighbors[i].bit_count()-sum(
                        v for m,v in neg.items() if i in members(m))
                neg[0] = 25-sum(neg.values())
                if all(0<=neg[m]<=size[m] for m in range(8)):
                    yield neighbors,size,neg


def key(g,size,neg):
    def transform(p):
        def mask(m):
            return sum(1<<p[j] for j in members(m))
        edges = sorted(tuple(sorted((p[i],p[j]))) for i,j in PAIRS if j in members(g[i]))
        return tuple(edges),tuple(sorted((mask(m),size[m],neg[m]) for m in range(8)))
    return min(transform(p) for p in permutations(range(3)))


def signature(g,size,neg):
    return (sum(m.bit_count() for m in g)//2,size[7],neg[7],
            *(neg[m] for m in PAIR_MASKS))


def profiles(g,size,neg):
    cells = [(m,1,i) for i,m in enumerate(g)]
    pop = [1]*3
    for m in range(8):
        for sign,count in ((-1,neg[m]),(0,size[m]-neg[m])):
            if count:
                cells.append((m,sign,None))
                pop.append(count)
    pools = []
    for site,(mask,sign,positive) in enumerate(cells):
        row = [int(j in members(mask)) for j in range(3)]+[0]*(len(cells)-3)
        if positive is not None:
            for j,(m,_,_) in enumerate(cells[3:],3):
                row[j] = pop[j]*int(positive in members(m))
            pools.append([tuple(row)])
            continue
        budget = [2-int(i in members(mask))-(mask&g[i]).bit_count() for i in range(3)]
        target = mask.bit_count()+4+4*sign
        active = [j for j in range(3,len(cells)) if cells[j][0]]
        empty = {t:j for j,(m,t,_) in enumerate(cells[3:],3) if not m}
        ways = []

        def enumerate_rows(h,left,needed,degree):
            if h == len(active):
                if any(left) or not 0<=needed<=degree:
                    return
                for t,count in ((-1,needed),(0,degree-needed)):
                    j = empty.get(t)
                    if j is None:
                        if count:
                            return
                    elif count>pop[j]-int(j==site):
                        return
                    else:
                        row[j] = count
                ways.append(tuple(row))
                return
            j = active[h]
            m,t,_ = cells[j]
            cap = min(pop[j]-int(j==site), needed if t<0 else degree-needed,
                      *(left[i] for i in members(m)))
            for v in range(cap+1):
                row[j] = v
                enumerate_rows(h+1,[a-v*int(i in members(m)) for i,a in enumerate(left)],
                               needed-v*int(t<0),degree-v)

        enumerate_rows(0,budget,target,14-mask.bit_count())
        if not ways:
            return None
        pools.append(ways)
    return cells,pop,pools


# Keys record positive edges, all triple sites, negative triple sites, then
# negative double sites for the named pairs 01, 02, 12.
DUALS = {
    (0,0,0,0,0,1): {'size.z5':-42,'pair.p1.z0':7,'pair.p1.n1':-28,
        'edge.p1.n2':27,'edge.p1.z2':-63,'pair.p1.n4':-28,'pair.n0.n0':21},
    (0,0,0,0,0,2): {'size.z5':-10,'pair.p0.n0':7,'edge.p0.z1':-8,
        'pair.p0.z2':2,'pair.p0.z3':2,'edge.p0.z3':6,'pair.p0.n4':-4},
    (0,0,0,0,1,1): {'size.n0':14,'size.n2':-10,'size.n5':-14,'edge.p0.n5':-14,
        'edge.p1.n2':-10,'edge.p1.z3':28,'edge.n0.z3':-14,'pair.z3.z3':7},
    (0,2,2,0,0,0): {'size.p0':-84,'size.n2':-11,'pair.p0.n1':3,
        'edge.p1.n2':-11,'pair.p2.n0':3,'pair.p2.n4':-3,'edge.p2.n4':-6,
        'pair.p2.n7':-6,'edge.n4.z4':-3,'pair.n7.n7':33},
    (1,1,1,0,1,1): {'size.n0':-52130,'size.n2':-735,'pair.p0.n0':26973,
        'pair.p0.n4':-810,'pair.p2.z0':150,'pair.p2.n4':270,'pair.p2.z4':420,
        'edge.p2.n6':1500,'edge.n0.z1':24985,'pair.n0.n5':270,'edge.z0.n4':270,
        'edge.z0.n7':5934,'pair.n1.z2':270,'pair.z1.z2':540,'edge.z1.z4':-150,
        'pair.n2.z2':-540,'edge.n2.z4':735,'edge.n2.n5':540,'pair.z2.n7':-1320,
        'edge.z2.n7':6474,'pair.n4.n7':-5154,'edge.n4.n7':7134,'pair.n6.n7':20400},
}


def check_separator(data,weights):
    cells,pop,pools = data
    indices = {('p'+str(p) if p is not None else ('n' if t<0 else 'z')+str(m)):i
               for i,(m,t,p) in enumerate(cells)}
    terms = []
    rhs = 0
    for name,c in weights.items():
        op,*args = name.split('.')
        j = indices[args[0]]
        k = j if op=='size' else indices[args[1]]
        terms.append((op,j,k,c))
        if op=='size':
            rhs += c*pop[j]
        elif op=='pair':
            rhs += 2*c*pop[j]*(pop[k]-int(j==k))
    assert rhs<0
    for i,rows in enumerate(pools):
        for r in rows:
            total = 0
            for op,j,k,c in terms:
                if op=='size':
                    value = int(i==j)
                elif op=='edge':
                    value = int(i==j)*r[k]-int(i==k)*r[j]
                else:
                    value = r[j]*(r[k]-int(j==k))+int(i==j)*r[k]
                total += c*value
            assert total>=0


def survivors():
    seen = set()
    verified = set()
    totals = Counter()
    for g,pop,neg in signatures():
        orbit = key(g,pop,neg)
        if orbit in seen:
            continue
        seen.add(orbit)
        sig = signature(g,pop,neg)
        data = profiles(g,pop,neg)
        if data is None:
            totals['missing row'] += 1
        elif sig in DUALS:
            check_separator(data,DUALS[sig])
            verified.add(sig)
        else:
            yield g,pop,neg
    assert len(seen)==38 and totals['missing row']==20 and verified==set(DUALS)


if __name__=='__main__':
    results = list(survivors())
    assert len(results)==13
    assert sorted({n[0] for g,s,n in results})==[3,4,5,6,7]
    for g,s,n in results:
        print(*signature(g,s,n), 'isolated negatives', n[0])
    print('38 signatures; 20 lack a row and 5 have exact separating inequalities; 13 remain.')
