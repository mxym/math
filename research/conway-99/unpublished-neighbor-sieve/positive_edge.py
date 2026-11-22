"""Exact completion of the four unmarked neighbors at each end of a positive edge."""
from collections import Counter, defaultdict
from itertools import combinations
from three_positive import survivors
from three_positive_supports import outside_rounding, parent_pairs, support_graphs, valid_pairs, spectral


def options(core,residual,needed):
    n = len(core)
    closed = [row | (1<<i) for i,row in enumerate(core)]
    compatible = [sum(1<<i for i,r in enumerate(rr) if r>0) for rr in residual]
    negative = ((1<<n)-1)^7
    result = []

    def add_negatives(pool,left,mask,once,twice):
        if not left:
            result.append(mask)
            return
        while pool.bit_count()>=left:
            bit = pool & -pool
            pool ^= bit
            i = bit.bit_length()-1
            covered = closed[i]
            if not (covered & twice):
                add_negatives(pool & compatible[i],left-1,mask|bit,
                              once|covered,twice|(once&covered))

    for m in needed:
        pool = negative
        once = twice = 0
        for j in range(3):
            if not m&(1<<j):
                continue
            if (m & ~(1<<j)) & ~compatible[j] or twice & closed[j]:
                break
            pool &= compatible[j]
            twice |= once & closed[j]
            once |= closed[j]
        else:
            add_negatives(pool,4+m.bit_count(),m,once,twice)
    return result


def pairings(free):
    if not free:
        yield ()
        return
    for index in range(1,len(free)):
        for tail in pairings(free[1:index]+free[index+1:]):
            yield ((free[0],free[index]),)+tail


def extended(core,masks,edges):
    n = len(core)
    out = core.copy()+list(masks)
    for a,mask in enumerate(masks,n):
        for j in range(n):
            if mask & (1<<j):
                out[j] |= 1<<a
    for a,b in edges:
        out[n+a] |= 1<<(n+b)
        out[n+b] |= 1<<(n+a)
    return out


def neighborhoods(core,size,neg,p):
    n = len(core)
    residual = [[(14-core[i].bit_count()) if i==j else
                 2-((core[i]>>j)&1)-(core[i]&core[j]).bit_count()
                 for j in range(n)] for i in range(n)]
    assert residual[p][p]==4
    root = 1<<p
    needed = Counter({m:size[m]-neg[m] for m in range(8) if m&root and size[m]>neg[m]})
    masks = [m^root for m in options(core,residual,needed)]
    once = sum(1<<i for i in range(n) if residual[p][i]==1)
    twice = sum(1<<i for i in range(n) if residual[p][i]==2)
    pairs = defaultdict(list)
    for i,x in enumerate(masks):
        for j in range(i+1,len(masks)):
            y = masks[j]
            both = x&y
            if both.bit_count()<=1 and not (both&~twice) and not ((x|y)&~(once|twice)):
                pairs[x^y,both].append((i,j))
    for (single,double),left in pairs.items():
        other = ((once&~single)|(twice&single),twice&~(single|double))
        for i,j in left:
            for k,l in pairs.get(other,()):
                if j>=k:
                    continue
                values = [masks[v]|root for v in (i,j,k,l)]
                if Counter(v&7 for v in values)!=needed:
                    continue
                if any((x&y).bit_count()>2 for x,y in combinations(values,2)):
                    continue
                free = [h for h,m in enumerate(values) if not (core[p]&m)]
                for mates in pairings(free):
                    if any(values[a]&values[b]!=root for a,b in mates):
                        continue
                    if valid_pairs(extended(core,values,mates)):
                        yield values,mates


def census():
    answer = []
    for g,size,neg in survivors():
        if not g[0]:
            continue
        tested = accepted = rounded = 0
        for core in support_graphs(g,neg):
            if not valid_pairs(core) or not spectral(core):
                continue
            tested += 1
            if all(next(neighborhoods(core,size,neg,p),None) is not None for p in (0,1)):
                accepted += 1
                if parent_pairs(core,2) and outside_rounding(core):
                    rounded += 1
        answer.append((tested,accepted,rounded))
        print('Negative double classes',*(neg[m] for m in (3,5,6)),
              'supports before, after endpoint neighborhoods, and after both outside tests',
              tested,accepted,rounded,flush=True)
    return answer


if __name__=='__main__':
    assert census()==[(99,7,6),(76,22,18)]
