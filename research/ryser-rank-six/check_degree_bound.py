"""Exact replay of the nineteen-edge necessary bound; no SAT dependency.

Universal graph-to-degree reductions and the scalar proof are in
NINETEEN_EDGE_BOUND.md. This checker expands the complete finite case space
and compares it with a different six-type integer certificate.
"""
from itertools import combinations_with_replacement
from math import comb


def require(condition, label):
    if not condition:
        raise ValueError(label)


def partitions(total):
    def rec(left, maximum, prefix):
        if left == 0:
            if len(prefix) >= 6:
                yield tuple(prefix)
            return
        for value in range(min(left, maximum), 1, -1):
            yield from rec(left-value, value, prefix+(value,))
    return list(rec(total, total, ()))


def excess_patterns(total):
    # Independent generation by part length and partitions of excess over two.
    def rec(left, maximum, slots, prefix):
        if slots == 0:
            if left == 0:
                yield tuple(2+a for a in prefix)
            return
        for value in range(min(left, maximum), -1, -1):
            yield from rec(left-value, value, slots-1, prefix+(value,))
    out=[]
    for width in range(6, total//2+1):
        out.extend(rec(total-2*width, total-2*width, width, ()))
    return out


def energy(pattern):
    return sum(comb(d,2) for d in pattern)


def mutual(p, q, total=18):
    return sum(comb(max(0,d+e-total+7),2) for d in p for e in q)


def count_vectors(slots, total):
    if slots == 1:
        yield (total,)
        return
    for first in range(total+1):
        for rest in count_vectors(slots-1,total-first):
            yield (first,)+rest


def main():
    for total in range(12,19):
        p=partitions(total)
        require(len(p)==len(set(p)) and set(p)==set(excess_patterns(total)),
                f'independent partition generators at N={total}')
        require(all(sum(x)==total and len(x)>=6 and min(x)>=2 for x in p),
                'partition domain')
        if total<=15:
            require(max(map(energy,p))==comb(total-10,2)+5, 'small-edge maximum')
            require(6*max(map(energy,p))<comb(total,2), 'small-edge contradiction')
        elif total==16:
            require(all(energy(x)<= (20 if max(x)==6 else 17) for x in p),
                    'sixteen-edge table')
        elif total==17:
            bound={3:16,4:18,5:20,6:22,7:26}
            require(all(energy(x)<=bound[max(x)] for x in p), 'seventeen-edge table')
    pats=partitions(18)
    require(len(pats)==19, 'nineteen degree patterns')
    types=[(8,2,2,2,2,2),(7,3,2,2,2,2),(6,4,2,2,2,2),
           (5,5,2,2,2,2),(5,4,3,2,2,2),(4,4,4,2,2,2)]
    expected_energy=[33,28,25,24,22,21]
    expected_mutual=[[10,6,3,2,1,0],[6,3,1,0,0,0],[3,1,0,0,0,0],
                     [2,0,0,0,0,0],[1,0,0,0,0,0],[0,0,0,0,0,0]]
    require(list(map(energy,types))==expected_energy, 'six-type energy table')
    require([[mutual(p,q) for q in types] for p in types]==expected_mutual,
            'six-type mutual table')
    for p in pats:
        if max(p)==8: q=types[0]
        elif max(p)==7: q=types[1]
        elif max(p)==6: q=types[2]
        elif max(p)==5 and p.count(5)==2: q=types[3]
        elif max(p)==5: q=types[4]
        else: q=types[5]
        require(energy(q)>=energy(p), 'dominating energy')
        require(all(mutual(q,r)<=mutual(p,r) for r in pats), 'dominating every partner')

    # Direct pattern enumeration, without the six-type reduction.
    values=list(map(energy,pats))
    cross=[[mutual(p,q) for q in pats] for p in pats]
    maximum=-10**9; checked=0
    for inds in combinations_with_replacement(range(19),6):
        s=sum(values[i] for i in inds)
        b0=sum(cross[inds[i]][inds[j]] for i in range(6) for j in range(i+1,6))
        value=5*(s-153)-2*b0
        maximum=max(maximum,value); checked+=1
        require(value<0, 'direct nineteen-pattern contradiction')
    require(checked==comb(24,6)==134596 and maximum==-1, 'complete enumeration count/max')

    # Independent reduced-type composition enumeration and polynomial check.
    cases=0; best=-10**9
    for ns in count_vectors(6,6):
        s=sum(n*v for n,v in zip(ns,expected_energy))
        b0=sum(expected_mutual[i][i]*comb(ns[i],2) for i in range(6))
        b0+=sum(expected_mutual[i][j]*ns[i]*ns[j] for i in range(6) for j in range(i+1,6))
        a,b,c,d,e,f=ns
        poly=(-10*a*a-12*a*b-6*a*c-4*a*d-2*a*e+70*a
              -3*b*b-2*b*c+38*b+20*c+15*d+5*e-135)
        require(poly==5*(s-153)-2*b0, 'count polynomial identity')
        require(poly<=-1, 'integer scalar certificate')
        best=max(best,poly); cases+=1
    require(cases==comb(11,5)==462 and best==-1, 'reduced enumeration count/max')
    # A missing repeated-intersection entry must be detected independently.
    damaged=[row.copy() for row in expected_mutual]; damaged[0][3]=0
    require(damaged!=[[mutual(p,q) for q in types] for p in types],
            'negative control: damaged matrix rejected')
    print('N=12..17 degree tables and independent partition generation: EXACT PASS')
    print('N=18: all 19 patterns and all partner-dominance comparisons: EXACT PASS')
    print('134596 complete six-part combinations: maximum necessary deficit -1, EXACT PASS')
    print('462 independent type-count combinations and polynomial certificate: EXACT PASS')


if __name__=='__main__':main()
