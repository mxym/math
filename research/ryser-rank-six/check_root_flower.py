"""Exact root-flower/label normalization diagnostic on the F5 affine plane."""
from itertools import combinations, product
from search import cover_at_most


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    # Truth-table test for the private-neighbour equivalence and the distinct
    # two-input critical-hit equivalence, independent of the SAT solver.
    def satisfies(clauses,values):
        return all(any(values[abs(lit)]==(lit>0) for lit in clause) for clause in clauses)
    private_literals=[1,-2,-3,-4,-5,-6]
    private_clauses=[[-7,lit] for lit in private_literals]+[[7]+[-lit for lit in private_literals]]
    for bits in product((False,True),repeat=7):
        values=dict(enumerate(bits,1))
        require(satisfies(private_clauses,values)==(bits[6]==(bits[0] and not any(bits[1:6]))),
                'private-neighbour literal truth table')
    for bits in product((False,True),repeat=3):
        values=dict(enumerate(bits,1))
        require(satisfies([[-3,1],[-3,2],[-1,-2,3]],values)==(bits[2]==(bits[0] and bits[1])),
                'critical-hit literal truth table')
    edges=[tuple((y-d*x)%5 for d in range(5))+(x,) for x in range(5) for y in range(5)]
    root=edges[0]
    flower=[]
    for c in range(6):
        f=next(e for e in edges if [i for i in range(6) if e[i]==root[i]]==[c])
        flower.append(f)
    require(len(set([root]+flower))==7, 'six distinct private neighbours')
    rows=[root]+flower+[e for e in edges if e!=root and e not in flower]
    maps=[{} for _ in range(6)]
    normalized=[]
    for e in rows:
        out=[]
        for c,v in enumerate(e):
            if v not in maps[c]:maps[c][v]=len(maps[c])
            out.append(maps[c][v])
        normalized.append(tuple(out))
    require(normalized[0]==(0,)*6, 'normalized root')
    for c in range(6):
        require([i for i in range(6) if normalized[c+1][i]==0]==[c], 'private-neighbour units')
    require(normalized[1]==(0,1,1,1,1,1) and normalized[2][0]==1, 'first nonzero labels')
    for c in range(6):
        seen=set()
        for e in normalized:
            require(e[c]<2 or e[c]-1 in seen, 'label-precedence clause')
            seen.add(e[c])
    require(all(any(a==b for a,b in zip(e,f)) for e,f in combinations(normalized,2)), 'intersection')
    for i,e in enumerate(normalized):
        for c in range(6):
            require(any(i!=j and [d for d in range(6) if e[d]==f[d]]==[c]
                        for j,f in enumerate(normalized)), 'every-row private-neighbour condition')
    cover,_=cover_at_most(normalized,width=6)
    require(cover is not None and len(cover)==5, 'flower is necessary, not sufficient')
    print('F5 private-neighbour normalization and all precedence clauses: EXACT PASS')
    print('Five-cover retained: root flower alone does not establish a counterexample')


if __name__=='__main__':main()
