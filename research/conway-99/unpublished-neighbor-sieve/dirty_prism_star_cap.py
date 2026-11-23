"""Exact certificate for the saturated-axis dirty prism obstruction.

See dirty-prism-star-cap.md for the graph-to-table reduction. The code
never assigns horizontal or unsaturated clean-cell adjacencies. It only
uses necessary vertical row moments and saturates common slots on V12.
"""
from itertools import combinations, product, permutations
from functools import lru_cache

I3 = tuple(range(3))
I4 = tuple(range(4))
PAIRS = tuple(combinations(I4, 2))
FACES = tuple(combinations(I3, 2))
PAIR_ROWS = tuple(product(I4, repeat=2))

def canonical(edges, rows):
    # Independent D8 relabeling of the signed-parent bits in one packet.
    charts = []
    for swap, shift in product((False, True), I4):
        p = tuple(((2*(x % 2) + x//2) if swap else x) ^ shift for x in I4)
        ee = tuple(sorted(tuple(sorted((p[x], p[y]))) for x, y in edges))
        rr = tuple(rows[p.index(x)] for x in I4)
        charts.append((ee, rr))
    return min(charts)

def packet(m, i):
    j, k = (t for t in I3 if t != i)
    out = set()
    for edges in combinations(PAIRS, m[i]):
        degrees = tuple(sum(x in e for e in edges) for x in I4)
        if 2 in degrees and any((x ^ y) not in (1, 2) for x, y in edges):
            continue  # a center uses the two true sign flips
        choices = []
        for d in degrees:
            choices.append([
                x for x in product(range(-1, 3), repeat=3)
                if -1 <= x[i] <= 1 and min(x[j], x[k]) >= 0
                and x[j] + x[k] == 2-d and x[i]+max(x[j], x[k]) <= 1
            ])
        targets = tuple(m[i]-sum(m) if k == i else 4-m[i] for k in I3)
        for rows in product(*choices):
            if tuple(map(sum, zip(*rows))) == targets:
                out.add(canonical(edges, rows))
    return tuple(sorted(out))

@lru_cache(maxsize=None)
def matrices(rows, cols):
    return tuple(
        lines for lines in product(*(tuple(combinations(I4, d)) for d in rows))
        if tuple(sum(y in line for line in lines) for y in I4) == cols
    )

def add(adj, x, y):
    adj[x] |= 1 << y
    adj[y] |= 1 << x

def vertical_graphs(packets, m):
    """Emit a record for each moment menu and each cap-vetted V12 graph."""
    M = sum(m)
    for chart in product(*packets):
        edges, rows = zip(*chart)
        allrows = sum(rows, ())
        if any(sum(x[i]*x[j] for x in allrows) != -3*m[3-i-j] for i,j in FACES):
            continue
        rem = tuple(28 - 8 - 2*(M-m[i]) - sum(x[i]**2 for x in allrows)
                    for i in I3)
        if any(r < 0 or r > 8 or r % 2 for r in rem):
            continue
        yield None  # marker for this moment-menu count
        options = []
        for i,j in FACES:
            k = 3-i-j
            options.append(matrices(tuple(1-x[i]-x[k] for x in rows[i]),
                                    tuple(1-x[j]-x[k] for x in rows[j])))
        base = [0]*12
        for i, ee in enumerate(edges):
            for x,y in ee:
                add(base,4*i+x,4*i+y)
        for mm in product(*options):
            adj = base.copy()
            for (i,j), lines in zip(FACES,mm):
                for x, line in enumerate(lines):
                    for y in line:
                        add(adj,4*i+x,4*j+y)
            if all((adj[x]&adj[y]).bit_count()
                   + (x//4 == y//4 and (x^y) in (1,2))
                   <= 2-(adj[x]>>y&1) for x,y in combinations(range(12),2)):
                yield adj,rem

def single_square(n):
    # Omit empty rows; fix the order of double then single rows.
    sizes = (2,)*n + (1,)*(4-2*n)
    partitions = {
        tuple(tuple(p[sum(sizes[:i]):sum(sizes[:i+1])])
              for i in range(len(sizes)))
        for p in permutations(I4)
    }
    out = set()
    for a,b in product(partitions, repeat=2):
        l = sum(1 << PAIRS.index(tuple(sorted(x))) for x in a if len(x)==2)
        r = sum(1 << PAIRS.index(tuple(sorted(x))) for x in b if len(x)==2)
        x = sum(1 << (4*i+j) for aa,bb in zip(a,b) for i,j in product(aa,bb))
        out.add((l,r,x))
    return tuple(sorted(out))

SQUARES = tuple(single_square(n) for n in range(3))
assert tuple(map(len,SQUARES)) == (24,72,18)

@lru_cache(maxsize=None)
def face(left, right, cross, negatives):
    """All necessary combined records for the two stars on one V-pair face."""
    masks = lambda ds: sum(1 << i for i,d in enumerate(ds) if d)
    ones = lambda ds: sum(1 << i for i,d in enumerate(ds) if d == 1)
    al,ar,ax = map(masks,(left,right,cross))
    bl,br,bx = map(ones,(left,right,cross))
    out = set()
    for n in range(3):
        m = negatives-n
        if not n <= m <= 2:
            continue
        admissible = lambda k: [
            (l,r,x) for l,r,x in SQUARES[k]
            if (l&~al)==(r&~ar)==(x&~ax)==0
        ]
        for (l,r,x),(L,R,X) in product(admissible(n),admissible(m)):
            if l&L&bl or r&R&br or x&X&bx:
                continue
            used_l = tuple((l>>i&1)+(L>>i&1) for i in range(6))
            used_r = tuple((r>>i&1)+(R>>i&1) for i in range(6))
            rr = tuple(d-(x>>i&1)-(X>>i&1) for i,d in enumerate(cross))
            row = tuple(sum(rr[4*i+j] for j in I4) for i in I4)
            col = tuple(sum(rr[4*i+j] for i in I4) for j in I4)
            out.add((used_l,used_r,row,col))
    return tuple(out)

def sub(a,b):
    return tuple(x-y for x,y in zip(a,b))

def star_join(adj, rem):
    debt = []
    for i in I3:
        debt.append(tuple(
            2-(adj[4*i+x]>>(4*i+y)&1)-((x^y) in (1,2))
            -(adj[4*i+x]&adj[4*i+y]).bit_count() for x,y in PAIRS))
    records = []
    for i,j in FACES:
        cross = tuple(2-(adj[4*i+x]>>(4*j+y)&1)
                      -(adj[4*i+x]&adj[4*j+y]).bit_count()
                      for x,y in PAIR_ROWS)
        records.append(face(debt[i],debt[j],cross,rem[3-i-j]//2))
    # For each packet, the two face records must use all its own debts
    # and leave equal row counts for the single-contact horizontal triples.
    by0 = {}
    for l,r,x,y in records[1]:  # face (0,2)
        by0.setdefault((l,x),set()).add((r,y))
    keys12 = set(records[2])
    for l,r,x,y in records[0]:  # face (0,1)
        for s,z in by0.get((sub(debt[0],l),x),()):
            if (sub(debt[1],r),sub(debt[2],s),y,z) in keys12:
                return True
    return False

def check(m):
    pp = tuple(packet(m,i) for i in I3)
    nmenu = ngraphs = njoin = 0
    for item in vertical_graphs(pp,m):
        if item is None:
            nmenu += 1
            continue
        ngraphs += 1
        njoin += star_join(*item)
    return tuple(map(len,pp)), nmenu, ngraphs, njoin

if __name__ == '__main__':
    expected = {
        (1,1,1): ((23,23,23),88,1546,0),
        (0,2,2): ((5,32,32),126,1464,0),
        (1,1,2): ((23,23,32),117,210,0),
    }
    for m in product(range(3),repeat=3):
        if tuple(sorted(m)) != m:
            continue
        got = check(m)
        if m in expected:
            assert got == expected[m], (m,got)
        else:
            assert got[1:] == (0,0,0), (m,got)
        print(m, *got)
