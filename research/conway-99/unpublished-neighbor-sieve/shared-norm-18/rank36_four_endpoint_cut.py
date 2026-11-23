"""Exact 19-row certificate from the endpoint intersection and Turan bounds."""
from itertools import product
from rank36_four_fano_palette_cut import P, UNIT, engine

CERT = [[[0,20],[0,26],[1,25],[3,37]],11913036,[["('w', (2, 22))",7148352],["('w', (2, 26))",922368],["('w', (3, 33))",94081536],["('w', (3, 35))",40007712],["Y1",20991600],["Y3",65856],["('Fano short difference', 2)",283272],["('Fano all pairs → S', 50)",5040],["('no three orthogonal tangent', 50)",34149],["Fano1 endpoint N24",283272],["('minus', (0, 16))",2365182144],["('minus', (0, 18))",579477696],["('minus', (0, 24))",1346887872],["('minus', (1, 21))",48424320],["('minus', (1, 27))",8070720],["('minus', (2, 28))",50614944],["('minus', (2, 30))",4067296992],["Fano→G230",566544],["('w', (4, 44))",20176800]]]

def check_endpoints():
    allowed = {(1,1),(0,2),(3,6),(6,10),(9,14),(4,5),(7,9)}
    values = {i for pair in allowed for i in pair}
    got = set()
    for a,b,c,d in product(values, repeat=4):
        if abs(a+d-b-c) != 1:
            continue
        if all(tuple(sorted(p)) in allowed for p in ((a,b),(c,d),(a,c),(b,d))):
            got.add(tuple(sorted((a,b,c,d))))
    assert got == {(3,6,6,10)}

def main():
    check_endpoints()
    R, _, D, one = engine()
    face, deficit, witness = CERT
    allowed = set(map(tuple, face))
    assert len(allowed) == 4 and allowed <= UNIT and deficit > 0
    rows = {str(k): v for k,v in R.items()}
    for k in UNIT - allowed:
        rows[str(('minus',k))] = [-x for x in D[k]]
    m1,m2,m4 = [R[('Fano pairs',k)] for k in (1,2,4)]
    rows[str(('Fano all pairs → S',50))] = [
        P*s+4*(a+b+d)-49*n+1250*c for s,a,b,d,n,c in zip(R['S'],m1,m2,m4,R['N'],one)
    ]
    rows[str(('no three orthogonal tangent',50))] = [
        16*(a+b+d)-96*n+2500*c for a,b,d,n,c in zip(m1,m2,m4,R['N'],one)
    ]
    rows['Fano1 endpoint N24'] = [P*n-2*a for n,a in zip(R[('w',(0,24))],m1)]
    assert len(witness) == len(dict(witness)) == 19
    assert all(k in rows and a > 0 and len(rows[k]) == len(one) for k,a in witness)
    check = [sum(a*rows[k][i] for k,a in witness) for i in range(len(one))]
    assert check == [-deficit*x for x in one]
    print("Endpoint Fano exclusion: 19 nonnegative rows give", -deficit)

if __name__=='__main__':
    main()
