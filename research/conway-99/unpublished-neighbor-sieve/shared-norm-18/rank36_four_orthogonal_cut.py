"""Check the fourth rank-36 palette exclusion by an exact 19-row witness."""
from rank36_four_fano_palette_cut import P, UNIT, engine

CERT = [[[0,20],[0,26],[2,28],[2,30]],170270270,[["('w', (0, 22))",374507830],["('w', (2, 22))",136151365],["('w', (2, 26))",367718577],["('w', (3, 35))",400320923],["('w', (3, 37))",6789253],["('w', (4, 44))",6789253],["S",49854711],["Y1",583215591],["Y3",271656],["N16lift",122572859],["('Fano short difference', 2)",71854],["('Fano short difference', 4)",71854],["Fano→U125 or G121",143708],["('Fano all pairs → S', 400)",35927],["('minus', (0, 16))",15407739492],["('minus', (0, 18))",1318352112],["('minus', (0, 24))",357124556],["('minus', (1, 21))",652098563],["('minus', (1, 25))",3056327619]]]

def main():
    R, _, D, one = engine()
    face, deficit, witness = CERT
    allowed = set(map(tuple, face))
    assert len(allowed) == 4 and allowed <= UNIT and deficit > 0
    rows = {str(k): v for k,v in R.items()}
    for k in UNIT - allowed:
        rows[str(('minus',k))] = [-x for x in D[k]]
    rows[str(('Fano all pairs → S',400))] = [
        P*s + 4*(m1+m2+m4) - 399*n + 80000*c
        for s,m1,m2,m4,n,c in zip(R['S'],R[('Fano pairs',1)],
                                   R[('Fano pairs',2)],R[('Fano pairs',4)],
                                   R['N'],one)
    ]
    assert len(witness) == len(dict(witness)) == 19
    assert all(k in rows and a > 0 and len(rows[k]) == len(one) for k,a in witness)
    result = [sum(a*rows[k][i] for k,a in witness) for i in range(len(one))]
    assert result == [-deficit*x for x in one]
    print("Orthogonal Fano exclusion: 19 nonnegative rows give", -deficit)

if __name__=='__main__':
    main()
