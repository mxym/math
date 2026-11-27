#!/usr/bin/env python3
"""Dependency-free ML-KEM NTT algebra certificate.

Checks public mathematical and conformance identities from FIPS 203.  It is
not a cryptanalytic or vulnerability-testing program.
"""
from random import Random

Q, N, ZETA = 3329, 256, 17
R = (1 << 16) % Q

# FIPS 203 Appendix A: zeta**BitRev7(i), i=0,...,127.
FIPS_ZETAS = [
  1,1729,2580,3289,2642,630,1897,848,1062,1919,193,797,2786,3260,569,1746,
  296,2447,1339,1476,3046,56,2240,1333,1426,2094,535,2882,2393,2879,1974,821,
  289,331,3253,1756,1197,2304,2277,2055,650,1977,2513,632,2865,33,1320,1915,
  2319,1435,807,452,1438,2868,1534,2402,2647,2617,1481,648,2474,3110,1227,910,
  17,2761,583,2649,1637,723,2288,1100,1409,2662,3281,233,756,2156,3015,3050,
  1703,1651,2789,1789,1847,952,1461,2687,939,2308,2437,2388,733,2337,268,641,
  1584,2298,2037,3220,375,2549,2090,1645,1063,319,2773,757,2099,561,2466,2594,
  2804,1092,403,1026,1143,2150,2775,886,1722,1212,1874,1029,2110,2935,885,2154,
]

# pq-crystals/kyber ref/ntt.c at commit 3edd5af: centered Montgomery form.
PQCRYSTALS_MONT_ZETAS = [
  -1044,-758,-359,-1517,1493,1422,287,202,-171,622,1577,182,962,-1202,-1474,1468,
  573,-1325,264,383,-829,1458,-1602,-130,-681,1017,732,608,-1542,411,-205,-1571,
  1223,652,-552,1015,-1293,1491,-282,-1544,516,-8,-320,-666,-1618,-1162,126,1469,
  -853,-90,-271,830,107,-1421,-247,-951,-398,961,-1508,-725,448,-1065,677,-1275,
  -1103,430,555,843,-1251,871,1550,105,422,587,177,-235,-291,-460,1574,1653,
  -246,778,1159,-147,-777,1483,-602,1119,-1590,644,-872,349,418,329,-156,-75,
  817,1097,603,610,1322,-1285,-1465,384,-1215,-136,1218,-1335,-874,220,-1187,-1659,
  -1185,-1530,-1278,794,-1510,-854,-870,478,-108,-308,996,991,958,-1460,1522,1628,
]

def bitrev7(i):
    assert 0 <= i < 128
    return int(f"{i:07b}"[::-1], 2)

def centered(x):
    x %= Q
    return x - Q if x > Q // 2 else x

def poly_mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] = (out[i+j] + x*y) % Q
    return out

def ntt(f):
    """FIPS 203 Algorithm 9."""
    out = [x % Q for x in f]
    i, length = 1, 128
    while length >= 2:
        for start in range(0, N, 2*length):
            zeta = FIPS_ZETAS[i]
            i += 1
            for j in range(start, start+length):
                t = zeta*out[j+length] % Q
                out[j+length] = (out[j]-t) % Q
                out[j] = (out[j]+t) % Q
        length //= 2
    assert i == 128
    return out

def inv_ntt(fhat):
    """FIPS 203 Algorithm 10."""
    out = [x % Q for x in fhat]
    i, length = 127, 2
    while length <= 128:
        for start in range(0, N, 2*length):
            zeta = FIPS_ZETAS[i]
            i -= 1
            for j in range(start, start+length):
                t = out[j]
                out[j] = (t+out[j+length]) % Q
                out[j+length] = zeta*(out[j+length]-t) % Q
        length *= 2
    assert i == 0
    return [x*3303 % Q for x in out]  # 3303 = 128^(-1) mod q.

def multiply_ntts(a, b):
    """FIPS 203 Algorithms 11 and 12."""
    out = [0] * N
    for i in range(128):
        gamma = pow(ZETA, 2*bitrev7(i)+1, Q)
        a0, a1, b0, b1 = a[2*i], a[2*i+1], b[2*i], b[2*i+1]
        out[2*i] = (a0*b0 + gamma*a1*b1) % Q
        out[2*i+1] = (a0*b1 + a1*b0) % Q
    return out

def negacyclic_mul(a, b):
    out = [0] * N
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            k = i+j
            out[k % N] += x*y if k < N else -x*y
    return [x % Q for x in out]

def main():
    # Field/order facts.
    assert all(Q % p for p in range(2, int(Q**0.5)+1))
    assert Q-1 == (2**8)*13
    assert pow(ZETA, 128, Q) == Q-1 and pow(ZETA, 256, Q) == 1
    assert (Q-1) % 512 != 0

    br = [bitrev7(i) for i in range(128)]
    assert sorted(br) == list(range(128))
    assert [pow(ZETA, e, Q) for e in br] == FIPS_ZETAS

    # The 128 constants are distinct nonsquares, so the quadratics are
    # pairwise coprime and irreducible over F_q.
    gammas = [pow(ZETA, 2*e+1, Q) for e in br]
    assert len(set(gammas)) == 128
    assert all(pow(g, (Q-1)//2, Q) == Q-1 for g in gammas)

    # Exact factorization of X^256+1.
    product = [1]
    for gamma in gammas:
        product = poly_mul(product, [(-gamma) % Q, 0, 1])
    target = [0] * (N+1)
    target[0] = target[N] = 1
    assert product == target

    # Public reference table is exactly the FIPS table in R=2^16
    # Montgomery form, centered to [-q/2,q/2].
    assert PQCRYSTALS_MONT_ZETAS == [centered(R*z) for z in FIPS_ZETAS]

    # Exact 256-column proof of Algorithm 9 = direct CRT residue map, and
    # Algorithm 10 is its inverse.  Linearity makes this exhaustive.
    for k in range(N):
        basis = [0] * N
        basis[k] = 1
        got = ntt(basis)
        for i, gamma in enumerate(gammas):
            want = ((pow(gamma, k//2, Q), 0) if k % 2 == 0
                    else (0, pow(gamma, (k-1)//2, Q)))
            assert (got[2*i], got[2*i+1]) == want
        assert inv_ntt(got) == basis

    # Independent end-to-end multiplication checks.
    rng = Random(203)
    for _ in range(8):
        a = [rng.randrange(Q) for _ in range(N)]
        b = [rng.randrange(Q) for _ in range(N)]
        assert inv_ntt(ntt(a)) == a
        assert inv_ntt(ntt(b)) == b
        assert inv_ntt(multiply_ntts(ntt(a), ntt(b))) == negacyclic_mul(a, b)

    print("PASS: order/factorization/CRT/tables/NTT/inverse/product")

if __name__ == "__main__":
    main()
