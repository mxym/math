#!/usr/bin/env python3
"""Exact local and numerical checks for Proof.md; no analytic claims by replay."""
from fractions import Fraction
from math import gcd


def test(condition, message):
    if not condition:
        raise SystemExit(message)


def main():
    qcases = rcases = 0
    for p in (2, 3, 5, 7, 11, 13):
        for n in range(p):
            if p == 2 and n:
                continue
            for v in range(4):
                if n == 0 and v:
                    continue
                mod = p ** (v + 1)
                base = p**v
                lifts = [x for x in range(mod) if gcd(x, p) == 1 and (x-n) % base == 0]
                favorable = [x for x in lifts if (x-n) % mod == 0]
                expected = (Fraction(0) if n == 0 else
                            Fraction(1, p) if v else Fraction(1, p-1))
                test(Fraction(len(favorable), len(lifts)) == expected,
                     f"quotient-local mismatch: {p,n,v}")
                qcases += 1
            for r in range(1, p):
                survivors = [m for m in range(p) if m and (r*m-n) % p]
                correction = Fraction(1) if n == 0 else 1-Fraction(1,p-1)
                test(Fraction(len(survivors), p) == (1-Fraction(1,p))*correction,
                     f"two-bank CRT mismatch: {p,n,r}")
                rcases += 1

    low, theta, strip, eps = map(Fraction, (".498", ".60", ".23", ".001"))
    test(1+strip+strip*strip/2 > (1-low)/(1-theta), "log upper")
    test(low*(1+eps) + 2*(1+eps)*strip/Fraction(".996") < Fraction(".962"),
         "strict giant mass")
    test(low + Fraction(".001") < Fraction(".5"), "source BV")
    test(low > (1-low)/2, "outer modulus outside the raw integer sieve")
    test(Fraction(".002") + Fraction(".996") < 1, "power-saving integer count")
    test(Fraction(".40") + Fraction(".010") + Fraction(".08") < Fraction(".5"),
         "fork BV")
    test(Fraction(".010") < Fraction(".020") and
         Fraction(".08")/Fraction(".020") == 4, "tag bank and lower linear sieve")
    test(Fraction(".020")*50 == 1, "exact residual rank cap")
    print(f"PASS {qcases} quotient-local cases, {rcases} two-bank residue cases, exact level and gap checks")


if __name__ == "__main__":
    main()
