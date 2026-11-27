#!/usr/bin/env python3
"""Exact witness for d_H(x^3, Aff(F_2^8)) <= 240.

All arithmetic is implemented here, with no dependencies.  The matching lower
bound is Theorem 18(iii) of Nagy (Cryptography and Communications 17, 2025).
"""
MOD = 0x11B  # t^8+t^4+t^3+t+1
ROW_MASKS = [0x41, 0xD6, 0xFE, 0x56, 0x7C, 0x94, 0xF4, 0x84]
LINEARIZED = [0xB8, 0x64, 0x70, 0x7A, 0x41, 0x79, 0x12, 0xFD]
EXPECTED = [
    0x00,0x01,0x03,0x19,0x25,0x79,0x88,0x95,
    0x9E,0xA6,0xB7,0xC3,0xCA,0xD8,0xF3,0xF7,
]

def degree(p):
    return p.bit_length()-1

def poly_mod(a, b):
    while a and degree(a) >= degree(b):
        a ^= b << (degree(a)-degree(b))
    return a

def poly_gcd(a, b):
    while b:
        a, b = b, poly_mod(a, b)
    return a

def poly_mul_mod(a, b, modulus=MOD):
    out = 0
    while b:
        if b & 1:
            out ^= a
        b >>= 1
        a <<= 1
        if a & 0x100:
            a ^= modulus
    return out

def poly_pow(a, e):
    out = 1
    while e:
        if e & 1:
            out = poly_mul_mod(out, a)
        a = poly_mul_mod(a, a)
        e >>= 1
    return out

def cube(x):
    return poly_mul_mod(poly_mul_mod(x, x), x)

def linear_map(x):
    out = 0
    for r, mask in enumerate(ROW_MASKS):
        out |= (((mask & x).bit_count() & 1) << r)
    return out

def linearized_map(x):
    out = 0
    for i, c in enumerate(LINEARIZED):
        out ^= poly_mul_mod(c, poly_pow(x, 1 << i))
    return out

def check_irreducible():
    # Rabin test for the degree-eight binary polynomial MOD.
    x = 0b10
    y = x
    for i in range(1, 5):
        y = poly_mul_mod(y, y)
        assert poly_gcd(y ^ x, MOD) == 1, i
    for _ in range(4):
        y = poly_mul_mod(y, y)
    assert y == x

def check_apn():
    # The Gold map x^3 must have at most two solutions to every derivative
    # equation F(x+a)+F(x)=b, a != 0.
    for a in range(1, 256):
        counts = [0]*256
        for x in range(256):
            counts[cube(x ^ a) ^ cube(x)] += 1
        assert max(counts) == 2

def main():
    check_irreducible()
    check_apn()

    # Verify both descriptions of L and F_2-linearity exhaustively.
    for x in range(256):
        assert linear_map(x) == linearized_map(x)
        for y in range(256):
            assert linear_map(x ^ y) == (linear_map(x) ^ linear_map(y))

    agreeing = [x for x in range(256) if cube(x) == linear_map(x)]
    assert agreeing == EXPECTED
    assert len(agreeing) == 16

    print("PASS")
    print("field modulus: t^8+t^4+t^3+t+1 (0x11B)")
    print("agreement count:", len(agreeing))
    print("agreement set:", " ".join(f"{x:02x}" for x in agreeing))
    print("witness distance:", 256-len(agreeing))

if __name__ == "__main__":
    main()
