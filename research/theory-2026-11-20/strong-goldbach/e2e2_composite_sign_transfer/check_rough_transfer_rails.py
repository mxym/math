"""Exact rational rail and local-density checks; runs under python -O."""
from fractions import Fraction as F


def require(test, label):
    if not test:
        raise RuntimeError(label)


def bank_cap(k):
    j = k - 1
    d = F(".02") / (4 * k * k + 4 * k - 1)
    left = sum(2 * i + 2 for i in range(1, k + 1))
    right = sum(2 * i + 2 for i in range(k + 1, 2 * k + 1))
    require(left == k * (k + 3) and right == k * (3 * k + 3), "bank sums")
    require((j + right) * d < F(".016"), "single-leg cap")
    require((j + left + right) * d == F(".020") + F(".060") * k / (4*k*k+4*k-1),
            "combined-bank expression")
    if k >= 15:
        require(F(".975") + (j + left + right) * d + F(".001") + F(".002")
                < F(".999"), "combined CRT floor cap")


for k in range(4, 500):
    bank_cap(k)

require(F(".4875") + F(".016") + F(".001") + F(".002") == F(".5065"),
        "mixed all-small-part modulus")
require(F(".4875") + F(".002") == F(".4895"), "nested-gate modulus")

# The Euler factor at p|m,p∤N must use 1/p at the added sieve prime,
# including when the modulus already contains a higher power p**e.
for p in (3, 5, 7, 11, 17, 101):
    for e in range(1, 6):
        phi = p ** (e - 1) * (p - 1)
        mixed = (1 - F(1, p)) / ((1 - F(1, p - 1)) * phi)
        pure = F(p - 1, (p - 2) * p ** e)
        require(mixed == pure, "power-sensitive conditional local factor")

print("moving determinant support and conditional p-adic factors verified")
