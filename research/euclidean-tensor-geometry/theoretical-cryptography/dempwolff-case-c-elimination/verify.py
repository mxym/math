"""Exhaust both constant derivatives along the top input bit, without external data."""
def check(m):
    size = 1 << m
    half = size // 2
    mask = (1 << half) - 1
    amp = 1 << ((m + 1) // 2)
    chars = [sum(((w & x).bit_count() & 1) << x for x in range(size))
             for w in range(size)]
    for c in (0, 1):
        count = balanced = 0
        target = set(range(c * half, (c + 1) * half))
        for lower in range(mask + 1):
            upper = lower ^ (mask if c else 0)
            truth = lower | (upper << half)
            walsh = [size - 2 * (truth ^ chi).bit_count() for chi in chars]
            support = {i for i, v in enumerate(walsh) if v}
            if not support <= target:
                raise ValueError("constant-derivative support inclusion failed")
            if all(abs(w) in (0, amp) for w in walsh):
                if support != target or ((walsh[0] == 0) != bool(c)):
                    raise ValueError("semibent support equality or balance failed")
                count += 1
                balanced += walsh[0] == 0
        print(f"dimension={m}, derivative={c}, semibent={count}, balanced={balanced}")


if __name__ == "__main__":
    check(3)
    check(5)
