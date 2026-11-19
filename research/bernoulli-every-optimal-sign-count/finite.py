"""Exhaustive finite part of the sign-count realizability proof; exact integers."""
from math import comb, gcd


def observed(r, s, n):
    """Scale by s**n. P[j] = mass at j-(n-ell) for ell plus signs."""
    q = s-r
    P = [comb(n, j)*r**(n-j)*q**j for j in range(n+1)]
    best, winners = 0, []
    norm = s**n
    for ell in range(n+1):
        if min(P) <= 0 or sum(P) != norm:
            raise ArithmeticError("not a probability polynomial")
        if 2*ell >= n:
            h = max(P)
            if h > best:
                winners.clear()
                best = h
            if h == best:
                winners.extend((2*ell-n, j-(n-ell)) for j, mass in enumerate(P) if mass == h)
        if ell == n:
            break
        # Exact multiplication by (q + r*z)/(r + q*z).
        prev, new = 0, []
        for j in range(n):
            val, rem = divmod(P[j] - q*prev, r)
            if rem:
                raise ArithmeticError("polynomial division failed")
            new.append(q*val + r*prev)
            prev = val
        if P[-1] != q*prev:
            raise ArithmeticError("leading term did not divide")
        P = new+[r*prev]
    return winners


def main():
    tests=0
    for n in range(3,150,2):
        for T in range(3,n+1,2):
            # p=(1-(1-1/n)/T)/2. Exact peak has original sum x=(T-1)/2.
            r,s=n*T-n+1,2*n*T
            g=gcd(r,s);r//=g;s//=g
            ans=observed(r,s,n)
            if ans != [(T,(T-1)//2)]:
                raise ArithmeticError((n,T,r,s,ans))
            tests+=1
        if n%20==9 or n==149:
            print(f"through n={n}: {tests} exact full-law comparisons",flush=True)
    print("PASS: all required odd lengths below 150 and all imbalances T>=3.")
if __name__ == "__main__":
    main()
