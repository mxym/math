"""Rational lower constant and support exclusions for DoubleHighPositiveMassBarrier."""
from fractions import Fraction as F
from itertools import product


def need(test, message):
    if not test:
        raise ArithmeticError(message)


S = tuple(map(F, (".100", ".140")))
P = tuple(map(F, (".455", ".555")))
R = tuple(map(F, (".560", ".680")))
for s,p,r in product(S,P,R):
    u,v = 1-s-p,1-r
    need(s<v<p<r and s<u<p, 'ordered exact prime bands')
    need(u>F(".300") and v>F(".300"), 'rough / squarefree support')
    need(p+r>=F("1.015"), 'subcritical exclusion')
    need(2*(1-r)+s+2*p>=F("1.650"), 'giant-reflected exclusion')
    need(1-s-p<=F(".445") and 1-s-p>=F(".305"), 'q cofactor bounds')
    need(r>F(".535") and p>F(".387"), 'forward and reverse strip exclusion')
    need(r>F(".5105") and u>F(".02102"), 'Ramaré gate exclusion')
    need(p>F(".359") and r>F(".499"), 'raised tag cuts')


def log_lower(t):
    z=(t-1)/(t+1)
    return 2*(z+z**3/3)


J = log_lower(F(7,5))-F(".1408")
bound = J*F(".100")/F(".445")*log_lower(F(11,8))
need(bound>F(".0139")>F(".010"), 'strict normalized obstruction')
print('8 support corners, certified lower bound:', str(bound), float(bound))


def divisors(sf, primes):
    out = [1]
    for ell in primes:
        out += [ell*z for z in out]
    need(max(out) == sf, 'squarefree product')
    return out


gram_cases = 0
for primes in [[],[3],[3,5],[3,5,7]]:
    c=1
    for ell in primes:
        c*=ell
    for r in (17,23):
        for k in (1,13):
            s,N=11,2
            m=r*c
            D=divisors(c,primes)
            a={e:(k*N*pow(s*(c//e),-1,r*e)*(c//e))%m for e in D}
            # For a general unit b, each direct exponent is a[e]*inverse(b)
            # modulo m. Over uniform units this average equals the normalized
            # Ramanujan sum by CRT, giving exact rational tensor tests.
            for e,ee in product(D,D):
                diff=(a[e]-a[ee])%m
                need(diff%r==0,'different common-r phase')
                expected=actual=F(1)
                for ell in primes:
                    if (e%ell==0)!=(ee%ell==0):
                        expected*=-F(1,ell-1)
                    if diff%ell:
                        actual*=-F(1,ell-1)
                need(actual==expected,'CRT allocation Gram')
                need(a[e]%r!=0,'nonvanishing r phase for centering')
                for ell in primes:
                    need((a[e]%ell!=0)==(e%ell==0),'allocation-model mean')
                gram_cases+=1
print('exact allocation Gram and model centering cases:',gram_cases)
